import Soplex.Tactic.LP.Certificate

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

/-! ## Per-goal driver.

Given a parsed atomic `Rat` goal `lhs op rhs` and the collected `≤`/`=`
hypotheses-as-rows, build the LP, run SoPlex, and assemble the direct
certificate proof. -/

/-- Assemble the optimal-branch certificate proof from the numerical
multipliers and the parsed rows. Shared between the SoPlex-driven path
and the trivial closed-goal short-circuit (where multipliers are all
zero and `c = objLin.const`). -/
def assembleLeProof (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (vars : Array FVarId)
    (lhs rhs : Expr) : TacticM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual objLin rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: dual certificate did not algebraically cancel the goal{
      ""} (residual still depends on variables); refusing to build a proof"
  let c := residual.const
  if strict then
    unless decide (0 < c) do
      throwError "lp: goal is not entailed; numerical residual is {c}, not > 0"
  else
    unless decide (0 ≤ c) do
      throwError "lp: goal is not entailed; numerical residual is {c}, not ≥ 0"
  let rhsMinusLhs ← mkRatSub rhs lhs
  let mut entries : Array (Rat × Expr × Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      let row := rows[i]
      let term ← row.term
      let proof ← row.proof
      entries := entries.push (lam, term, proof)
  let (sumExpr, sumProof) ← buildWeightedSumAndProof entries
  let cExpr ← mkRatLit c
  let lhsId ← mkRatAdd rhsMinusLhs sumExpr
  -- Explicit-proof-term discharge of `lhsId = c`.
  let identProof ← proveCertificateIdentity vars lhsId c
  -- Build the final closer by explicit-argument application instead of
  -- `mkAppM`. The four implicits (`lhs`, `rhs`, `s`, `c`) are already in
  -- hand here, so making `mkAppM` rediscover them by `isDefEq` over the
  -- deeply nested `sumProof`/`identProof` types can blow the elaborator's
  -- `maxRecDepth` on large LPs.
  if strict then
    let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
    return mkAppN (mkConst ``direct_lt_close)
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), cExpr])
    return mkAppN (mkConst ``direct_le_close)
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]

def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) : TacticM Expr := do
  -- Objective: `rhs - lhs` as a `LinExpr`.
  let (objLin, _) ←
    (do
      let lhsLin ← parseExpr lhs
      let rhsLin ← parseExpr rhs
      pure (rhsLin.sub lhsLin)).run { vars := vars }
  -- Short-circuit when the goal is purely a closed `Rat` comparison: no
  -- rows are needed, no SoPlex call is needed, and the empty-sum direct
  -- certificate is enough. The wider `isLinExprClosed objLin` case is
  -- only safe when the residual constant has the right sign — otherwise
  -- the rows may be inconsistent and the proper certificate routes
  -- through SoPlex's infeasibility branch (vacuous-guard case from the
  -- x-independent inner-`∀` path).
  let canShortcut : Bool :=
    vars.size = 0 ||
    (isLinExprClosed objLin &&
     (if strict then decide (0 < objLin.const) else decide (0 ≤ objLin.const)))
  if canShortcut then
    let mults := Array.replicate rows.size (0 : Rat)
    return ← assembleLeProof rows strict objLin mults vars lhs rhs
  -- Numerical row data is only needed once we know a solver call is
  -- required; the closed-goal path above proves the goal with the empty
  -- weighted sum.
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := objLin.toDense vars
  let objConst := objLin.const
  -- Build the LP.
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs objConst vars.size hSize
  let opts : Options := { ({} : Options) with sense := .minimize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp: invalid generated problem: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => throwError "lp: solveExact failed: {repr e}"
    | .ok sol => pure sol
  -- Handle the unbounded case up front: there is no dual to consume.
  match sol.status with
  | .unbounded =>
      let baseRepr := sol.certificate.primal |>.map (ratList ·.toArray) |>.getD "?"
      let rayRepr := sol.certificate.ray |>.map (ratList ·.toArray) |>.getD "?"
      throwError "lp: objective is unbounded above; base={baseRepr}, ray={rayRepr}"
  | _ => pure ()
  let some d := sol.certificate.dual
    | throwError "lp: SoPlex returned no dual certificate"
  let mults := d.rowUpper.toArray
  -- Verify multipliers are nonneg.
  unless mults.all (fun lam => 0 ≤ lam) do
    throwError "lp: SoPlex returned a negative upper-bound multiplier; refusing to build a proof"
  -- Branch on the SoPlex outcome.
  let rowLins := rows.map (·.expr)
  match sol.status with
  | .optimal =>
      assembleLeProof rows strict objLin mults vars lhs rhs
  | .infeasible =>
      -- Build a Farkas-style sum and turn the goal into anything via `False.elim`.
      let zeroLin : LinExpr := {}
      let residual := computeResidual zeroLin rowLins mults
      unless isLinExprClosed residual do
        throwError "lp: SoPlex reported infeasible but the Farkas certificate did not{
          ""} algebraically cancel"
      let c := residual.const
      unless decide (0 < c) do
        throwError "lp: SoPlex reported infeasible but Farkas residual {c} is not > 0"
      -- Collect entries.
      let mut entries : Array (Rat × Expr × Expr) := #[]
      for h : i in [0:rows.size] do
        let lam := mults[i]!
        if lam ≠ 0 then
          let row := rows[i]
          let term ← row.term
          let proof ← row.proof
          entries := entries.push (lam, term, proof)
      let (sumExpr, sumProof) ← buildWeightedSumAndProof entries
      let cExpr ← mkRatLit c
      -- Explicit-proof-term discharge of the Farkas identity
      -- `sumExpr = c`, sharing `proveCertificateIdentity` with the
      -- optimal branch.
      let identProof ← proveCertificateIdentity vars sumExpr c
      let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
      -- Explicit-argument construction; see comment in `assembleLeProof`.
      let hFalse := mkAppN (mkConst ``direct_infeasible_close)
        #[sumExpr, cExpr, sumProof, hC, identProof]
      let goalType ←
        if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
      mkAppOptM ``False.elim #[some goalType, some hFalse]
  | s =>
      throwError "lp: solver outcome was unchecked: {repr s}"
def solveAtomic (g : MVarId) : TacticM Unit := do
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let ((parsed?, rows), st) ← (do
      let p ← parseAtomic? target
      let hs ← collectHyps
      pure (p, hs)).run {}
    let some (rel, lhsExpr, rhsExpr, _, _) := parsed?
      | throwError "lp: goal is not an atomic Rat comparison"
    match rel with
    | .le =>
        let proof ← proveEntailed rows false st.vars lhsExpr rhsExpr
        g.assign proof
    | .lt =>
        let proof ← proveEntailed rows true st.vars lhsExpr rhsExpr
        g.assign proof
    | .eq =>
        let h₁ ← proveEntailed rows false st.vars lhsExpr rhsExpr
        let h₂ ← proveEntailed rows false st.vars rhsExpr lhsExpr
        let proof ← mkAppM ``Rat.le_antisymm #[h₁, h₂]
        g.assign proof

end Soplex.Tactic.LP.Internal
