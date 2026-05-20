import Soplex.Tactic.LP.Atomic
import Soplex.Tactic.LP.Exists

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

/-! ## Forward-direction `maximize` tactic.

`maximize <expr>` and `maximize h : <expr>` take a linear `Rat` expression
and inject `have h : <expr> ≤ N := <proof>` where `N` is the certified
optimum of `<expr>` over the local non-strict linear hypotheses.

Architecturally this is a *forward-direction surface* on top of the same
sup-LP construction the x-independent inner-`∀` path uses — that path
substitutes a residual row into a witness LP, while `maximize` injects
the bound as a new hypothesis. The proof of `expr ≤ N` is built by
reusing `proveEntailed` with `rhs := mkRatLit N`: `direct_le_close` is
the closing lemma; the Farkas-multiplier weighting against the original
hypothesis terms is the binder/vector mapping; and `normalizeR` is the
surface-form reflection.

Verified-outcome dispatch:
- `.optimal x* d`: recompute `N = exprLin.evalAt vars x*` in Lean (the
  primal is trusted only as a vector of `Rat` literals; SoPlex's reported
  objective value is not used). Then call `proveEntailed` to build a
  proof of `expr ≤ N` against the original hypothesis terms.
- `.infeasible d`: hypotheses are inconsistent. Reuse
  `tryHypsInconsistent` to derive `False` from the dual, then close the
  *surrounding goal* by `False.elim` (the only branch where `maximize`
  touches the goal).
- `.unbounded …`: the sup is `+∞`. Fail with the canonical
  "verified unbounded" message.
- any other status: fail with the canonical "unchecked" message.

Strict-hypothesis rejection is inherited from `collectHyps`: strict
hypotheses throw at parse time before any LP call. -/

def runMaximize (g : MVarId) (hname : Name) (exprE : Expr) :
    TacticM Unit := g.withContext do
  -- Verify the user's expression has type `Rat`. Surfacing this here
  -- gives a cleaner diagnostic than letting `parseExpr` discover the
  -- mismatch deep inside the affine grammar walker.
  let exprE ← instantiateMVars exprE
  let exprTy ← inferType exprE
  unless ← isDefEq exprTy ratType do
    throwError "maximize: expected a `Rat` expression, got{indentExpr exprE}{
      ""}\n  of type{indentExpr exprTy}"
  -- Parse `expr` (registers its `Rat` locals as LP variables) and then
  -- collect the non-strict linear hypotheses from the local context.
  -- Order matters only for the LP column ordering: `expr`'s vars come
  -- first, matching what `solveAtomic` does for goal-then-hyps.
  let ((exprLin, rows), state) ← (do
      let exprLin ← parseExpr exprE
      let hs ← collectHyps
      pure (exprLin, hs)).run {}
  let vars := state.vars
  -- Build the sup LP: `max exprLin subject to (each row.expr ≤ 0)`.
  -- A variable appearing in `exprLin` but in no hypothesis row has a
  -- zero column in every row but a non-zero objective coefficient ⇒ the
  -- LP is unbounded, which surfaces as the "verified unbounded" message
  -- below. This is the "expression mentions a variable absent from
  -- hypotheses" pitfall.
  -- Degenerate LP short-circuit: with no `Rat` locals at all, the
  -- expression is a constant and `N = exprLin.const`. SoPlex would
  -- abort on a 0-variable LP, so we sidestep it — but inconsistency
  -- still has to be probed first, otherwise a goal like `False` under
  -- `_h : (1 : Rat) ≤ 0` would just receive a vacuous `0 ≤ 0` injection
  -- and stay open. The closed-rows-only branch of `tryHypsInconsistent`
  -- handles the probe without SoPlex.
  if vars.size = 0 then
    match ← tryHypsInconsistent rows vars with
    | some hFalse =>
        let goalType ← g.getType
        let proofTerm ← mkAppOptM ``False.elim #[some goalType, some hFalse]
        g.assign proofTerm
        return
    | none => pure ()
    -- Hypotheses are consistent (each closed row says `c ≤ 0` with
    -- `c ≤ 0`); the bound `expr ≤ N` follows from `Rat.le_refl` via
    -- `proveEntailed`'s empty-multiplier branch.
    let N := exprLin.const
    let NE ← mkRatLit N
    let proof ← proveEntailed rows false vars exprE NE
    let propType ← mkAppM ``LE.le #[exprE, NE]
    let g' ← g.assert hname propType proof
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    return
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := exprLin.toDense vars
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs exprLin.const vars.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "maximize: invalid generated problem: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => throwError "maximize: solveExact failed: {repr e}"
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | throwError "maximize: SoPlex reported optimal without a primal certificate"
      -- `pr : Vector Rat n` is typed-by-construction over `n = vars.size`,
      -- so this check should never fire — but `evalAt` uses `xs[i]!`,
      -- and a violated FFI contract would otherwise panic instead of
      -- producing a tactic-level error.
      unless pr.toArray.size = vars.size do
        throwError "maximize: solver primal has {pr.toArray.size} entries, {
          ""}expected {vars.size}; refusing to evaluate the objective"
      -- Recompute `N` on the Lean side: do not trust the solver's
      -- reported objective. `exprLin.evalAt` folds in the constant
      -- offset, so a `maximize 3 * x + 7` optimum is the full
      -- `3 * x* + 7`, not just `3 * x*`.
      let N : Rat := exprLin.evalAt vars pr.toArray
      let NE ← mkRatLit N
      -- Build `proof : exprE ≤ NE` by reusing the atomic-goal
      -- entailment discharger. This re-solves an LP internally — a small redundant
      -- cost in exchange for sharing the entire closing-lemma and
      -- reflection-equality machinery rather than reproving it.
      let proof ← proveEntailed rows false vars exprE NE
      let propType ← mkAppM ``LE.le #[exprE, NE]
      -- Inject as `have hname : prop := proof`. Existing hypotheses
      -- named `hname` are shadowed (matching `have`'s standard
      -- behavior); the user can pass an explicit name to avoid that.
      let g' ← g.assert hname propType proof
      let (_, g'') ← g'.intro1P
      replaceMainGoal [g'']
  | .infeasible =>
      -- Hypotheses imply `False`. Reuse the existential-path inconsistency
      -- probe to extract a `False` proof from the dual, then close the
      -- surrounding goal (any proposition) by `False.elim`. This is the
      -- only branch where `maximize` touches the goal.
      match ← tryHypsInconsistent rows vars with
      | some hFalse =>
          let goalType ← g.getType
          let proofTerm ← mkAppOptM ``False.elim #[some goalType, some hFalse]
          g.assign proofTerm
      | none =>
          throwError "maximize: SoPlex reported infeasible but no `False` {
            ""}certificate could be reconstructed from the dual"
  | .unbounded =>
      -- SoPlex reports unbounded; we do not run `checkUnbounded` here,
      -- so this is the solver's diagnosis, not a kernel-checked
      -- certificate. The tactic fails — no bogus claim enters the
      -- proof — but the message is phrased as the solver report it is.
      throwError "maximize: the LP is unbounded above; no finite {
        ""}upper bound exists for this expression under the collected hypotheses"
  | s =>
      throwError "maximize: solver/certificate unchecked; no Lean proof {
        ""}was produced (status: {repr s})"

/-- `maximize <expr>` injects `have hbound : <expr> ≤ N := <proof>` where
`N` is the certified maximum of `<expr>` over the local linear
hypotheses. `maximize h : <expr>` uses `h` as the hypothesis name. -/
syntax (name := maximizeStx) "maximize" (atomic(ppSpace ident " : "))? ppSpace term : tactic

elab_rules : tactic
  | `(tactic| maximize $[$h :]? $e) => do
      let goals ← getGoals
      match goals with
      | [] => throwError "maximize: no goals"
      | g :: rest =>
          setGoals [g]
          g.withContext do
            let hname : Name := match h with
              | some id => id.getId
              | none    => `hbound
            let exprE ← Elab.Tactic.elabTermEnsuringType e ratType
            runMaximize g hname exprE
          let newGoals ← getGoals
          setGoals (newGoals ++ rest)

end Soplex.Tactic.LP.Internal
