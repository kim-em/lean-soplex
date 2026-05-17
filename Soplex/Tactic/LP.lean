import Lean
import Init.Data.Vector.Lemmas
import Soplex.Basic
import Soplex.Verify.CertStats
import Soplex.Tactic.RatLin.Tactic

open Lean Meta Elab Tactic
open Soplex Soplex.Verify

namespace Soplex.Tactic.LP

register_option soplex.lp.certificateStats : Bool := {
  defValue := false
  descr := "print denominator/dyadic/integer-scaling statistics for the SoPlex multiplier vector consumed by the lp tactic"
}

/-! # Direct certificate backend for the `lp` tactic.

SoPlex is used as an untrusted oracle to find Farkas / dual multipliers.
The proof term is a compact arithmetic certificate over the original
hypotheses and goal: a weighted sum of hypothesis-side `≤ 0` facts plus
a closed `Rat` algebraic identity, discharged by `grobner`. No
`Problem` / `denseMatrix` / `AffCert` data reductions reach the
kernel. -/

/-! ## Small `Rat` helpers and closing lemmas -/

theorem rat_le_of_sub_nonpos {a b : Rat} (h : a - b ≤ 0) : a ≤ b := by
  have hAdd := (Rat.add_le_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_le {a b : Rat} (h : a ≤ b) : a - b ≤ 0 := by
  have hAdd := (Rat.add_le_add_right (a := a) (b := b) (c := -b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_eq {a b : Rat} (h : a = b) : a - b ≤ 0 := by
  subst h
  simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel]

theorem rat_lt_of_sub_neg {a b : Rat} (h : a - b < 0) : a < b := by
  have hAdd := (Rat.add_lt_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_le_of_nonneg_sub {a b : Rat} (h : 0 ≤ b - a) : a ≤ b :=
  Soplex.Verify.RatAux.sub_nonneg.mp h

theorem rat_lt_of_pos_sub {a b : Rat} (h : 0 < b - a) : a < b := by
  have hle : a ≤ b := rat_le_of_nonneg_sub (Rat.le_of_lt h)
  exact Rat.lt_of_le_of_ne hle (by
    intro hEq
    subst hEq
    simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel] at h)

/-- A nonnegative scalar of a nonpositive value is nonpositive. -/
theorem rat_smul_nonpos {a lam : Rat} (ha : a ≤ 0) (hlam : 0 ≤ lam) : lam * a ≤ 0 := by
  have h := Rat.mul_le_mul_of_nonneg_left ha hlam
  simpa [Rat.mul_zero] using h

/-- Sum of two nonpositive `Rat`s is nonpositive. -/
theorem rat_add_nonpos {a b : Rat} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  have h := Soplex.Verify.RatAux.add_le_add ha hb
  simpa [Rat.zero_add] using h

/-- Final closer for non-strict goals.

Given a nonpositive sum `s ≤ 0`, a nonnegative residual `c`, and the
algebraic identity `(rhs - lhs) + s = c`, we get `lhs ≤ rhs`. The
identity is a pure `Rat` polynomial fact in the user expressions and is
discharged by `grobner` at tactic time. -/
theorem direct_le_close {lhs rhs s c : Rat}
    (hSum : s ≤ 0) (hC : 0 ≤ c) (hIdent : rhs - lhs + s = c) :
    lhs ≤ rhs := by
  apply rat_le_of_nonneg_sub
  -- (rhs - lhs) = c - s ; both 0 ≤ c and -s ≥ 0
  have hStep : c - s = rhs - lhs := by
    have h := hIdent
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
           Rat.add_neg_cancel, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add, Rat.neg_neg]
  rw [← hStep]
  exact Soplex.Verify.RatAux.sub_nonneg.mpr (Rat.le_trans hSum hC)

/-- Final closer for strict goals: same shape as `direct_le_close`, but the
residual must be strictly positive. -/
theorem direct_lt_close {lhs rhs s c : Rat}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : rhs - lhs + s = c) :
    lhs < rhs := by
  apply rat_lt_of_pos_sub
  have hStep : c - s = rhs - lhs := by
    have h := hIdent
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
           Rat.add_neg_cancel, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add, Rat.neg_neg]
  rw [← hStep]
  -- 0 < c - s, with hC : 0 < c, hSum : s ≤ 0, so s < c (via le_lt transitivity).
  have hsc : s < c := Rat.lt_of_le_of_ne (Rat.le_trans hSum (Rat.le_of_lt hC)) (by
    intro hEq
    subst hEq
    exact (Rat.not_le.mpr hC) hSum)
  exact (Rat.lt_iff_sub_pos s c).mp hsc

/-- Final closer for infeasibility: `s ≤ 0` and `s = c` with `0 < c` is
`False`. Used when SoPlex reports an infeasible LP and supplies a Farkas
certificate. -/
theorem direct_infeasible_close {s c : Rat}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : s = c) : False := by
  rw [hIdent] at hSum
  exact Rat.not_le.mpr hC hSum

/-! ## Parsing affine `Rat` expressions and `≤`/`=` hypotheses.

The parsing layer is unchanged in spirit from the previous verifier
backend, but it no longer produces `AffCert` / `Problem`-shaped
artefacts. Each parsed row carries:

* `term : Expr` — the source-side Lean expression `lhsᵢ - rhsᵢ`;
* `proof : Expr` of type `term ≤ 0`;
* `linexpr : LinExpr` — numerical coefficients on the parsed variables,
  used to build the LP problem fed to SoPlex and to compute the
  numerical residual after the dual comes back.
-/

inductive Rel where
  | le
  | lt
  | eq
  deriving Repr, DecidableEq

structure LinExpr where
  const : Rat := 0
  coeffs : Array (FVarId × Rat) := #[]
  deriving Inhabited

structure Row where
  term : Expr
  expr : LinExpr
  proof : MetaM Expr

structure ParseState where
  vars : Array FVarId := #[]
  deriving Inhabited

abbrev ParseM := StateT ParseState MetaM

private def ratType : Expr := mkConst ``Rat

private def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

private def addCoeff (coeffs : Array (FVarId × Rat)) (v : FVarId) (c : Rat) :
    Array (FVarId × Rat) := Id.run do
  if c = 0 then
    return coeffs
  let mut out := #[]
  let mut found := false
  for (v', c') in coeffs do
    if v' == v then
      found := true
      let c'' := c' + c
      if c'' != 0 then
        out := out.push (v', c'')
    else
      out := out.push (v', c')
  if found then out else out.push (v, c)

private def LinExpr.add (a b : LinExpr) : LinExpr :=
  { const := a.const + b.const
    coeffs := b.coeffs.foldl (fun acc (v, c) => addCoeff acc v c) a.coeffs }

private def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

private def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

private def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

/-- Convert a `LinExpr` to a dense coefficient `Array Rat` over a fixed
variable ordering. Unknown variables are skipped (treated as zero
coefficient, which only happens in degenerate parses). -/
private def LinExpr.toDense (e : LinExpr) (vars : Array FVarId) :
    Array Rat := Id.run do
  let mut out := Array.replicate vars.size (0 : Rat)
  for (v, c) in e.coeffs do
    for h : i in [0:vars.size] do
      if vars[i] == v then
        out := out.set! i (out[i]! + c)
  return out

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/-- Recognise an expression as a reducibly-closed `Rat` scalar (matches
  the previous backend's scalar-recogniser policy exactly). -/
private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  let e ← withReducible <| whnfR e
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => parseScalar? value
      | none => return none
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``OfNat.ofNat _ =>
          if args.size == 3 then
            match args[1]! with
            | .lit (.natVal n) => return some (OfNat.ofNat n)
            | _ => return none
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? args[2]!).map (fun x => -x)
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a + b)
            | _, _ => return none
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some _, some 0 => return none
            | some a, some b => return some (a / b)
            | _, _ => return none
      | _ => return none
      return none

private partial def parseExpr (e : Expr) : ParseM LinExpr := do
  if let some v ← parseScalar? e then
    return { const := v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return { const := v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return { const := v }
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp: expected a Rat expression, found{indentExpr e}"
      addVar id
      return { coeffs := #[(id, 1)] }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).add (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).sub (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseExpr args[2]!).neg
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? e then
            return { const := v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              return (← parseExpr rhs).smul c
            if let some c ← parseScalar? rhs then
              return (← parseExpr lhs).smul c
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | .const ``HDiv.hDiv _ =>
          throwError "lp: division is outside the supported affine Rat grammar"
      | _ => pure ()
      throwError "lp: unsupported Rat expression{indentExpr e}"

private def isRatExpr (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) ratType

private def parseAtomicRat (rel : Rel) (lhs rhs : Expr) :
    ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  unless (← isRatExpr lhs) && (← isRatExpr rhs) do
    return none
  return some (rel, lhs, rhs, ← parseExpr lhs, ← parseExpr rhs)

private def parseAtomic? (type : Expr) : ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  let e := type
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``LE.le _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[2]! args[3]!
  | .const ``GE.ge _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[3]! args[2]!
  | .const ``LT.lt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[2]! args[3]!
  | .const ``GT.gt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[3]! args[2]!
  | .const ``Eq _ =>
      if args.size == 3 then
        return ← parseAtomicRat .eq args[1]! args[2]!
  | _ => pure ()
  return none

private def isAnd? (type : Expr) : Option (Expr × Expr) :=
  let fn := type.getAppFn
  let args := type.getAppArgs
  match fn with
  | .const ``And _ =>
      if args.size == 2 then some (args[0]!, args[1]!) else none
  | _ => none

private partial def collectHypProof (origin : Name) (proof : Expr) :
    ParseM (Array Row) := do
  let type ← inferType proof
  if (isAnd? type).isSome then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    return (← collectHypProof origin left) ++ (← collectHypProof origin right)
  match ← parseAtomic? type with
  | none => return #[]
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict hypothesis `{origin}` is not supported in Stage 1"
  | some (.le, lhsExpr, rhsExpr, lhs, rhs) =>
      let row := lhs.sub rhs
      let term ← mkAppM ``HSub.hSub #[lhsExpr, rhsExpr]
      return #[{ term := term, expr := row, proof := mkAppM ``rat_sub_nonpos_of_le #[proof] }]
  | some (.eq, lhsExpr, rhsExpr, lhs, rhs) =>
      let d := lhs.sub rhs
      let term₁ ← mkAppM ``HSub.hSub #[lhsExpr, rhsExpr]
      let term₂ ← mkAppM ``HSub.hSub #[rhsExpr, lhsExpr]
      return #[
        { term := term₁, expr := d, proof := mkAppM ``rat_sub_nonpos_of_eq #[proof] },
        { term := term₂, expr := d.neg, proof := do mkAppM ``rat_sub_nonpos_of_eq #[← mkEqSymm proof] }]

private def collectHyps : ParseM (Array Row) := do
  let mut rows := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        rows := rows ++ (← collectHypProof decl.userName decl.toExpr)
  return rows

/-! ## Building the LP problem fed to SoPlex.

The LP is `min (rhs - lhs)` over free `Rat` variables, with constraints
`eᵢ ≤ 0` for each parsed `≤`-row (`=`-rows expand to two `≤`-rows in
`collectHypProof`). SoPlex is only used as an oracle; the returned
dual multipliers are re-checked numerically at tactic time before any
proof term is built. -/

private def mkEntries (rowDense : Array (Array Rat)) (n : Nat) :
    Array (Fin rowDense.size × Fin n × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rowDense.size] do
    if hi : i < rowDense.size then
      let coeffs := rowDense[i]
      for j in [0:n] do
        if hj : j < n then
          let c := coeffs[j]!
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

private def buildProblem (rowDense : Array (Array Rat)) (rowConsts : Array Rat)
    (objCoeffs : Array Rat) (objConst : Rat) (n : Nat)
    (h : rowDense.size = rowConsts.size := by rfl) :
    Problem rowDense.size n :=
  let rowBounds := rowConsts.map fun c => ((none : Option Rat), some (-c))
  { c := Vector.ofFn fun j => objCoeffs[j.val]!
    objOffset := objConst
    a := mkEntries rowDense n
    rowBounds := ⟨rowBounds, by simp [rowBounds, h]⟩
    colBounds := Vector.replicate n (none, none) }

/-! ## Tactic-side proof assembly. -/

private def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

private def traceMultiplierStats (label : String) (mults : Array Rat) : TacticM Unit := do
  if (← getOptions).getBool `soplex.lp.certificateStats false then
    logInfo (Soplex.Verify.RatProfile.summary label (Soplex.Verify.profileRatArray mults))

/-- Build a `Rat` `HMul.hMul a b` Expr. -/
private def mkRatMul (a b : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[a, b]

/-- Build a `Rat` `HAdd.hAdd a b` Expr. -/
private def mkRatAdd (a b : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

/-- Build a `Rat` `HSub.hSub a b` Expr. -/
private def mkRatSub (a b : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[a, b]

/-- Build a `Rat` literal Expr.  We emit a `Q.toRat`-normalised form so
that the RatLin discharger's `Lin.eval` reduces to the same kernel term
on both sides of the identity.  Closed `Rat.div`-form literals (which is
what `toExpr Rat` produces for non-integer rationals) would not be
definitionally equal to our `Rat.normalize`-form `eval` output. -/
private def mkRatLit (r : Rat) : MetaM Expr := do
  let numE : Expr := match r.num with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)
  let denE : Expr := mkNatLit r.den
  let denNeType ← mkAppM ``Ne #[denE, mkNatLit 0]
  let denNeProof ← mkDecideProof denNeType
  let qExpr := mkApp3 (mkConst ``Soplex.Tactic.RatLin.Q.mk) numE denE denNeProof
  return mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qExpr

/--
Build a Lean expression representing the weighted sum
`λ_{i₀} * term_{i₀} + λ_{i₁} * term_{i₁} + ... + λ_{iₖ₋₁} * term_{iₖ₋₁}`
together with a proof that this sum is `≤ 0`. `entries` lists only the
nonzero multipliers, in iteration order.

Returns `(sumExpr, sumProof)` where:
* `sumExpr : Rat` is the literal sum expression;
* `sumProof : sumExpr ≤ 0`.

The empty list yields `sumExpr = (0 : Rat)` and the trivial proof
`Rat.le_refl : (0 : Rat) ≤ 0`. -/
private def buildWeightedSumAndProof
    (entries : Array (Rat × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  if entries.size = 0 then
    let zero ← mkRatLit 0
    let proof ← mkAppOptM ``Rat.le_refl #[some zero]
    return (zero, proof)
  -- Right-fold so the sum nests on the right and the proof is built
  -- bottom-up. We accumulate (sumExpr, sumProof) as we go.
  let n := entries.size
  let last := n - 1
  let (lamₖ, termₖ, hRowₖ) := entries[last]!
  let lamₖExpr ← mkRatLit lamₖ
  let hLamₖ ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), lamₖExpr])
  let sumₖ ← mkRatMul lamₖExpr termₖ
  let proofₖ ← mkAppM ``rat_smul_nonpos #[hRowₖ, hLamₖ]
  let mut sumExpr := sumₖ
  let mut sumProof := proofₖ
  for i in [0:last] do
    let idx := last - 1 - i
    let (lam, term, hRow) := entries[idx]!
    let lamExpr ← mkRatLit lam
    let hLam ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), lamExpr])
    let head ← mkRatMul lamExpr term
    let headProof ← mkAppM ``rat_smul_nonpos #[hRow, hLam]
    let newSum ← mkRatAdd head sumExpr
    let newProof ← mkAppM ``rat_add_nonpos #[headProof, sumProof]
    sumExpr := newSum
    sumProof := newProof
  return (sumExpr, sumProof)

/-- Look up a variable's coefficient inside a `LinExpr`. -/
private def LinExpr.coeffOf (e : LinExpr) (v : FVarId) : Rat := Id.run do
  for (v', c) in e.coeffs do
    if v' == v then return c
  return 0

/-- Compute the numerical residual `c = (rhs - lhs) + Σ λᵢ * eᵢ`
expressed as a `LinExpr`. The caller verifies that the variable
coefficients all vanish; what remains is the closed `Rat` constant
that gets fed to `decide` for the sign check and to `grobner` for the
algebraic identity proof. -/
private def computeResidual (objLin : LinExpr) (rowLins : Array LinExpr)
    (mults : Array Rat) : LinExpr := Id.run do
  let mut acc : LinExpr := objLin
  for h : i in [0:rowLins.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      acc := acc.add (LinExpr.smul lam rowLins[i])
  return acc

private def isLinExprClosed (e : LinExpr) : Bool :=
  e.coeffs.all (fun (_, c) => c == 0)

/-! ## Discharger for the closed `Rat` algebraic identity.

The identity has the form `(rhs - lhs) + Σ λᵢ * tᵢ = c` (or the Farkas
shape `Σ λᵢ * tᵢ = c` for infeasible certificates).  Each `tᵢ` is a
user-side `Rat` expression, each `λᵢ` and `c` is a closed `Rat` literal,
and the identity is a pure polynomial fact in user variables.

We discharge it with a purpose-built reflective normaliser
`Soplex.Tactic.RatLin.proveLinearIdentity`, whose work is bounded by
the nonzero count of the identity (`O(nnz)`) and which produces a
predictable proof term independent of the variable count.  See
`Soplex/Tactic/RatLin/{Q,AST,NF,Tactic}.lean` for the implementation
and soundness theorem. -/

private def proveAlgebraicIdentity (target : Expr) : TacticM Expr :=
  Soplex.Tactic.RatLin.proveLinearIdentity target

/-! ## Per-goal driver.

Given a parsed atomic `Rat` goal `lhs op rhs` and the collected `≤`/`=`
hypotheses-as-rows, build the LP, run SoPlex, and assemble the direct
certificate proof. -/

/-- Assemble the optimal-branch certificate proof from the numerical
multipliers and the parsed rows. Shared between the SoPlex-driven path
and the trivial closed-goal short-circuit (where multipliers are all
zero and `c = objLin.const`). -/
private def assembleLeProof (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (lhs rhs : Expr) : TacticM Expr := do
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
      let proof ← row.proof
      entries := entries.push (lam, row.term, proof)
  let (sumExpr, sumProof) ← buildWeightedSumAndProof entries
  let cExpr ← mkRatLit c
  let lhsId ← mkRatAdd rhsMinusLhs sumExpr
  let identType ← mkEq lhsId cExpr
  let identProof ← proveAlgebraicIdentity identType
  -- Build the final closer by explicit-argument application instead of
  -- `mkAppM`. The four implicits (`lhs`, `rhs`, `s`, `c`) are already in
  -- hand here, so making `mkAppM` rediscover them by `isDefEq` over the
  -- deeply nested `sumProof`/`identProof` types blows the elaborator's
  -- `maxRecDepth` on large LPs. See issue #71.
  if strict then
    let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
    return mkAppN (mkConst ``direct_lt_close)
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), cExpr])
    return mkAppN (mkConst ``direct_le_close)
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]

private def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) : TacticM Expr := do
  -- Numerical row data.
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  -- Objective: `rhs - lhs` as a `LinExpr`.
  let (objLin, _) ←
    (do
      let lhsLin ← parseExpr lhs
      let rhsLin ← parseExpr rhs
      pure (rhsLin.sub lhsLin)).run { vars := vars }
  -- Short-circuit when the goal is purely a closed `Rat` comparison: no
  -- rows are needed, no SoPlex call is needed, and the empty-sum direct
  -- certificate is enough.
  if vars.size = 0 || isLinExprClosed objLin then
    let mults := Array.replicate rows.size (0 : Rat)
    return ← assembleLeProof rows strict objLin mults lhs rhs
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
  traceMultiplierStats "lp.rowUpper" mults
  -- Verify multipliers are nonneg.
  unless mults.all (fun lam => 0 ≤ lam) do
    throwError "lp: SoPlex returned a negative upper-bound multiplier; refusing to build a proof"
  -- Branch on the SoPlex outcome.
  let rowLins := rows.map (·.expr)
  match sol.status with
  | .optimal =>
      assembleLeProof rows strict objLin mults lhs rhs
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
          let proof ← row.proof
          entries := entries.push (lam, row.term, proof)
      let (sumExpr, sumProof) ← buildWeightedSumAndProof entries
      let cExpr ← mkRatLit c
      let identType ← mkEq sumExpr cExpr
      let identProof ← proveAlgebraicIdentity identType
      let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
      -- Explicit-argument construction; see comment in `assembleLeProof`.
      let hFalse := mkAppN (mkConst ``direct_infeasible_close)
        #[sumExpr, cExpr, sumProof, hC, identProof]
      let goalType ←
        if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
      mkAppOptM ``False.elim #[some goalType, some hFalse]
  | s =>
      throwError "lp: solver outcome was unchecked: {repr s}"

private def solveAtomic (g : MVarId) : TacticM Unit := do
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

private partial def solveGoal (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  g.withContext do
    let target ← whnfR (← g.getType)
    if let some (left, right) := isAnd? target then
      let leftProof ← mkFreshExprMVar left
      let rightProof ← mkFreshExprMVar right
      let proof ← mkAppM ``And.intro #[leftProof, rightProof]
      g.assign proof
      solveGoal leftProof.mvarId!
      solveGoal rightProof.mvarId!
    else
      solveAtomic g

elab "lp" : tactic => do
  let goals ← getGoals
  match goals with
  | [] => throwError "lp: no goals"
  | g :: rest =>
      setGoals [g]
      solveGoal g
      let newGoals ← getGoals
      setGoals (newGoals ++ rest)

end Soplex.Tactic.LP
