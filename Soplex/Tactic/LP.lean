import Lean
import Init.Data.Vector.Lemmas
import Soplex.Basic
import Soplex.Tactic.RatLin.Q

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic.RatLin (Q)

namespace Soplex.Tactic.LP

/-! # Direct certificate backend for the `lp` tactic.

SoPlex is used as an untrusted oracle to find Farkas / dual multipliers.
The proof term is a compact arithmetic certificate over the original
hypotheses and goal: a weighted sum of hypothesis-side `≤ 0` facts plus
a closed `Rat` algebraic identity, discharged by an explicit-proof-term
construction (`proveCertificateIdentity`). No `Problem` / `denseMatrix` /
`AffCert` data reductions reach the kernel. -/

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
discharged by the explicit-proof-term construction at tactic time. -/
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

/-! ## Explicit-proof-term discharger lemmas (issue #87)

These lemmas are the fixed-arity building blocks for the `normalize` /
`proveMerge` proof-term construction that discharges the closed `Rat`
algebraic identities on both the optimal and infeasible branches of the
`lp` tactic. Each lemma is applied by the metaprogram with `mkAppN` and
explicit arguments; the
kernel only structurally typechecks the resulting term, never reducing a
recursive function over the certificate. Numeral side conditions on `Q`
denominators reduce via GMP `Int` arithmetic — the only kernel *reduction*
in the produced proof.

`⟦L⟧` for a sorted `LinExpr` `{const := r, coeffs := [(x₀,c₀), …]}` is
rendered right-nested with the constant innermost:
`c₀ * x₀ + (c₁ * x₁ + (… + (cₙ₋₁ * xₙ₋₁ + r) …))`. -/

/-- Atom normal form: `x = 1 * x + 0`. Used at fvar leaves of `normalize`. -/
theorem atom_norm (x : Rat) : x = 1 * x + 0 := by
  rw [Rat.one_mul, Rat.add_zero]

/-- Merge step "take left": at this position the smaller atom is on the
left side. Peel its head and thread the recursive result. -/
theorem take_left (h ta b res : Rat) (e : ta + b = res) :
    (h + ta) + b = h + res := by
  subst e; exact Rat.add_assoc h ta b

/-- Merge step "take right": at this position the smaller atom is on the
right side. Float that head past the left operand and thread the recursive
result. -/
theorem take_right (a h tb res : Rat) (e : a + tb = res) :
    a + (h + tb) = h + res := by
  subst e
  rw [Rat.add_comm a (h + tb), Rat.add_assoc, Rat.add_comm tb a]

/-- Merge step "combine": shared atom; coefficients `c'` and `c` combine
to `m = c' + c`. Emit a single `m * x` head and thread the recursive
result. -/
theorem combine (x ta tb res c' c m : Rat)
    (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by
  subst e; subst hm
  grind [Rat.add_mul, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- Merge step "combine to zero": shared atom whose merged coefficient is
zero. Drop the head entirely. -/
theorem combine_zero (x ta tb res c' c : Rat)
    (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by
  subst e
  have hzero : c' * x + c * x = 0 := by
    rw [← Rat.add_mul, hm, Rat.zero_mul]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, Rat.add_zero, Rat.zero_add]

/-- `smul` walk step: scaling pushes `k` through one rendered head. -/
theorem smul_cons (k x c m rest rest' : Rat)
    (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by
  subst hm; subst e
  rw [Rat.mul_add, Rat.mul_assoc]

/-- `neg` walk step: negation pushes through one rendered head. -/
theorem neg_cons (x c m rest rest' : Rat)
    (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by
  subst hm; subst e
  rw [Rat.neg_add, Rat.neg_mul]

/-! ### Mini-`norm_num` for `Q`-shaped `Rat` numeral leaves.

Each leaf proves a closed `Rat` arithmetic fact between three `Q.toRat`
literals. The side condition is a closed `Int` equality discharged by
`mkDecideProof` — the kernel reduces it via GMP `Int` multiply + `decEq`.
This is the only kernel reduction in the produced certificate proof. -/

theorem ratlit_add (qa qb qm : Q)
    (h : (Q.add qa qb).num * (qm.den : Int)
         = qm.num * ((Q.add qa qb).den : Int)) :
    qa.toRat + qb.toRat = qm.toRat := by
  rw [← Q.toRat_add]; exact Q.toRat_eq_of_cross h

theorem ratlit_mul (qa qb qm : Q)
    (h : (Q.mul qa qb).num * (qm.den : Int)
         = qm.num * ((Q.mul qa qb).den : Int)) :
    qa.toRat * qb.toRat = qm.toRat := by
  rw [← Q.toRat_mul]; exact Q.toRat_eq_of_cross h

theorem ratlit_neg (qa qm : Q)
    (h : (Q.neg qa).num * (qm.den : Int)
         = qm.num * ((Q.neg qa).den : Int)) :
    -qa.toRat = qm.toRat := by
  rw [← Q.toRat_neg]; exact Q.toRat_eq_of_cross h

/-! ### Congruence lemmas used at `normalize`'s syntax-node boundaries.

Each is one application per `+`/`-`/`*`/`-` syntax node — O(N) total per
row, not the inner O(N²) hot path. Stated with explicit `Rat` arguments
so the metaprogram applies them via `mkAppN`. -/

theorem add_congr_eq (a A b B : Rat) (ha : a = A) (hb : b = B) :
    a + b = A + B := by subst ha; subst hb; rfl

theorem sub_congr_eq (a A b B : Rat) (ha : a = A) (hb : b = B) :
    a - b = A - B := by subst ha; subst hb; rfl

theorem mul_congr_eq_r (k a A : Rat) (e : a = A) : k * a = k * A := by
  subst e; rfl

theorem neg_congr_eq (a A : Rat) (e : a = A) : -a = -A := by subst e; rfl

theorem sub_to_add_neg (a b : Rat) : a - b = a + (-b) := Rat.sub_eq_add_neg a b

/-- Fast-path normaliser lemma for the `coefficient * atom` pattern that
dominates dense rows: `k * x = k * x + 0`. Stated with `kU`/`kL` separate
so the metaprogram can supply the user's coefficient Expr on the left and
the canonical `Q.toRat` form on the right; the equality is `rfl` once
both reduce, but stating it explicitly lets the rest of the proof keep
`Q.toRat` form uniformly. -/
theorem mul_atom_norm (k x : Rat) : k * x = k * x + 0 := by
  rw [Rat.add_zero]

/-- Fast-path normaliser lemma for the unary `-atom` pattern:
`-x = -1 * x + 0`. -/
theorem neg_atom_norm (x : Rat) : -x = -1 * x + 0 := by
  rw [Rat.add_zero, Rat.neg_mul, Rat.one_mul]

/-! ## Parsing affine `Rat` expressions and `≤`/`=` hypotheses.

The parsing layer is unchanged in spirit from the previous verifier
backend, but it no longer produces `AffCert` / `Problem`-shaped
artefacts. Each parsed row carries:

* `term : Expr` — the source-side Lean expression `lhsᵢ - rhsᵢ`;
* `proof : Expr` of type `term ≤ 0`;
* `linexpr : LinExpr` — numerical coefficients on the parsed variables,
  used to build the LP problem fed to SoPlex and to compute the
  numerical residual after the dual comes back.

The proof-facing artefacts are thunks: most parsed rows receive a zero
dual multiplier, so their Lean-side term and proof are never demanded by
the certificate.
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
  term : MetaM Expr
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

/-- Evaluate a `LinExpr` at a concrete `Rat` assignment, given a fixed
variable ordering. Variables in `e.coeffs` not present in `vars` are
silently ignored (degenerate-parse coeffs are treated as zero). -/
private def LinExpr.evalAt (e : LinExpr) (vars : Array FVarId) (xs : Array Rat) :
    Rat := Id.run do
  let mut acc := e.const
  for (v, c) in e.coeffs do
    for h : i in [0:vars.size] do
      if vars[i] == v then
        acc := acc + c * xs[i]!
  return acc

/-- Partition a `LinExpr`'s coefficients by variable scope, used by the
inner-`∀` paths to split `(φ − ψ)(x, y) = α(x) + β(y) + γ` after parsing
the body as a single linear expression. Returns `(β, α, outside)` where:
- `β` holds the coeffs over `ys` (with `const := 0`),
- `α` holds the coeffs over `xs` together with the constant `γ := e.const`,
- `outside` lists any FVarIds in `e.coeffs` that belong to neither scope
  (these trigger the syntactic-rejection / outer-parameter checks).

Algebraically: `e = α.const + Σ (v,c) ∈ α.coeffs c·v + Σ (v,c) ∈ β.coeffs c·v
+ (outside contributions)`. -/
private def LinExpr.partitionXY (e : LinExpr) (xs ys : Array FVarId) :
    LinExpr × LinExpr × Array FVarId := Id.run do
  let mut αCoeffs : Array (FVarId × Rat) := #[]
  let mut βCoeffs : Array (FVarId × Rat) := #[]
  let mut outside : Array FVarId := #[]
  for (v, c) in e.coeffs do
    if xs.any (· == v) then αCoeffs := αCoeffs.push (v, c)
    else if ys.any (· == v) then βCoeffs := βCoeffs.push (v, c)
    else outside := outside.push v
  let α : LinExpr := { const := e.const, coeffs := αCoeffs }
  let β : LinExpr := { coeffs := βCoeffs }
  (β, α, outside)

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/-- Read a `Nat` literal Expr — either `Expr.lit (.natVal n)` or
`OfNat.ofNat n` for a `Nat`-typed `OfNat`. -/
private def parseNatLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  match e with
  | .lit (.natVal n) => return some n
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
        match args[1]! with
        | .lit (.natVal n) => return some n
        | _ => return none
      else
        return none

/-- Read an `Int` literal Expr in `Int.ofNat n` / `Int.negSucc n` form. -/
private def parseIntLit? (e : Expr) : MetaM (Option Int) := do
  let e ← whnfR e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Int.ofNat && args.size == 1 then
    return (← parseNatLit? args[0]!).map (Int.ofNat ·)
  else if fn.isConstOf ``Int.negSucc && args.size == 1 then
    return (← parseNatLit? args[0]!).map (Int.negSucc ·)
  else
    return none

/-- Try to recognise `e` as `Q.toRat ⟨n, d, _⟩` for closed `Int`/`Nat`
literals `n`, `d`. Inspected BEFORE `whnfR` so the `@[inline]` `Q.toRat`
isn't unfolded out of the parse. -/
private def tryQToRat? (e : Expr) : MetaM (Option Rat) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``Soplex.Tactic.RatLin.Q.toRat && args.size == 1 do
    return none
  let q ← whnfR args[0]!
  let qFn := q.getAppFn
  let qArgs := q.getAppArgs
  unless qFn.isConstOf ``Soplex.Tactic.RatLin.Q.mk && qArgs.size == 3 do
    return none
  let some n ← parseIntLit? qArgs[0]! | return none
  let some d ← parseNatLit? qArgs[1]! | return none
  if h : d = 0 then return none
  else return some (Rat.normalize n d h)

/-- Scalar recogniser for the `lp` explicit-proof-term discharger.
Recognises `Q.toRat ⟨…⟩`, `@OfNat.ofNat Rat n _`, `let`-bound scalars,
and `Neg`/`HMul`/`HDiv` *of scalars* — but deliberately does **not**
descend into `HAdd`/`HSub` operands. The full `parseScalar?` recurses
through `+`/`-` trees to fold compound closed scalars like `2 - 1`;
calling that at every syntax node of a dense row was an O(N²) blow-up
in tactic-side work. Skipping `HAdd`/`HSub` keeps every call bounded by
the maximal *scalar-only* subtree: a row body (`HAdd` head) is rejected
in O(1), and a coefficient like `1/3` or `c` is still recognised. A
genuinely compound `(2+3) * x` is not short-circuited here, but
`normalize` still handles it via its structural `HAdd` path. -/
private partial def quickScalarLit? (e : Expr) : MetaM (Option Rat) := do
  if let some v ← tryQToRat? e then return some v
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => quickScalarLit? value
      | none => return none
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
      match args[1]! with
      | .lit (.natVal n) => return some (OfNat.ofNat n)
      | _ => return none
    if fn.isConstOf ``Neg.neg && args.size == 3 then
      return (← quickScalarLit? args[2]!).map (fun x => -x)
    if fn.isConstOf ``HMul.hMul && args.size == 6 then
      match ← quickScalarLit? args[4]!, ← quickScalarLit? args[5]! with
      | some a, some b => return some (a * b)
      | _, _ => return none
    if fn.isConstOf ``HDiv.hDiv && args.size == 6 then
      match ← quickScalarLit? args[4]!, ← quickScalarLit? args[5]! with
      | some _, some 0 => return none
      | some a, some b => return some (a / b)
      | _, _ => return none
    return none

/-- Recognise an expression as a reducibly-closed `Rat` scalar (matches
  the previous backend's scalar-recogniser policy exactly), with an added
  pre-`whnfR` check for `Q.toRat ⟨…⟩` literals so the explicit-proof-term
  discharger's `mkRatLit` outputs are recognised as scalars. -/
private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  if let some v ← tryQToRat? e then
    return some v
  let e ← withReducible <| whnfR e
  if let some v ← tryQToRat? e then
    return some v
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
      throwError "lp: strict hypothesis `{origin}` is not supported"
  | some (.le, lhsExpr, rhsExpr, lhs, rhs) =>
      let row := lhs.sub rhs
      return #[{
        term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
        expr := row,
        proof := mkAppM ``rat_sub_nonpos_of_le #[proof] }]
  | some (.eq, lhsExpr, rhsExpr, lhs, rhs) =>
      let d := lhs.sub rhs
      return #[
        {
          term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
          expr := d,
          proof := mkAppM ``rat_sub_nonpos_of_eq #[proof] },
        {
          term := mkAppM ``HSub.hSub #[rhsExpr, lhsExpr],
          expr := d.neg,
          proof := do mkAppM ``rat_sub_nonpos_of_eq #[← mkEqSymm proof] }]

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

/-! ## Cached `Rat`-arithmetic operator templates (issue #87).

The explicit-proof-term discharger calls `mkRatAdd`/`mkRatMul`/`mkRatLit`
O(N²) times per certificate. Each call previously routed through
`mkAppM`, which re-ran typeclass inference for `HAdd`/`HMul`/`HSub`/`Ne`
every time — collectively the dominant tactic-side cost at N=40. We
pre-build the fully-applied instance Exprs once below (constant Exprs,
no metavariables) and use them via raw `mkApp2`/`mkApp` in the hot
path. -/

/-- `@HAdd.hAdd Rat Rat Rat instHAdd_Rat_Rat_Rat` — partially-applied,
takes the two `Rat` arguments. -/
private def addRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHAdd [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instAdd)
  mkApp4 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HMul.hMul Rat Rat Rat _` partially applied. -/
private def mulRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHMul [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instMul)
  mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HSub.hSub Rat Rat Rat _` partially applied. -/
private def subRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHSub [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instSub)
  mkApp4 (mkConst ``HSub.hSub [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@Neg.neg Rat Rat.instNeg` partially applied. -/
private def negRatFn : Expr :=
  mkApp2 (mkConst ``Neg.neg [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instNeg)

/-- Build `-a : Rat` Expr without typeclass inference. -/
private def mkRatNeg (a : Expr) : Expr := mkApp negRatFn a

/-- Build a `Rat` `HMul.hMul a b` Expr without typeclass inference. -/
private def mkRatMul (a b : Expr) : MetaM Expr :=
  return mkApp2 mulRatFn a b

/-- Build a `Rat` `HAdd.hAdd a b` Expr without typeclass inference. -/
private def mkRatAdd (a b : Expr) : MetaM Expr :=
  return mkApp2 addRatFn a b

/-- Build a `Rat` `HSub.hSub a b` Expr without typeclass inference. -/
private def mkRatSub (a b : Expr) : MetaM Expr :=
  return mkApp2 subRatFn a b

/-- The standing proof `Nat.one_ne_zero : (1 : Nat) ≠ 0`, used as the
denominator-nonzero proof for every integer-denominator `Q` payload. -/
private def den1NeZeroProof : Expr := mkConst ``Nat.one_ne_zero

/-- Emit a `Q.mk num den den_ne` Expr for the `Rat` value `r`. For the
overwhelmingly common `r.den = 1` case (integer coefficients) we use the
cached `Nat.one_ne_zero` proof instead of running `mkDecideProof`. -/
private def mkQLit (r : Rat) : MetaM Expr := do
  let numE : Expr := match r.num with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)
  let denE : Expr := mkNatLit r.den
  let denNeProof ←
    if r.den == 1 then
      pure den1NeZeroProof
    else
      let denNeType : Expr := mkApp3 (mkConst ``Ne [Level.succ Level.zero])
        (mkConst ``Nat) denE (mkNatLit 0)
      mkDecideProof denNeType
  return mkApp3 (mkConst ``Soplex.Tactic.RatLin.Q.mk) numE denE denNeProof

/-- Build a `Rat` literal Expr.  We emit a `Q.toRat`-normalised form so
that the explicit-proof-term discharger (issue #87) can apply
`Q.toRat_add`/`toRat_mul`/`toRat_neg` without bridging through
`Rat.div`-form literals. -/
private def mkRatLit (r : Rat) : MetaM Expr := do
  return mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) (← mkQLit r)

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
that gets fed to `decide` for the sign check and to
`proveCertificateIdentity` for the algebraic identity proof. -/
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

/-! ## Explicit-proof-term discharger machinery (issue #87).

`normalize` walks the affine grammar of a `Rat` expression and returns
`(L : LinExpr, pf : e = ⟦L⟧)` with `L.coeffs` strictly sorted by atom
position in the global `vars` array. `⟦L⟧` is a concrete `Expr`
right-nested rendering with the constant innermost. The proof `pf` is
built from fixed-arity lemmas; the kernel only structurally typechecks
the resulting term, reducing only closed `Int` literal arithmetic inside
the `ratlit_*` side conditions. -/

/-- Position of `v` in the global `vars` array. The caller guarantees
membership; on lookup failure we return `vars.size` so the result is
still a valid total order (the unknown atom sorts last). -/
private def varIdx (vars : Array FVarId) (v : FVarId) : Nat :=
  vars.idxOf? v |>.getD vars.size

/-- Render a sorted `LinExpr` into the canonical right-nested `Rat`
Expr `c₀*x₀ + (c₁*x₁ + (… + (cₙ₋₁*xₙ₋₁ + r) …))`. -/
private def render (L : LinExpr) : MetaM Expr := do
  let mut acc ← mkRatLit L.const
  let n := L.coeffs.size
  for i in [0:n] do
    let idx := n - 1 - i
    let (v, c) := L.coeffs[idx]!
    let cE ← mkRatLit c
    let head ← mkRatMul cE (Expr.fvar v)
    acc ← mkRatAdd head acc
  return acc

/-! ### Cached side-condition templates for the numeral leaves.

`proveRatlit{Add,Mul,Neg}` are called O(N²) times per certificate. Each
call previously ran `inferType` on the partial lemma application to
extract the `(Q.add qa qb).num * (qm.den : Int) = …` side-condition Expr.
We compute that side-condition template just once per `lp` invocation,
keyed in an `IO.Ref`, and instantiate `qa`/`qb`/`qm` per leaf. -/

initialize ratlitAddDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitMulDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitNegDomainRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Walk past `n` `Pi` binders and return the body. -/
private def stripForalls (n : Nat) (e : Expr) : Expr :=
  match n with
  | 0 => e
  | n + 1 => stripForalls n e.bindingBody!

/-- Compute / fetch the cached side-condition template of `ratlit_add`,
i.e. the type of its 4th explicit argument with the first three
arguments left as bvars `#2, #1, #0` (referring to `qa, qb, qm`). -/
private def getRatlitAddDomain : MetaM Expr := do
  if let some t ← ratlitAddDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_add)
  -- typ : ∀ qa qb qm, hType → conclusion
  let body3 := stripForalls 3 typ
  let dom := body3.bindingDomain!
  ratlitAddDomainRef.set (some dom)
  return dom

private def getRatlitMulDomain : MetaM Expr := do
  if let some t ← ratlitMulDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_mul)
  let dom := (stripForalls 3 typ).bindingDomain!
  ratlitMulDomainRef.set (some dom)
  return dom

private def getRatlitNegDomain : MetaM Expr := do
  if let some t ← ratlitNegDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_neg)
  let dom := (stripForalls 2 typ).bindingDomain!
  ratlitNegDomainRef.set (some dom)
  return dom

/-- Build an `Eq.refl`-shaped proof of a closed `Int` literal equality.
The two sides are kernel-reducible to the same numeric value (this is
what makes the leaf valid in the first place), so `Eq.refl LHS` typechecks
where `LHS = RHS` is expected — moving the literal arithmetic work from
the tactic-side `mkDecideProof` into a single kernel reduction. -/
private def mkEqReflProof (hType : Expr) : Expr :=
  -- hType has shape `@Eq Int LHS RHS`; extract LHS and emit `Eq.refl LHS`.
  let lhs := hType.appFn!.appArg!
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Int) lhs

/-- Numeral leaf builder: build a proof of `qaE.toRat + qbE.toRat = qmE.toRat`
where `qmE` is the `Q` payload of `(qaVal + qbVal : Rat)`. -/
private def proveRatlitAdd (qaE qbE : Expr) (qaVal qbVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := qaVal + qbVal
  let qmE ← mkQLit mVal
  let template ← getRatlitAddDomain
  let hType := template.instantiate #[qmE, qbE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp4 (mkConst ``ratlit_add) qaE qbE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Numeral leaf builder: build a proof of `qaE.toRat * qbE.toRat = qmE.toRat`. -/
private def proveRatlitMul (qaE qbE : Expr) (qaVal qbVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := qaVal * qbVal
  let qmE ← mkQLit mVal
  let template ← getRatlitMulDomain
  let hType := template.instantiate #[qmE, qbE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp4 (mkConst ``ratlit_mul) qaE qbE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Numeral leaf builder: build a proof of `-qaE.toRat = qmE.toRat`. -/
private def proveRatlitNeg (qaE : Expr) (qaVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := -qaVal
  let qmE ← mkQLit mVal
  let template ← getRatlitNegDomain
  let hType := template.instantiate #[qmE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp3 (mkConst ``ratlit_neg) qaE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Precompute a "spine" of a sorted `LinExpr`: an array of head Exprs
`c_k * x_k`, an array of `Q.mk` payloads for each coefficient (for the
numeral leaves), and an array of suffix renderings where
`suffix[k] = ⟦{coeffs.drop k, const}⟧`. Suffix Exprs are built once and
shared by reference across the whole proof, avoiding the O(N³)
re-rendering of every merge step. -/
private def precomputeSpine (L : LinExpr) :
    MetaM (Array Expr × Array Expr × Array Expr) := do
  let n := L.coeffs.size
  let mut heads : Array Expr := Array.mkEmpty n
  let mut qs : Array Expr := Array.mkEmpty n
  for k in [0:n] do
    let (v, c) := L.coeffs[k]!
    let qE ← mkQLit c
    qs := qs.push qE
    let cE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qE
    heads := heads.push (← mkRatMul cE (Expr.fvar v))
  -- Suffix renderings, built right-to-left so each entry references the next.
  let mut suffix : Array Expr := Array.mkEmpty (n + 1)
  suffix := suffix.push (← mkRatLit L.const)
  for k in [0:n] do
    -- The k-th iteration produces `suffix[k+1]` ... no wait, we build from
    -- right to left so suffix[i] is built when k = n - i.
    let _ := k
    let idx := suffix.size  -- next slot
    let cur := suffix[suffix.size - 1]!
    let h := heads[n - idx]!  -- correct head to prepend
    suffix := suffix.push (← mkRatAdd h cur)
  -- `suffix` now has size n+1, with suffix[0] = mkRatLit const (the
  -- innermost) and suffix[n] = full ⟦L⟧. Reverse so suffix[k] is the
  -- rendering starting at coeff k.
  return (heads, qs, suffix.reverse)

/-- The linear ordered merge primitive — the one core proof primitive.

Given two `LinExpr`s `La` and `Lb` whose `coeffs` are sorted ascending by
`varIdx vars`, produce the sorted merge `L = La ⊕ Lb` together with a
proof `pf : ⟦La⟧ + ⟦Lb⟧ = ⟦L⟧`. Linear in `|La.coeffs| + |Lb.coeffs|`,
with all suffix Exprs precomputed and shared by reference. -/
private partial def proveMerge (vars : Array FVarId) (La Lb : LinExpr) :
    MetaM (LinExpr × Expr) := do
  let (headA, qA, suffA) ← precomputeSpine La
  let (headB, qB, suffB) ← precomputeSpine Lb
  let (L, pf, _resE) ← go headA qA suffA headB qB suffB 0 0
  return (L, pf)
where
  /-- Returns `(L, pf, ⟦L⟧)` where `pf : ⟦La⟧.suffix i + ⟦Lb⟧.suffix j = ⟦L⟧`
  and `⟦L⟧` is the result-side spine built incrementally (each step
  prepends a single head Expr to the shared previous tail). -/
  go (headA qA suffA headB qB suffB : Array Expr) (i j : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    let aDone := i ≥ La.coeffs.size
    let bDone := j ≥ Lb.coeffs.size
    if aDone && bDone then
      -- Base: pure constants. The leaf expects bare `Q` payloads.
      let qaE ← mkQLit La.const
      let qbE ← mkQLit Lb.const
      let (mVal, _qmE, pf) ← proveRatlitAdd qaE qbE La.const Lb.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    if aDone then
      let (vB, cB) := Lb.coeffs[j]!
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!  -- bare const since i = La.coeffs.size
      let tbE := suffB[j+1]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_right) #[aE, h, tbE, resPrev, pRest]
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    if bDone then
      let (vA, cA) := La.coeffs[i]!
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!
      let bE := suffB[j]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_left) #[h, taE, bE, resPrev, pRest]
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    let (vA, cA) := La.coeffs[i]!
    let (vB, cB) := Lb.coeffs[j]!
    let iA := varIdx vars vA
    let iB := varIdx vars vB
    -- Descending-varIdx convention: coeffs[0] is the largest varIdx, which
    -- the render places outermost. The overall next-outermost head comes
    -- from whichever side has the strictly larger varIdx at its current
    -- position; equal varIdx triggers the `combine` rule.
    if iA > iB then
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!
      let bE := suffB[j]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_left) #[h, taE, bE, resPrev, pRest]
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    else if iA < iB then
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!
      let tbE := suffB[j+1]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_right) #[aE, h, tbE, resPrev, pRest]
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    else
      let (mVal, qmE, hm) ← proveRatlitAdd qA[i]! qB[j]! cA cB
      let xE := Expr.fvar vA
      let (restL, pRest, resPrev) ←
        go headA qA suffA headB qB suffB (i+1) (j+1)
      let taE := suffA[i+1]!
      let tbE := suffB[j+1]!
      let cAE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qA[i]!
      let cBE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qB[j]!
      let mE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qmE
      if mVal = 0 then
        let pf := mkAppN (mkConst ``combine_zero)
          #[xE, taE, tbE, resPrev, cAE, cBE, pRest, hm]
        return (restL, pf, resPrev)
      else
        let newHead ← mkRatMul mE xE
        let resE ← mkRatAdd newHead resPrev
        let pf := mkAppN (mkConst ``combine)
          #[xE, taE, tbE, resPrev, cAE, cBE, mE, pRest, hm]
        return ({ restL with coeffs := #[(vA, mVal)] ++ restL.coeffs }, pf, resE)

/-- Scale a sorted `LinExpr` by a closed nonzero `Rat` literal `k`, with
proof `k * ⟦La⟧ = ⟦L⟧`. Linear walk; preserves sortedness. -/
private partial def proveSmul (kE : Expr) (kVal : Rat) (La : LinExpr) :
    MetaM (LinExpr × Expr) := do
  let (_headA, qA, suffA) ← precomputeSpine La
  let qkE ← mkQLit kVal
  let (L, pf, _) ← go qA suffA qkE 0
  return (L, pf)
where
  go (qA suffA : Array Expr) (qkE : Expr) (i : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let qaE ← mkQLit La.const
      let (mVal, _qmE, pf) ← proveRatlitMul qkE qaE kVal La.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    let (v, c) := La.coeffs[i]!
    let (mVal, qmE, hm) ← proveRatlitMul qkE qA[i]! kVal c
    let xE := Expr.fvar v
    let (restL, pRest, resPrev) ← go qA suffA qkE (i+1)
    let cE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qA[i]!
    let mE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qmE
    let restE := suffA[i+1]!
    let pf := mkAppN (mkConst ``smul_cons)
      #[kE, xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal = 0 then
      return (restL, pf, resPrev)
    else
      let newHead ← mkRatMul mE xE
      let resE ← mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)

/-- Negate a sorted `LinExpr`, with proof `-⟦La⟧ = ⟦L⟧`. Linear walk;
preserves sortedness. -/
private partial def proveNeg (La : LinExpr) : MetaM (LinExpr × Expr) := do
  let (_headA, qA, suffA) ← precomputeSpine La
  let (L, pf, _) ← go qA suffA 0
  return (L, pf)
where
  go (qA suffA : Array Expr) (i : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let qaE ← mkQLit La.const
      let (mVal, _qmE, pf) ← proveRatlitNeg qaE La.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    let (v, c) := La.coeffs[i]!
    let (mVal, qmE, hm) ← proveRatlitNeg qA[i]! c
    let xE := Expr.fvar v
    let (restL, pRest, resPrev) ← go qA suffA (i+1)
    let cE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qA[i]!
    let mE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qmE
    let restE := suffA[i+1]!
    let pf := mkAppN (mkConst ``neg_cons)
      #[xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal = 0 then
      return (restL, pf, resPrev)
    else
      let newHead ← mkRatMul mE xE
      let resE ← mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)

/-- Build `Eq.refl` typed as `lhs = rhs` for two `Rat` Exprs which are
defeq under kernel reduction. Used at literal leaves and atoms, where
`mkRatLit r` and the user's literal Expr (or `1*x + 0` from `atom_norm`)
agree under closed-`Rat` reduction. -/
private def mkRatEqByDefeq (lhs rhs : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)

/-- Build `Eq.trans` directly via `mkApp` on the `Eq.trans` constant,
without `Lean.Meta.mkEqTrans`'s `isDefEq` middle-term unification, which
is unnecessary when the two halves agree syntactically by construction. -/
private def mkEqTransFast (α aE bE cE p q : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) α aE bE cE p q

/-- Like `proveNeg`, `proveSmul`, `proveMerge` — except this also returns
the rendered `⟦L⟧` Expr alongside the proof, so callers can chain without
re-rendering. The rendered Expr is built incrementally, sharing tails. -/
private partial def proveNegR (La : LinExpr) : MetaM (LinExpr × Expr × Expr) := do
  let (L, pf) ← proveNeg La
  return (L, pf, ← render L)

/-- Structural-recursion normaliser. Returns `(L, pf, rL)` with
`pf : e = rL` and `rL = ⟦L⟧`. The rendered `rL` is threaded through the
recursion so the proof terms reference shared spine Exprs instead of
re-rendering them at every syntax node. -/
private partial def normalizeR (vars : Array FVarId) (e : Expr) :
    MetaM (LinExpr × Expr × Expr) := do
  -- Quick scalar-literal check (no recursion through `HAdd`/etc.). The
  -- full recursive `parseScalar?` is far more expensive — calling it at
  -- every syntax node dominated tactic-side typeclass inference.
  if let some r ← quickScalarLit? e then
    let lit ← mkRatLit r
    let pf ← mkRatEqByDefeq e lit
    return ({const := r}, pf, lit)
  let eW := e   -- skip `whnfR`: dense rows from `parseExpr` are already in
                -- the recognised head-symbol shape.
  match eW with
  | .fvar id =>
      -- `parseExpr` has already type-checked the atoms in this row/goal
      -- (only `Rat`-typed fvars survive into `vars`), so we skip the
      -- per-atom `inferType + isDefEq ty Rat` check that previously
      -- accounted for nearly all the tactic-side typeclass inference work.
      let L : LinExpr := {coeffs := #[(id, 1)]}
      let pf := mkApp (mkConst ``atom_norm) eW
      let rL ← render L
      return (L, pf, rL)
  | _ =>
      let fn := eW.getAppFn
      let args := eW.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HAdd in{indentExpr eW}"
          let aE := args[4]!
          let bE := args[5]!
          let (La, pa, rA) ← normalizeR vars aE
          let (Lb, pb, rB) ← normalizeR vars bE
          let step1 := mkAppN (mkConst ``add_congr_eq) #[aE, rA, bE, rB, pa, pb]
          if Lb.coeffs.size == 1 && Lb.const == 0 then
            let (vB, cB) := Lb.coeffs[0]!
            if !La.coeffs.any (·.1 == vB) then
              let h := rB.appFn!.appArg!  -- extract `cB*vB` from `cB*vB + 0`
              let zeroE ← mkRatLit 0
              let addZeroProof := mkApp (mkConst ``Rat.add_zero) rA
              let pm := mkAppN (mkConst ``take_right)
                #[rA, h, zeroE, rA, addZeroProof]
              let rAddRB ← mkRatAdd rA rB
              let rL ← mkRatAdd h rA
              let pf := mkEqTransFast ratType eW rAddRB rL step1 pm
              let L : LinExpr := { La with coeffs := #[(vB, cB)] ++ La.coeffs }
              return (L, pf, rL)
          let (L, pm) ← proveMerge vars La Lb
          let rL ← render L
          let rAddRB ← mkRatAdd rA rB
          let pf := mkEqTransFast ratType eW rAddRB rL step1 pm
          return (L, pf, rL)
      | .const ``HSub.hSub _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HSub in{indentExpr eW}"
          let aE := args[4]!
          let bE := args[5]!
          let (La, pa, rA) ← normalizeR vars aE
          let (Lb, pb, rB) ← normalizeR vars bE
          let (Lnb, pn, rLnb) ← proveNegR Lb
          let (L, pm) ← proveMerge vars La Lnb
          let rL ← render L
          let negBExpr := mkRatNeg bE
          let negRB := mkRatNeg rB
          let midSub ← mkRatAdd aE negBExpr
          let midAdd ← mkRatAdd rA rLnb
          let step1 := mkAppN (mkConst ``sub_to_add_neg) #[aE, bE]
          let step_neg := mkAppN (mkConst ``neg_congr_eq) #[bE, rB, pb]
          let step_neg_full := mkEqTransFast ratType negBExpr negRB rLnb step_neg pn
          let step2 := mkAppN (mkConst ``add_congr_eq)
            #[aE, rA, negBExpr, rLnb, pa, step_neg_full]
          let chained1 := mkEqTransFast ratType eW midSub midAdd step1 step2
          let pf := mkEqTransFast ratType eW midAdd rL chained1 pm
          return (L, pf, rL)
      | .const ``Neg.neg _ =>
          unless args.size == 3 do
            throwError "lp(normalize): malformed Neg.neg in{indentExpr eW}"
          let aE := args[2]!
          if aE.isFVar then
            let xFVar := aE.fvarId!
            let L : LinExpr := {coeffs := #[(xFVar, -1)]}
            let pf := mkApp (mkConst ``neg_atom_norm) aE
            let rL ← render L
            return (L, pf, rL)
          let (La, pa, rA) ← normalizeR vars aE
          let (L, pn, rL) ← proveNegR La
          let negRA := mkRatNeg rA
          let step1 := mkAppN (mkConst ``neg_congr_eq) #[aE, rA, pa]
          let pf := mkEqTransFast ratType eW negRA rL step1 pn
          return (L, pf, rL)
      | .const ``HMul.hMul _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HMul in{indentExpr eW}"
          let lhsE := args[4]!
          let rhsE := args[5]!
          if let some kVal ← quickScalarLit? lhsE then
            -- Fast path: `k * fvar x` directly to {coeffs:[(x, k)]}.
            if kVal ≠ 0 && rhsE.isFVar then
              let xFVar := rhsE.fvarId!
              let L : LinExpr := {coeffs := #[(xFVar, kVal)]}
              let pf := mkAppN (mkConst ``mul_atom_norm) #[lhsE, rhsE]
              let rL ← render L
              return (L, pf, rL)
            let (Lr, pr, rLr) ← normalizeR vars rhsE
            if kVal = 0 then
              let L : LinExpr := {}
              let zeroE ← mkRatLit 0
              let zeroMulPf ← mkAppM ``Rat.zero_mul #[rhsE]
              return (L, zeroMulPf, zeroE)
            let (L, ps) ← proveSmul lhsE kVal Lr
            let rL ← render L
            let step1 := mkAppN (mkConst ``mul_congr_eq_r)
              #[lhsE, rhsE, rLr, pr]
            let kMulRLr ← mkRatMul lhsE rLr
            let pf := mkEqTransFast ratType eW kMulRLr rL step1 ps
            return (L, pf, rL)
          else if let some kVal ← quickScalarLit? rhsE then
            let (Lr, pr, rLr) ← normalizeR vars lhsE
            let kE := rhsE
            if kVal = 0 then
              let L : LinExpr := {}
              let zeroE ← mkRatLit 0
              let mulZeroPf ← mkAppM ``Rat.mul_zero #[lhsE]
              return (L, mulZeroPf, zeroE)
            let (L, ps) ← proveSmul kE kVal Lr
            let rL ← render L
            let mulComm ← mkAppM ``Rat.mul_comm #[lhsE, kE]
            let step1 := mkAppN (mkConst ``mul_congr_eq_r)
              #[kE, lhsE, rLr, pr]
            let kMulLhs ← mkRatMul kE lhsE
            let kMulRLr ← mkRatMul kE rLr
            let pf := mkEqTransFast ratType eW kMulLhs rL mulComm
              (mkEqTransFast ratType kMulLhs kMulRLr rL step1 ps)
            return (L, pf, rL)
          else
            throwError "lp(normalize): nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | _ =>
          throwError "lp(normalize): unsupported Rat expression{indentExpr eW}"

/-- Phase 2 closer: given `lhsId : Expr` and a closed `Rat` value `cVal`,
build a proof `lhsId = mkRatLit cVal`. Normalises `lhsId` and, since the
algebraic identity already holds numerically, the resulting `LinExpr` has
no surviving coefficients and the constant matches `cVal` — closing by a
`rfl` step at the rendered constant. -/
private def proveCertificateIdentity (vars : Array FVarId) (lhsId : Expr)
    (cVal : Rat) : MetaM Expr := do
  let (L, pfNorm, _rL) ← normalizeR vars lhsId
  unless L.const == cVal do
    throwError "lp(closeIdentity): normalised constant {L.const} does not match expected residual {cVal}"
  unless L.coeffs.isEmpty do
    throwError "lp(closeIdentity): normalization invariant violated; {L.coeffs.size} surviving atom(s)"
  -- `pfNorm : lhsId = rL` and `rL = mkRatLit cVal`, so `pfNorm` is the proof we want.
  let cExpr ← mkRatLit cVal
  let target ← mkEq lhsId cExpr
  mkExpectedTypeHint pfNorm target

/-! ## Per-goal driver.

Given a parsed atomic `Rat` goal `lhs op rhs` and the collected `≤`/`=`
hypotheses-as-rows, build the LP, run SoPlex, and assemble the direct
certificate proof. -/

/-- Assemble the optimal-branch certificate proof from the numerical
multipliers and the parsed rows. Shared between the SoPlex-driven path
and the trivial closed-goal short-circuit (where multipliers are all
zero and `c = objLin.const`). -/
private def assembleLeProof (rows : Array Row) (strict : Bool)
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
  -- Explicit-proof-term discharge of `lhsId = c` (issue #87).
  let identProof ← proveCertificateIdentity vars lhsId c
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
      -- `sumExpr = c` (issue #91), sharing `proveCertificateIdentity`
      -- with the optimal branch.
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

/-! ## Existential goals (`∃ x₁ … xₙ : Rat, B`).

Closes goals of the form `∃ x₁ … xₙ : Rat, B` where `B` is a flat
conjunction of atomic non-strict (in)equality constraints over the
existential binders and reducibly-closed numeric constants only.

The algorithm:

1. Strip nested `∃ x : Rat, …` binders into a single block (entered via
   one `lambdaBoundedTelescope` per binder so the body is canonicalised
   in the same environment the atomic-goal extractor sees).
2. Parse the body as a flat conjunction of atomic Rat (in)equalities;
   reject strict constraints, nested quantifiers, or non-atomic shapes.
3. Verify the **closed-body invariant over the canonicalised atoms**:
   every free `Rat` local appearing in any extracted `LinExpr` must be
   an existential binder. Locals that hide behind reducible
   abbreviations, `let`-bindings, projections, or coercions are
   canonicalised by `parseExpr`'s `withReducible <| whnfR` before the
   check, so the check sees the post-canonicalisation atoms.
4. Build a witness LP: `max 0 subject to A x ≤ b` (objective `c = 0`).
   Any feasible point is optimal at value `0`.
5. Run SoPlex via `solveExact` and branch:
   - `.optimal x*` → splice the primal as `Rat` literals into an
     `Exists.intro` chain; recurse on the now-closed residual body.
   - `.infeasible` → fall back to an inconsistency probe on the outer
     hypotheses alone. If that certifies `H` inconsistent, close by
     `absurd`. Otherwise surface a "body infeasible, context
     consistent" error.
   - anything else → surface the underlying solver status.
6. The residual after splicing is a closed `And`/`Eq`/`LE` conjunction
   in `Rat`; `solveGoal` discharges each conjunct via the closed-goal
   atomic short-circuit (no SoPlex call, empty weighted sum).

Soundness comes from Lean reconstructing each primal value as a `Rat`
literal and rebuilding the residual proof — solver row activities and
objective values are not trusted. -/

/-- Is `e` of the form `∃ x : Rat, …`? Used as the existential-goal
dispatch predicate. -/
private def isExistsRat? (e : Expr) : MetaM Bool := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``Exists && args.size == 2 do return false
  let α ← whnf args[0]!
  return α.isConstOf ``Rat

/-- Peel an outer chain of `∃ x : Rat, …` binders into a single block.
Calls `k` with the array of binder fvars and the body (with binders
substituted as fvars). The fvars are only valid inside `k`. -/
private partial def peelExistsRat (target : Expr) (acc : Array FVarId)
    (k : Array FVarId → Expr → MetaM α) : MetaM α := do
  -- `whnf` may unfold `LE.le` for `Rat` into `Rat.blt _ _ = false`, so
  -- preserve the original `target` to pass into `k`; only the `whnf`
  -- form is consulted to decide whether the head is `Exists`.
  let targetW ← whnf target
  let fn := targetW.getAppFn
  let args := targetW.getAppArgs
  if fn.isConstOf ``Exists && args.size == 2 then
    let α ← whnf args[0]!
    if α.isConstOf ``Rat then
      let pred := args[1]!
      return ← Meta.lambdaBoundedTelescope pred 1 fun xs body => do
        peelExistsRat body (acc.push xs[0]!.fvarId!) k
  k acc target

/-- Collect atomic non-strict Rat (in)equalities from an existential
body, descending only through `And`. Throws on strict inequalities,
nested quantifiers, or any non-atomic shape. -/
private partial def collectExistsAtoms (body : Expr) :
    ParseM (Array (Rel × LinExpr × LinExpr)) := do
  -- Detect `And` on a `whnfR`-reduced form (matching the atomic-goal
  -- top-level `And` dispatch in `solveGoal`). The non-reduced `body`
  -- is what we pass to `parseAtomic?`: reducible whnf can unfold
  -- `LE.le` into `Rat.blt _ _ = false`, which `parseAtomic?` wouldn't
  -- recognise.
  let bodyW ← whnfR body
  if let some (left, right) := isAnd? bodyW then
    return (← collectExistsAtoms left) ++ (← collectExistsAtoms right)
  match ← parseAtomic? body with
  | none =>
      throwError
        "lp: existential body must be a flat conjunction of atomic non-strict {
          ""}Rat (in)equality constraints; got{indentExpr body}"
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict inequalities are not supported in existential bodies"
  | some (rel, _, _, lhs, rhs) =>
      return #[(rel, lhs, rhs)]

/-- Closed-body invariant check, post-canonicalisation.

For each extracted `LinExpr`, every free `Rat` local in `.coeffs` must
be an existential binder. Outer parameters (or `let`-bindings that
canonicalise to non-binder fvars) are rejected here with a precise
message identifying the offending local. -/
private def checkClosedBody (atoms : Array (Rel × LinExpr × LinExpr))
    (binders : Array FVarId) : MetaM Unit := do
  let isBinder (v : FVarId) : Bool := binders.any (· == v)
  let checkLin (L : LinExpr) : MetaM Unit := do
    for (v, _) in L.coeffs do
      unless isBinder v do
        let decl ← v.getDecl
        throwError "lp(∃): existential body references non-binder `Rat` local `{
          decl.userName}` after canonicalisation; the closed-existential path {
          ""}requires every linear expression in the body to depend only on the {
          ""}existential binders."
  for (_, lhs, rhs) in atoms do
    checkLin lhs
    checkLin rhs

/-- Solve a witness LP (constant-zero objective) for the existential
binders. On success returns the primal `Array Rat` of size `binders.size`.
On infeasibility returns `Except.error none`; on any non-`.optimal`,
non-`.infeasible` outcome returns `Except.error (some msg)`.

Pre: `lpRows` is in `≤ 0` form (`coeffsᵀ x + const ≤ 0`). -/
private def solveWitnessLP (lpRows : Array LinExpr) (binders : Array FVarId) :
    MetaM (Except (Option String) (Array Rat)) := do
  if lpRows.size = 0 then
    -- No constraints: any witness works; pick `0` for each binder.
    return .ok (Array.replicate binders.size (0 : Rat))
  let rowDense := lpRows.map (·.toDense binders)
  let rowConsts := lpRows.map (·.const)
  let objCoeffs := Array.replicate binders.size (0 : Rat)
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 binders.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => return .error (some s!"invalid generated problem: {repr e}")
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => return .error (some s!"solveExact failed: {repr e}")
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | return .error (some "SoPlex reported optimal but returned no primal certificate")
      return .ok pr.toArray
  | .infeasible => return .error none
  | .unbounded =>
      -- Cannot arise for a constant-zero objective. Treat as a
      -- solver/verifier invariant violation.
      return .error (some "SoPlex reported `unbounded` for a constant-zero objective; treating as an unchecked invariant violation")
  | s => return .error (some s!"solver outcome was unchecked: {repr s}")

/-- Try to certify that the outer hypotheses `rows` (over `vars`) are
inconsistent. Returns `some pf` with `pf : False` on success, or `none`
if the inconsistency probe doesn't fire (no rows, unchecked status, or
the LP says feasible).

This is the existential-path inconsistency-probe fallback: it reuses
the atomic-goal infeasibility branch's Farkas certificate construction,
but with a fixed constant-zero objective (`max 0 subject to H`) so we
are probing only the consistency of `H`. -/
private def tryHypsInconsistent (rows : Array Row) (vars : Array FVarId) :
    MetaM (Option Expr) := do
  if rows.size = 0 then return none
  -- Zero-variable special case: every row is a closed `c ≤ 0` fact.
  -- A row with `const > 0` is *itself* `False`, regardless of the others.
  -- SoPlex aborts on 0-column problems, so we handle this directly
  -- (multiplier 1 on the offending row → `direct_infeasible_close`).
  if vars.size = 0 then
    for row in rows do
      if isLinExprClosed row.expr && decide (0 < row.expr.const) then
        let c := row.expr.const
        let cExpr ← mkRatLit c
        let term ← row.term
        let proof ← row.proof
        let identProof ← proveCertificateIdentity vars term c
        let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
        let hFalse := mkAppN (mkConst ``direct_infeasible_close)
          #[term, cExpr, proof, hC, identProof]
        return some hFalse
    return none
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := Array.replicate vars.size (0 : Rat)
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 vars.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error _ => return none
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error _ => return none
    | .ok sol => pure sol
  match sol.status with
  | .infeasible =>
      let some d := sol.certificate.dual | return none
      let mults := d.rowUpper.toArray
      unless mults.all (fun lam => 0 ≤ lam) do return none
      let rowLins := rows.map (·.expr)
      let zeroLin : LinExpr := {}
      let residual := computeResidual zeroLin rowLins mults
      unless isLinExprClosed residual do return none
      let c := residual.const
      unless decide (0 < c) do return none
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
      let identProof ← proveCertificateIdentity vars sumExpr c
      let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
      let hFalse := mkAppN (mkConst ``direct_infeasible_close)
        #[sumExpr, cExpr, sumProof, hC, identProof]
      return some hFalse
  | _ => return none

/-- Apply `Exists.intro` with the given witness to `g`, returning the
metavariable for the body proof obligation. The witness must be a
`Rat` expression. -/
private def introExistsRat (g : MVarId) (witness : Expr) : MetaM MVarId := do
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let tyW ← whnf ty
    let fn := tyW.getAppFn
    let args := tyW.getAppArgs
    unless fn.isConstOf ``Exists && args.size == 2 do
      throwError "lp(introExistsRat): expected `∃ x : Rat, _`, got{indentExpr ty}"
    let level := match fn with
      | .const _ (u :: _) => u
      | _ => Level.succ Level.zero
    let αE := args[0]!
    let predE := args[1]!
    -- Only beta-reduce the predicate applied to the witness; do not
    -- `whnf` further (it may unfold `LE.le` into `Rat.blt _ _ = false`
    -- and block the residual proof's atomic-comparison dispatch).
    let bodyTy := (mkApp predE witness).headBeta
    let newMVar ← mkFreshExprSyntheticOpaqueMVar bodyTy (tag := `lp_exists_body)
    let proof := mkApp4 (mkConst ``Exists.intro [level]) αE predE witness newMVar
    g.assign proof
    return newMVar.mvarId!

/-! ## Inner-`∀` elimination over x-independent guards.

Extends the existential body grammar with subformulas of shape
`∀ y₁ … yₘ : Rat, G₁ → … → Gₖ → atomic(x, y)` where the universal
guards `Gᵢ` and the atomic body's `y`-dependent part form an LP region
independent of the existential-bound `x`. Each such universal is
eliminated by a sup-LP that bounds `β(y)` over the guard region; the
resulting `α(x) + γ + M ≤ 0` constraint joins the witness LP.

After the witness is spliced, each residual `∀ y, G → atomic(witness, y)`
falls back to the atomic-goal path via `solveGoal`'s
`intros`+`solveAtomic` recursion: `G`-hypotheses are picked up by
`collectHyps`, and the same Farkas multipliers that proved
sup-boundedness reconstruct the bound on `β(y)`. The vacuous-guard
case (`Verified.infeasible` on the sup-LP) adds no constraint to the
witness LP; the atomic-goal infeasibility branch derives `False` from
the `G`-hypotheses post-splicing and closes the atomic via
`False.elim`.

Limitations:
- No outer-parameter promotion: outer Rat locals are rejected in both
  the universal body's `α(x)` and the guards. The two failure modes
  ("Outer parameter in body" vs "Outer parameter in guard") get
  separate diagnostics.
- Strict universal guards and strict universal bodies are rejected.
- Bilinear `x * y` terms in the universal body are rejected by the
  extractor (one side of `*` must be a reducibly-closed Rat scalar). -/

/-- Is `e` of the form `∀ y : Rat, _` with the binder actually used in the
body? `Rat → P` (non-dependent function type) is *not* recognised as a
universal — the inner-`∀` path only fires on quantifiers, not implications. -/
private def isForallRat? (e : Expr) : MetaM Bool := do
  match ← whnf e with
  | .forallE _ ty body _ =>
      let tyW ← whnf ty
      return tyW.isConstOf ``Rat && body.hasLooseBVars
  | _ => return false

/-- Outcome of the sup-LP for one body direction of an x-independent
inner universal. -/
private inductive SupResult
  | /-- Optimal: `M` is the Lean-recomputed value of `β` at the spliced
       primal; the witness LP receives `α(x) + γ + M ≤ 0`. -/
    bounded (M : Rat)
  | /-- Verified vacuity: the guard LP is infeasible; the universal is
       vacuously true and contributes no witness-LP constraint. The
       post-splice atomic obligation falls through to the atomic-goal
       path, which discharges it from the (infeasible) guard hypotheses
       via `False.elim`. -/
    vacuous

/-- Build and solve `max β(y) s.t. (guardsLe each ≤ 0)`.

- `.bounded M` on optimal: `M := β.evalAt` recomputed from the
  solver-returned primal (we do not trust the solver's objective).
- `.vacuous` on infeasible: the guard region is empty.
- Throws on `unbounded` or any unchecked status (with diagnostic). -/
private def runSupLP (yBinders : Array FVarId) (guardsLe : Array LinExpr)
    (β : LinExpr) : MetaM SupResult := do
  if guardsLe.size = 0 then
    -- No guards: feasible region is all of `R^|y|`. If `β` is constant
    -- in `y`, the sup is just that constant; otherwise the sup is `+∞`.
    if β.coeffs.size = 0 then
      return .bounded β.const
    throwError "lp(∀): universal has no guards but `β(y)` is non-constant; {
      ""}sup is unbounded above. Universal constraint impossible under the stated guard."
  -- Guards present: must run the LP to detect vacuity even when `β` is
  -- constant in `y`. A constant-`β` universal with infeasible guards is
  -- still vacuously true, and dropping the residual row is necessary —
  -- otherwise the strengthened witness LP would carry a fake row
  -- `α(x) + γ + β.const ≤ 0` that may rule out an otherwise good
  -- witness (Codex review, issue #45).
  let rowDense := guardsLe.map (·.toDense yBinders)
  let rowConsts := guardsLe.map (·.const)
  let objCoeffs := β.toDense yBinders
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 yBinders.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp(∀): invalid sup-LP: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => throwError "lp(∀): solveExact failed on sup-LP: {repr e}"
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | throwError "lp(∀): sup-LP reported optimal without a primal certificate"
      let M := β.evalAt yBinders pr.toArray
      return .bounded M
  | .infeasible =>
      return .vacuous
  | .unbounded =>
      throwError "lp(∀): sup-LP is unbounded above; universal constraint impossible {
        ""}under the stated guard"
  | s =>
      throwError "lp(∀): sup-LP outcome was unchecked: {repr s}"

/-- Parse a universal guard expression into `≤ 0` directions over
`xBinders ∪ yBinders` (1 row for `≤`, 2 for `=`). No validation against
xBinder occurrence; the caller decides whether x-dependence is acceptable
(the x-independent path rejects it; the Benders path accepts and routes
to constraint generation). Strict guards and unparseable shapes are
still rejected at this layer. -/
private def parseGuardLinExprs (xBinders yBinders : Array FVarId) (g : Expr) :
    MetaM (Array LinExpr) := do
  let parsed ← (parseAtomic? g).run' { vars := xBinders ++ yBinders }
  match parsed with
  | none =>
      throwError "lp(∀): universal guard must be a non-strict atomic Rat {
        ""}(in)equality{indentExpr g}"
  | some (.lt, _, _, _, _) =>
      throwError "lp(∀): strict universal guard is not supported{indentExpr g}"
  | some (.le, _, _, lhs, rhs) =>
      return #[lhs.sub rhs]
  | some (.eq, _, _, lhs, rhs) =>
      let d := lhs.sub rhs
      return #[d, d.neg]

/-- Parse a single universal guard expression as one or two `≤ 0`
`LinExpr`s over `yBinders` only. Rejects strict guards, existential-binder
references, and outer-parameter references (the latter would require
parameter promotion, not currently supported).

Entry point for the x-independent guard path; the Benders path uses
`parseGuardLinExprs` directly and routes x-dependent guards to
constraint generation. -/
private def parseUniversalGuard (xBinders yBinders : Array FVarId) (g : Expr) :
    MetaM (Array LinExpr) := do
  let dirs ← parseGuardLinExprs xBinders yBinders g
  for L in dirs do
    for (v, _) in L.coeffs do
      if xBinders.any (· == v) then
        let name := (← v.getDecl).userName
        throwError "lp(∀): universal guard references existential binder `{name}`{
          indentExpr g}; guards must be independent of `x`"
      unless yBinders.any (· == v) do
        let name := (← v.getDecl).userName
        throwError "lp(∀): universal guard references outer Rat local `{name}`{
          indentExpr g}; v1 does not promote outer parameters to sup-LP variables"
  return dirs

/-- Parse and solve one inner-`∀ y₁ … yₘ : Rat, G₁ → … → Gₖ →
atomic(x, y)` subformula on the x-independent guard path. Returns the
residual `≤ 0` rows (each with coeffs over `xBinders` only and a
constant `γ + M`) to be added to the witness LP. A vacuous universal
contributes zero rows.

The fvars introduced by `forallTelescope` are local to this call; the
returned `LinExpr`s only mention `xBinders`, which remain valid in the
caller's scope. -/
private def parseAndSolveUniversal (xBinders : Array FVarId) (forallExpr : Expr) :
    MetaM (Array LinExpr) := do
  let forallExpr ← whnf forallExpr
  Meta.forallTelescopeReducing forallExpr fun args bodyAtom => do
    -- Partition `args` into `yBinders` (type = Rat) and guard hypotheses
    -- (Prop). The grammar `∀ y₁ … yₘ : Rat, G₁ → … → Gₖ → atomic`
    -- requires all Rat binders to precede all guards.
    let mut yBinders : Array FVarId := #[]
    let mut guardExprs : Array Expr := #[]
    let mut seenGuard : Bool := false
    for arg in args do
      let argId := arg.fvarId!
      let decl ← argId.getDecl
      let ty ← whnf decl.type
      if ty.isConstOf ``Rat then
        if seenGuard then
          throwError "lp(∀): universal `Rat` binders must precede guards in {
            ""}`∀ y₁ … yₘ : Rat, G → … → atomic` shape{indentExpr forallExpr}"
        yBinders := yBinders.push argId
      else
        seenGuard := true
        guardExprs := guardExprs.push arg
    if yBinders.isEmpty then
      throwError "lp(∀): expected at least one `∀ y : Rat, _` binder{
        indentExpr forallExpr}"
    -- Parse guards.
    let mut guardsLe : Array LinExpr := #[]
    for hExpr in guardExprs do
      let gType ← inferType hExpr
      let dirs ← parseUniversalGuard xBinders yBinders gType
      guardsLe := guardsLe ++ dirs
    -- Parse atomic body.
    let parsedBody ← (parseAtomic? bodyAtom).run' { vars := xBinders ++ yBinders }
    let some (rel, _, _, lhsLin, rhsLin) := parsedBody
      | throwError "lp(∀): universal body must be a non-strict atomic Rat {
          ""}(in)equality{indentExpr bodyAtom}"
    if rel = .lt then
      throwError "lp(∀): strict universal body is not supported{
        indentExpr bodyAtom}"
    let d := lhsLin.sub rhsLin
    let bodyDirs : Array LinExpr :=
      match rel with
      | .le => #[d]
      | .eq => #[d, d.neg]
      | .lt => #[]
    -- Validate body coeffs: only in `xBinders ∪ yBinders`. Any other
    -- fvar (outer Rat local) triggers syntactic rejection.
    for L in bodyDirs do
      let (_, _, outside) := L.partitionXY xBinders yBinders
      if outside.size > 0 then
        let nameStrs ← outside.toList.mapM fun v => do
          return s!"`{(← v.getDecl).userName}`"
        throwError "lp(∀): outer Rat local(s) {String.intercalate ", " nameStrs} {
          ""}appear in the universal body's `x`-dependent part{indentExpr bodyAtom}; {
          ""}parametric witnesses are not supported"
    -- Solve sup-LP per direction; collect residuals over `xBinders`.
    let mut residuals : Array LinExpr := #[]
    for bodyDir in bodyDirs do
      let (β, α, _) := bodyDir.partitionXY xBinders yBinders
      match ← runSupLP yBinders guardsLe β with
      | .bounded M =>
          residuals := residuals.push { const := α.const + M, coeffs := α.coeffs }
      | .vacuous =>
          -- No witness-LP constraint; the atomic-goal path discharges
          -- the residual post-splice atomic from the (infeasible)
          -- guards via `False.elim`.
          pure ()
    return residuals

/-! ## Inner-`∀` with x-dependent guards via Benders.

Extends the inner-`∀` path to subformulas whose guards may mention the
surrounding existential variables, via an iterative constraint-generation
(Benders) search for a witness `x*`. The cuts are search-direction
guidance only — they do **not** appear in the final proof. Once Benders
accepts a candidate `x*`, the witness is spliced via `Exists.intro`,
after which each original `∀ y, G(x*, y) → atomic(x*, y)` becomes y-only
(since `x*` is a concrete `Rat` literal); the x-independent sup-LP
machinery discharges each universal directly at `x*`, and the
closed-goal atomic short-circuit handles the residual atoms.

Policy (no completeness commitment):
- `Verified.unbounded` from any subproblem → tactic fails with a precise
  message. Generating sound ray cuts on `x` requires a Farkas projection
  over the guard polyhedron and is not currently implemented.
- Outer `Rat` parameters in either body or guard → rejected at the
  numeric-witness restriction (rejected before any Benders work).
- Strict guards / strict bodies → rejected.
- Extreme dual extraction is not enforced; SoPlex's returned dual is
  used directly, with duplicate-cut detection plus a max-iterations
  safety net guarding against cycling on adversarial bases. -/

/-- One body direction of an x-dependent universal subformula, captured
in the parametric form

```
∀ y, A · y ≤ b + B · x  →  p · y ≤ q · x + r
```

with each guard row stored as a (`guardY`, `guardX`) pair of `LinExpr`s
whose sum is the original guard's `≤ 0` direction. The subproblem at a
concrete `x*` is `max bodyY(y) s.t. (guardY(y) + guardX.evalAt(x*) ≤ 0)`,
and the body is satisfied at `x*` iff `M + bodyX.evalAt(x*) ≤ 0`. -/
private structure BendersUniversal where
  yBinders : Array FVarId
  guardY : Array LinExpr
  guardX : Array LinExpr
  bodyY : LinExpr
  bodyX : LinExpr
  /-- The original `∀`-expression, retained only for diagnostics. -/
  source : Expr := default

/-- Outcome of a Benders subproblem solve at a concrete candidate `x*`. -/
private inductive BendersSubResult
  | /-- Subproblem is feasible with finite optimum `M` and dual `λ`.
       `λ.size` equals the row count of the parametric LP. -/
    bounded (M : Rat) (lam : Array Rat)
  | /-- Verified-infeasible guards at `x*`: the universal is vacuously
       true at this candidate, no cut. -/
    infeasibleGuard
  | /-- Subproblem unbounded: fail fast (the corresponding ray cut on
       `x` is non-linear and is not currently produced). -/
    unboundedFail (msg : String)
  | /-- `Verified.unchecked` from SoPlex: fail. -/
    uncheckedFail (msg : String)

/-- Solve the parametric subproblem at a concrete `xStar`: maximise
`bodyY(y)` subject to `guardY[i](y) + guardX[i].evalAt(xStar) ≤ 0`.
Returns `bounded M λ`, `infeasibleGuard`, `unboundedFail`, or
`uncheckedFail`. Dispatches on `Verified.{optimal,infeasible,unbounded,
unchecked}` exactly as the x-independent sup-LP does. -/
private def runBendersSubproblem (u : BendersUniversal)
    (xBinders : Array FVarId) (xStar : Array Rat) : MetaM BendersSubResult := do
  -- Build the y-only rows: each `guardY[i]` with constant
  -- `guardX[i].evalAt(xStar)`. A constant-`bodyY` subproblem with no
  -- y-only rows has its optimum equal to `bodyY.const` (treated as
  -- bounded), and a constant-`bodyY` subproblem with no constraints can
  -- still arrive via constant guards — let SoPlex handle it normally.
  let nRows := u.guardY.size
  let mut rowLins : Array LinExpr := Array.mkEmpty nRows
  for h : i in [0:nRows] do
    let gy := u.guardY[i]
    let gx := u.guardX[i]!
    let c := gx.evalAt xBinders xStar
    rowLins := rowLins.push { const := gy.const + c, coeffs := gy.coeffs }
  if u.yBinders.isEmpty then
    -- Degenerate: no y-variables. `bodyY` is then constant and the
    -- subproblem is feasibility-of-guards only. Check guard feasibility
    -- numerically (all rows must satisfy `const ≤ 0`).
    let allOk := rowLins.all (fun L => decide (L.const ≤ 0))
    if !allOk then return .infeasibleGuard
    return .bounded u.bodyY.const (Array.replicate nRows 0)
  if rowLins.isEmpty then
    -- No guards: feasible region is `R^|y|`. Bounded iff `bodyY` is
    -- constant in y.
    if u.bodyY.coeffs.size = 0 then
      return .bounded u.bodyY.const #[]
    return .unboundedFail
      "lp (Benders): subproblem has no guards but `p · y` is non-constant; sup is +∞."
  let rowDense := rowLins.map (·.toDense u.yBinders)
  let rowConsts := rowLins.map (·.const)
  let objCoeffs := u.bodyY.toDense u.yBinders
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 u.yBinders.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => return .uncheckedFail s!"invalid Benders subproblem LP: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => return .uncheckedFail s!"solveExact failed on Benders subproblem: {repr e}"
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | return .uncheckedFail "Benders subproblem reported optimal without a primal certificate"
      let some d := sol.certificate.dual
        | return .uncheckedFail "Benders subproblem reported optimal without a dual certificate"
      -- Recompute objective at primal; do not trust SoPlex's number.
      let M := u.bodyY.evalAt u.yBinders pr.toArray
      let lam := d.rowUpper.toArray
      -- Sanity: nonnegativity of multipliers (a maximize LP's row-upper
      -- duals must be ≥ 0; reject otherwise).
      unless lam.all (fun l => 0 ≤ l) do
        return .uncheckedFail "Benders subproblem dual has a negative multiplier"
      return .bounded M lam
  | .infeasible =>
      return .infeasibleGuard
  | .unbounded =>
      return .unboundedFail
        ("lp (Benders): cannot produce a linear cut from an unbounded subproblem; " ++
         "the goal may still be true but requires symbolic-QE machinery " ++
         "that is not currently implemented.")
  | s =>
      return .uncheckedFail s!"Benders subproblem outcome was unchecked: {repr s}"

/-- Compute the Benders optimal-point cut from a subproblem with dual
multipliers `λ`. In the parametric form `∀ y, A·y ≤ b + B·x → p·y ≤ q·x + r`,
the issue's formula is `(λᵀ B − q) · x ≤ r − λᵀ b`. In our `≤ 0`
representation this is `cut := bodyX - Σᵢ λᵢ · guardX[i] ≤ 0`. -/
private def computeBendersCut (u : BendersUniversal) (lam : Array Rat) : LinExpr := Id.run do
  let mut acc : LinExpr := u.bodyX
  for h : i in [0:u.guardX.size] do
    let l := lam[i]!
    if l ≠ 0 then
      acc := acc.sub (u.guardX[i].smul l)
  return acc

/-- Outcome of canonicalising a candidate Benders cut. -/
private inductive CutCanon
  | /-- Cut canonicalises to `0 ≤ 0` or `0 ≤ c` with `c ≥ 0` — drop it. -/
    tautology
  | /-- Cut canonicalises to `0 ≤ c` with `c < 0` — search cannot
       continue from this candidate without first finding an inconsistency. -/
    contradiction
  | /-- Cut is non-degenerate; carries the canonical form (for duplicate
       detection) plus the proof-shaped `LinExpr` to splice into the master. -/
    normal (key : Array (FVarId × Int) × Int) (cut : LinExpr)

private def fvarLt (a b : FVarId) : Bool :=
  match a.name.quickCmp b.name with
  | .lt => true
  | _ => false

/-- Canonicalise a Benders cut into a form suitable for tautology /
contradiction detection and duplicate hashing. The cut is fixed in
`coeffs · x + const ≤ 0` orientation; canonicalisation clears
denominators, divides by the *positive* gcd, drops zero coeffs, and
sorts coeffs by FVarId. Do **not** sign-flip after this step — the
orientation is intrinsic to the cut. -/
private def canonicaliseCut (cut : LinExpr) : CutCanon := Id.run do
  -- Step 1: drop zero coeffs and sort. (`addCoeff` should already have
  -- merged duplicates, but we re-sort here.)
  let nz := cut.coeffs.filter (fun (_, c) => c ≠ 0)
  let sorted := nz.qsort (fun (a, _) (b, _) => fvarLt a b)
  if sorted.isEmpty then
    -- Pure-constant `const ≤ 0` form.
    if cut.const ≤ 0 then return .tautology
    else return .contradiction
  -- Step 2: clear denominators by multiplying by LCM of all denominators
  -- (including const's).
  let allDens : Array Nat :=
    (sorted.map (fun (_, c) => c.den)).push cut.const.den
  let lcmDen : Nat := allDens.foldl Nat.lcm 1
  let lcmInt : Int := Int.ofNat lcmDen
  let scaleRat (r : Rat) : Int := r.num * (lcmInt / Int.ofNat r.den)
  let intCoeffs : Array (FVarId × Int) := sorted.map (fun (v, c) => (v, scaleRat c))
  let intConst : Int := scaleRat cut.const
  -- Step 3: divide by positive gcd of |intCoeffs| and |intConst|.
  let mut g : Nat := intConst.natAbs
  for (_, c) in intCoeffs do
    g := Nat.gcd g c.natAbs
  if g = 0 then
    -- All zero (shouldn't happen given sorted.isEmpty short-circuit).
    return .tautology
  let gInt : Int := Int.ofNat g
  let finalCoeffs : Array (FVarId × Int) := intCoeffs.map (fun (v, c) => (v, c / gInt))
  let finalConst : Int := intConst / gInt
  -- Step 4: emit normal form with the proof-shaped `LinExpr` rebuilt
  -- (over the sorted FVarIds; integer coefficients reinterpreted as
  -- `Rat`s).
  let normCoeffs : Array (FVarId × Rat) :=
    finalCoeffs.map (fun (v, c) => (v, Rat.ofInt c))
  let normLin : LinExpr := { const := Rat.ofInt finalConst, coeffs := normCoeffs }
  return .normal (finalCoeffs, finalConst) normLin

/-- A canonical-form key plus the candidate-rejection log. Tracks the
duplicate-detection state across a Benders run. -/
private structure BendersState where
  /-- Canonical keys of cuts already in the master. Append-only. -/
  cutKeys : Array (Array (FVarId × Int) × Int) := #[]
  /-- Master constraints: the `x`-independent body atoms plus all
      accepted cuts, each in `≤ 0` form over `xBinders`. -/
  masterRows : Array LinExpr := #[]
  /-- Candidates already proposed by the master LP (deduplicated by
      vector equality). If the master proposes the same candidate twice
      the search is stuck. -/
  triedCandidates : Array (Array Rat) := #[]
  iter : Nat := 0
  deriving Inhabited

private def keyEq (a b : Array (FVarId × Int) × Int) : Bool :=
  a.snd == b.snd &&
  a.fst.size == b.fst.size &&
  (Array.zip a.fst b.fst).all (fun ((v1, c1), (v2, c2)) => v1 == v2 && c1 == c2)

private def arrayRatEq (a b : Array Rat) : Bool :=
  a.size == b.size && (Array.zip a b).all (fun (x, y) => x == y)

/-- Configurable upper bound on Benders iterations. With cut
canonicalisation and duplicate suppression, finite termination *should*
hold under nondegenerate dual extraction, but adversarial degeneracy
without extreme-dual selection can cycle; the bound is a safety net. -/
private def bendersMaxIter : Nat := 64

/-- Run the Benders cutting-plane search. Returns either a Rat-valued
witness `x*` (each universal verified-satisfied at `x*`) or an error
message. The user-facing proof is built afterwards by the caller via
`introExistsRat` + post-splice validation through the x-independent
sup-LP machinery. -/
private partial def runBendersLoop (xBinders : Array FVarId)
    (initialMaster : Array LinExpr) (universals : Array BendersUniversal) :
    MetaM (Except (Option String) (Array Rat)) := do
  let mut state : BendersState :=
    { masterRows := initialMaster, cutKeys := #[], triedCandidates := #[], iter := 0 }
  while state.iter < bendersMaxIter do
    state := { state with iter := state.iter + 1 }
    -- Solve the master LP.
    let candResult ← solveWitnessLP state.masterRows xBinders
    let xStar ←
      match candResult with
      | .error none =>
          -- Master infeasible. Two ways this happens:
          -- (a) initial master was infeasible (caller falls back to
          --     inconsistency probe);
          -- (b) accumulated cuts made the master infeasible. v1 cannot
          --     distinguish a real infeasibility-of-the-existential
          --     from "search exhausted because cuts over-excluded";
          --     return the same `.error none` so the caller probes
          --     hypotheses (correct fallback semantics).
          return .error none
      | .error (some msg) => return .error (some msg)
      | .ok xStar => pure xStar
    -- Candidate repeat detection.
    if state.triedCandidates.any (arrayRatEq xStar) then
      return .error (some "lp (Benders): made no progress — the same candidate was proposed twice.")
    state := { state with triedCandidates := state.triedCandidates.push xStar }
    -- Subproblem sweep. We accept the candidate iff every universal is
    -- satisfied at `x*`; otherwise we accumulate the *first* violating
    -- cut and restart. Accumulating all violations at once is also
    -- valid but can over-constrain the master; one at a time is the
    -- textbook Benders loop.
    let mut anyViolation := false
    for u in universals do
      match ← runBendersSubproblem u xBinders xStar with
      | .infeasibleGuard =>
          continue
      | .unboundedFail msg => return .error (some msg)
      | .uncheckedFail msg => return .error (some msg)
      | .bounded M lam =>
          let bodyAtX := u.bodyX.evalAt xBinders xStar
          if M + bodyAtX ≤ 0 then continue
          -- Violation: derive cut.
          let cut := computeBendersCut u lam
          match canonicaliseCut cut with
          | .tautology =>
              -- At a violating candidate, an optimal dual must satisfy
              --   cut.evalAt(x*) = M + bodyX.evalAt(x*) > 0,
              -- so a tautological cut here means the dual returned by
              -- SoPlex failed an invariant (stationarity / nonnegativity)
              -- or we computed the cut with the wrong sign. Surface it
              -- distinctly from a routine "weak cut" outcome.
              return .error (some
                ("lp (Benders): derived a tautological cut at a violating " ++
                 "candidate. The dual certificate from SoPlex appears not to be " ++
                 "optimal — this is an invariant violation, not a routine " ++
                 "non-extreme-dual outcome."))
          | .contradiction =>
              -- Cut-augmented master would be inconsistent. Caller
              -- falls back to inconsistency probe on H.
              return .error none
          | .normal key cutLin =>
              if state.cutKeys.any (keyEq key) then
                -- The previous identical cut is already in the master,
                -- so `x*` should not have been master-feasible. Hitting
                -- this branch implies the master LP returned a vertex
                -- the cut set already excludes — again an invariant
                -- violation rather than non-extreme-dual fallout.
                return .error (some
                  ("lp (Benders): duplicate cut produced for a candidate " ++
                   "the existing cut should already exclude — invariant violation."))
              state := { state with
                cutKeys := state.cutKeys.push key
                masterRows := state.masterRows.push cutLin }
              anyViolation := true
              break
    if !anyViolation then
      -- All universals satisfied at `x*`; accept candidate.
      return .ok xStar
  return .error (some
    s!"lp (Benders): hit the max-iterations safety net ({bendersMaxIter}); search exhausted.")

/-- Classification of an inner-`∀` subformula based on whether any
guard mentions an existential binder. -/
private inductive UniversalDispatch
  | /-- All guards are x-independent → residual `≤ 0` rows on `xBinders`
       that join the witness LP directly. -/
    independentGuards (residuals : Array LinExpr)
  | /-- At least one guard mentions an existential binder → Benders
       subproblems (one per body direction). -/
    dependentGuards (universals : Array BendersUniversal)

/-- Classify one universal subformula, building the data needed for
either the x-independent path or the Benders path. The numeric-witness
restriction is enforced here (before any Benders work): outer Rat
parameters in either the body or any guard cause a precise rejection. -/
private def classifyUniversal (xBinders : Array FVarId) (forallExpr : Expr) :
    MetaM UniversalDispatch := do
  let forallExpr ← whnf forallExpr
  Meta.forallTelescopeReducing forallExpr fun args bodyAtom => do
    -- Partition `args` into yBinders (Rat-typed) and guard hypotheses (Prop).
    let mut yBinders : Array FVarId := #[]
    let mut guardExprs : Array Expr := #[]
    let mut seenGuard : Bool := false
    for arg in args do
      let argId := arg.fvarId!
      let decl ← argId.getDecl
      let ty ← whnf decl.type
      if ty.isConstOf ``Rat then
        if seenGuard then
          throwError "lp(∀): universal `Rat` binders must precede guards{
            indentExpr forallExpr}"
        yBinders := yBinders.push argId
      else
        seenGuard := true
        guardExprs := guardExprs.push arg
    if yBinders.isEmpty then
      throwError "lp(∀): expected at least one `∀ y : Rat, _` binder{
        indentExpr forallExpr}"
    -- Parse guards as `Array LinExpr` (no x/y validation yet).
    let mut allGuardDirs : Array LinExpr := #[]
    for hExpr in guardExprs do
      let gType ← inferType hExpr
      let dirs ← parseGuardLinExprs xBinders yBinders gType
      allGuardDirs := allGuardDirs ++ dirs
    -- Validate guard scope: each coefficient must be in `xBinders ∪ yBinders`.
    -- Outer Rat parameters in any guard are rejected (numeric-witness restriction).
    let mut anyXInGuard := false
    for L in allGuardDirs do
      let (_, _, outside) := L.partitionXY xBinders yBinders
      if outside.size > 0 then
        let nameStrs ← outside.toList.mapM fun v => do
          return s!"`{(← v.getDecl).userName}`"
        throwError "lp(∀): outer Rat local(s) {String.intercalate ", " nameStrs} {
          ""}appear in a universal guard{indentExpr forallExpr}; parametric {
          ""}witnesses are not supported"
      for (v, _) in L.coeffs do
        if xBinders.any (· == v) then anyXInGuard := true
    -- Parse body atomic.
    let parsedBody ← (parseAtomic? bodyAtom).run' { vars := xBinders ++ yBinders }
    let some (rel, _, _, lhsLin, rhsLin) := parsedBody
      | throwError "lp(∀): universal body must be a non-strict atomic Rat {
          ""}(in)equality{indentExpr bodyAtom}"
    if rel = .lt then
      throwError "lp(∀): strict universal body is not supported{indentExpr bodyAtom}"
    let d := lhsLin.sub rhsLin
    let bodyDirs : Array LinExpr :=
      match rel with
      | .le => #[d]
      | .eq => #[d, d.neg]
      | .lt => #[]
    -- Validate body coeffs: only in `xBinders ∪ yBinders`. The
    -- numeric-witness restriction is enforced here too.
    for L in bodyDirs do
      let (_, _, outside) := L.partitionXY xBinders yBinders
      if outside.size > 0 then
        let nameStrs ← outside.toList.mapM fun v => do
          return s!"`{(← v.getDecl).userName}`"
        throwError "lp(∀): outer Rat local(s) {String.intercalate ", " nameStrs} {
          ""}appear in the universal body{indentExpr bodyAtom}; parametric {
          ""}witnesses are not supported"
    if !anyXInGuard then
      -- x-independent guards: solve a sup-LP per body direction and
      -- contribute residual `≤ 0` rows on `xBinders` to the witness LP.
      let mut residuals : Array LinExpr := #[]
      for bodyDir in bodyDirs do
        let (β, α, _) := bodyDir.partitionXY xBinders yBinders
        match ← runSupLP yBinders allGuardDirs β with
        | .bounded M =>
            residuals := residuals.push { const := α.const + M, coeffs := α.coeffs }
        | .vacuous => pure ()
      return .independentGuards residuals
    -- At least one guard mentions an x-binder: build one BendersUniversal
    -- per body direction. Each direction shares the same guard data;
    -- only the body splits differ for an `=` body.
    let mut guardY : Array LinExpr := #[]
    let mut guardX : Array LinExpr := #[]
    for L in allGuardDirs do
      let (β, α, _) := L.partitionXY xBinders yBinders
      -- `α` is the x-part with const = L.const; `β` is y-only, const 0.
      guardY := guardY.push β
      guardX := guardX.push α
    let mut bendUniversals : Array BendersUniversal := #[]
    for bodyDir in bodyDirs do
      let (β, α, _) := bodyDir.partitionXY xBinders yBinders
      bendUniversals := bendUniversals.push
        { yBinders := yBinders
          guardY := guardY
          guardX := guardX
          bodyY := β
          bodyX := α
          source := forallExpr }
    return .dependentGuards bendUniversals

/-- Existential-body walker: descend through `And`, recognise either
atomic constraints or inner `∀ y : Rat, G → … → atomic` subformulas.
Each universal is classified into x-independent residual rows or
x-dependent Benders subproblems. -/
private partial def collectExistsBody (xBinders : Array FVarId) (body : Expr) :
    ParseM (Array (Rel × LinExpr × LinExpr) × Array LinExpr × Array BendersUniversal) := do
  let bodyW ← whnfR body
  if let some (left, right) := isAnd? bodyW then
    let (al, ul, bl) ← collectExistsBody xBinders left
    let (ar, ur, br) ← collectExistsBody xBinders right
    return (al ++ ar, ul ++ ur, bl ++ br)
  if ← isForallRat? body then
    match ← classifyUniversal xBinders body with
    | .independentGuards residuals => return (#[], residuals, #[])
    | .dependentGuards universals => return (#[], #[], universals)
  match ← parseAtomic? body with
  | none =>
      throwError "lp: existential body must be a flat conjunction of atomic {
        ""}non-strict Rat (in)equality constraints or `∀ y : Rat, G → atomic` {
        ""}subformulas; got{indentExpr body}"
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict inequalities are not supported in existential bodies"
  | some (rel, _, _, lhs, rhs) =>
      return (#[(rel, lhs, rhs)], #[], #[])

/-- Existential-goal driver. Pre: `g`'s goal type is `∃ x : Rat, …`. -/
private partial def solveExistential (solveGoal : MVarId → TacticM Unit)
    (g : MVarId) : TacticM Unit := do
  -- Collect outer hypotheses (visible before entering the binders); used
  -- only by the inconsistency-probe fallback on `.infeasible`.
  let (hypRows, hypState) ← g.withContext do
    (collectHyps).run {}
  -- Enter the existential telescope, parse the body, solve the witness
  -- LP, and pop the primal back out as an `Array Rat` (closed values
  -- remain valid outside the telescope).
  let result : Except (Option String) (Array Rat) ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    peelExistsRat target #[] fun binders body => do
      if binders.size = 0 then
        throwError "lp(∃): expected at least one `∃ x : Rat, _` binder"
      -- Parse the body. The walker classifies each inner `∀ y : Rat, _`
      -- as x-independent (residual rows on the witness LP) or
      -- x-dependent (Benders subproblems), returning the atoms,
      -- residual rows, and Benders subproblems in one pass.
      let ((atoms, univResiduals, bendersUnivs), _) ←
        (collectExistsBody binders body).run { vars := binders }
      checkClosedBody atoms binders
      -- Encode each atomic constraint as `lhs - rhs ≤ 0` (an `=` atom
      -- expands to a `≤ 0` row in each direction), then append the
      -- inner-`∀` residual rows (each already in `≤ 0` form).
      let mut lpRows : Array LinExpr := #[]
      for (rel, lhs, rhs) in atoms do
        let d := lhs.sub rhs
        match rel with
        | .le => lpRows := lpRows.push d
        | .eq =>
            lpRows := lpRows.push d
            lpRows := lpRows.push d.neg
        | .lt =>
            throwError "lp(∃): strict inequalities are not supported"
      lpRows := lpRows ++ univResiduals
      if bendersUnivs.isEmpty then
        -- No x-dependent guards: a single witness LP solves the whole
        -- problem.
        solveWitnessLP lpRows binders
      else
        -- x-dependent guards present: iterative Benders search. The
        -- accepted candidate is validated post-splice by the
        -- x-independent sup-LP machinery (each original
        -- `∀ y, G(x*, y) → atomic(x*, y)` becomes y-only after
        -- substitution and falls through that path).
        runBendersLoop binders lpRows bendersUnivs
  match result with
  | .ok primal =>
      -- Splice the primal as `Rat` literals into an `Exists.intro` chain.
      let mut curG := g
      for v in primal do
        let wExpr ← mkRatLit v
        curG ← introExistsRat curG wExpr
      -- Residual: closed `And`/`Eq`/`LE` conjunction in `Rat`. Discharge
      -- via the closed-goal atomic short-circuit.
      solveGoal curG
  | .error none =>
      -- Witness LP infeasible: probe whether outer hyps are inconsistent.
      match ← tryHypsInconsistent hypRows hypState.vars with
      | some hFalse =>
          let goalType ← g.getType
          let proof ← mkAppOptM ``False.elim #[some goalType, some hFalse]
          g.assign proof
      | none =>
          throwError "lp(∃): existential body is infeasible and the {
            ""}tactic could not certify that the outer hypotheses are {
            ""}inconsistent. The goal may still be provable by other means."
  | .error (some msg) =>
      throwError "lp(∃): {msg}"

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
    if ← isExistsRat? target then
      solveExistential solveGoal g
    else if let some (left, right) := isAnd? target then
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

private def runMaximize (g : MVarId) (hname : Name) (exprE : Expr) :
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
  -- below. This matches the issue's "expression mentions a variable
  -- absent from hypotheses" pitfall.
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

end Soplex.Tactic.LP
