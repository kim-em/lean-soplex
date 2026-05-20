import Lean
import Init.Data.Vector.Lemmas
import Soplex.Basic
import Soplex.Tactic.Q

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

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

/-! ## Explicit-proof-term discharger lemmas

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

The parsing layer keeps proof-facing row data separate from the dense
LP matrix representation. Each parsed row carries:

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

def ratType : Expr := mkConst ``Rat

def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

def addCoeff (coeffs : Array (FVarId × Rat)) (v : FVarId) (c : Rat) :
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

def LinExpr.add (a b : LinExpr) : LinExpr :=
  { const := a.const + b.const
    coeffs := b.coeffs.foldl (fun acc (v, c) => addCoeff acc v c) a.coeffs }

def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

/-- Convert a `LinExpr` to a dense coefficient `Array Rat` over a fixed
variable ordering. Unknown variables are skipped (treated as zero
coefficient, which only happens in degenerate parses). -/
def LinExpr.toDense (e : LinExpr) (vars : Array FVarId) :
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
def LinExpr.evalAt (e : LinExpr) (vars : Array FVarId) (xs : Array Rat) :
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
def LinExpr.partitionXY (e : LinExpr) (xs ys : Array FVarId) :
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

end Soplex.Tactic.LP.Internal
