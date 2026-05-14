/-
  Mathematical (Prop-level) LP predicates.

  These are stated in minimisation form. The sense-aware wrappers
  `IsOptimal` and `IsUnbounded` defer to the min-canonical versions
  after negating the objective.

  Every `Prop` here is decidable in principle — they're all built out
  of decidable predicates on `Rat` — but we keep the `Bool` view
  separate (`Soplex.Verify.Bool`) to make sure the checker uses
  the computational definition while soundness theorems reason about
  the mathematical one.
-/

import Soplex.Verify.Types
import Soplex.Verify.Bool

namespace Soplex.Verify

open Soplex

/-! ## Predicates. -/

/-- `x` satisfies all column bounds of `p`. -/
def ColBoundsSatisfied {m n : Nat} (p : Problem m n) (x : Array Rat) : Prop :=
  x.size = n ∧
  ∀ j : Fin n,
    let (lo, hi) := p.colBounds[j]
    (∀ l, lo = some l → l ≤ x[j.val]!) ∧
    (∀ h, hi = some h → x[j.val]! ≤ h)

/-- `Ax` satisfies all row bounds of `p`. -/
def RowBoundsSatisfied {m n : Nat} (p : Problem m n) (x : Array Rat) : Prop :=
  let ax := evalAx p x
  ∀ i : Fin m,
    let (lo, hi) := p.rowBounds[i]
    (∀ l, lo = some l → l ≤ ax[i.val]!) ∧
    (∀ h, hi = some h → ax[i.val]! ≤ h)

/-- `x` is primal-feasible for `p`. -/
def IsFeasible {m n : Nat} (p : Problem m n) (x : Array Rat) : Prop :=
  ColBoundsSatisfied p x ∧ RowBoundsSatisfied p x

/-- `p` has no feasible point. -/
def IsInfeasible {m n : Nat} (p : Problem m n) : Prop :=
  ¬ ∃ x, IsFeasible p x

/-- `x` minimises `c·x + objOffset` over the feasible region. -/
def IsOptimalMin {m n : Nat} (p : Problem m n) (x : Array Rat) : Prop :=
  IsFeasible p x ∧
    ∀ y, IsFeasible p y → primalObj p x ≤ primalObj p y

/-- The minimisation problem is unbounded below. -/
def IsUnboundedMin {m n : Nat} (p : Problem m n) : Prop :=
  (∃ x, IsFeasible p x) ∧
    ∀ M : Rat, ∃ y, IsFeasible p y ∧ primalObj p y < M

/-! ## Prop-level dual feasibility.

  Mirrors the Bool checks in `Soplex.Verify.Bool` but at the Prop
  level so the soundness proofs can talk about them without
  unfolding `Array.all`/`arrayEq`. The Bool-to-Prop lemmas live in
  `Soplex.Verify.Arith`. -/

/-- Componentwise nonnegativity plus zero-where-the-matching-bound-is-
    absent. Pulled out so both `IsDualFeasible` and `IsFarkasDualFeasible`
    can reuse it. -/
structure DualNonnegZeroWhereAbsent {m n : Nat}
    (p : Problem m n) (d : DualBundle m n) : Prop where
  row_nonneg : ∀ i : Fin m,
    0 ≤ d.rowLower[i] ∧ 0 ≤ d.rowUpper[i]
  col_nonneg : ∀ j : Fin n,
    0 ≤ d.colLower[j] ∧ 0 ≤ d.colUpper[j]
  row_zero_absent : ∀ i : Fin m,
    (p.rowBounds[i].1 = none → d.rowLower[i] = 0) ∧
    (p.rowBounds[i].2 = none → d.rowUpper[i] = 0)
  col_zero_absent : ∀ j : Fin n,
    (p.colBounds[j].1 = none → d.colLower[j] = 0) ∧
    (p.colBounds[j].2 = none → d.colUpper[j] = 0)

namespace DualNonnegZeroWhereAbsent

variable {m n : Nat} {p : Problem m n} {d : DualBundle m n}

/-! Dot-notation size lemmas. `Vector.size_toArray` already proves each
    of these — they're re-exposed on `DualNonnegZeroWhereAbsent` so the
    soundness layer can write `hDual.rowLower_size` next to the other
    facts it pulls from the hypothesis. -/

theorem rowLower_size (_ : DualNonnegZeroWhereAbsent p d) :
    d.rowLower.toArray.size = m := d.rowLower.size_toArray

theorem rowUpper_size (_ : DualNonnegZeroWhereAbsent p d) :
    d.rowUpper.toArray.size = m := d.rowUpper.size_toArray

theorem colLower_size (_ : DualNonnegZeroWhereAbsent p d) :
    d.colLower.toArray.size = n := d.colLower.size_toArray

theorem colUpper_size (_ : DualNonnegZeroWhereAbsent p d) :
    d.colUpper.toArray.size = n := d.colUpper.size_toArray

end DualNonnegZeroWhereAbsent

/-- Stationarity against an arbitrary `q : Vector Rat n`:
    `Aᵀ(yL − yU) + (zL − zU) = q` componentwise. -/
def StationarityAgainst {m n : Nat}
    (p : Problem m n) (d : DualBundle m n) (q : Vector Rat n) : Prop :=
  ∀ j : Fin n,
    (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))[j.val]! +
      (d.colLower[j] - d.colUpper[j]) = q[j]

/-- Full dual feasibility for the optimality certificate: nonnegativity,
    zero-where-absent, and stationarity against the objective `c`. -/
structure IsDualFeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Prop where
  nonneg_zero_absent : DualNonnegZeroWhereAbsent p d
  stationarity : StationarityAgainst p d p.c

/-- Farkas (homogeneous) dual feasibility: nonnegativity, zero-where-absent,
    and stationarity against `0`. -/
structure IsFarkasDualFeasible {m n : Nat}
    (p : Problem m n) (d : DualBundle m n) : Prop where
  nonneg_zero_absent : DualNonnegZeroWhereAbsent p d
  stationarity_zero : ∀ j : Fin n,
    (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))[j.val]! +
      (d.colLower[j] - d.colUpper[j]) = 0

/-- Prop form of `isRecessionRay`. Each row/column with a finite bound
    on a given side constrains the ray's sign on the matching `r[j]!`
    or `(evalAx p r)[i]!`. Equality rows / boxed columns collapse to
    `= 0` by antisymmetry. -/
structure IsRecessionRay {m n : Nat} (p : Problem m n) (r : Array Rat) : Prop where
  size : r.size = n
  col_lo_nonneg : ∀ j : Fin n, p.colBounds[j].1.isSome = true → 0 ≤ r[j.val]!
  col_hi_nonpos : ∀ j : Fin n, p.colBounds[j].2.isSome = true → r[j.val]! ≤ 0
  row_lo_nonneg : ∀ i : Fin m,
    p.rowBounds[i].1.isSome = true → 0 ≤ (evalAx p r)[i.val]!
  row_hi_nonpos : ∀ i : Fin m,
    p.rowBounds[i].2.isSome = true → (evalAx p r)[i.val]! ≤ 0

/-! ## Sense-aware wrappers. -/

/-- Optimality wrt the user's original sense. -/
def IsOptimal {m n : Nat} (p : Problem m n) (sense : ObjSense) (x : Array Rat) : Prop :=
  IsOptimalMin (canonicalize sense p) x

/-- Unboundedness wrt the user's original sense. -/
def IsUnbounded {m n : Nat} (p : Problem m n) (sense : ObjSense) : Prop :=
  IsUnboundedMin (canonicalize sense p)

end Soplex.Verify
