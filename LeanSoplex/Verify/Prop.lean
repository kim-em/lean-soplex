/-
  Mathematical (Prop-level) LP predicates.

  These are stated in minimisation form. The sense-aware wrappers
  `IsOptimal` and `IsUnbounded` defer to the min-canonical versions
  after negating the objective.

  Every `Prop` here is decidable in principle — they're all built out
  of decidable predicates on `Rat` — but we keep the `Bool` view
  separate (`LeanSoplex.Verify.Bool`) to make sure the checker uses
  the computational definition while soundness theorems reason about
  the mathematical one.
-/

import LeanSoplex.Verify.Types
import LeanSoplex.Verify.Bool

namespace LeanSoplex.Verify

open LeanSoplex

/-! ## Canonicalisation. -/

/-- Flip the objective in place. Identity on everything else. -/
def negateObjective (p : Problem) : Problem :=
  { p with c := p.c.map Neg.neg, objOffset := -p.objOffset }

/-- Reduce to minimisation form. -/
def canonicalize (sense : ObjSense) (p : Problem) : Problem :=
  match sense with
  | .minimize => p
  | .maximize => negateObjective p

/-! ## Predicates. -/

/-- `x` satisfies all column bounds of `p`. -/
def ColBoundsSatisfied (p : Problem) (x : Array Rat) : Prop :=
  x.size = p.numVars ∧
  ∀ j : Fin p.numVars,
    let (lo, hi) := p.colBounds[j.val]!
    (∀ l, lo = some l → l ≤ x[j.val]!) ∧
    (∀ h, hi = some h → x[j.val]! ≤ h)

/-- `Ax` satisfies all row bounds of `p`. -/
def RowBoundsSatisfied (p : Problem) (x : Array Rat) : Prop :=
  let ax := evalAx p x
  ∀ i : Fin p.numConstraints,
    let (lo, hi) := p.rowBounds[i.val]!
    (∀ l, lo = some l → l ≤ ax[i.val]!) ∧
    (∀ h, hi = some h → ax[i.val]! ≤ h)

/-- `x` is primal-feasible for `p`. -/
def IsFeasible (p : Problem) (x : Array Rat) : Prop :=
  ColBoundsSatisfied p x ∧ RowBoundsSatisfied p x

/-- `p` has no feasible point. -/
def IsInfeasible (p : Problem) : Prop :=
  ¬ ∃ x, IsFeasible p x

/-- `x` minimises `c·x + objOffset` over the feasible region. -/
def IsOptimalMin (p : Problem) (x : Array Rat) : Prop :=
  IsFeasible p x ∧
    ∀ y, IsFeasible p y → primalObj p x ≤ primalObj p y

/-- The minimisation problem is unbounded below. -/
def IsUnboundedMin (p : Problem) : Prop :=
  (∃ x, IsFeasible p x) ∧
    ∀ M : Rat, ∃ y, IsFeasible p y ∧ primalObj p y < M

/-! ## Sense-aware wrappers. -/

/-- Optimality wrt the user's original sense. -/
def IsOptimal (p : Problem) (sense : ObjSense) (x : Array Rat) : Prop :=
  IsOptimalMin (canonicalize sense p) x

/-- Unboundedness wrt the user's original sense. -/
def IsUnbounded (p : Problem) (sense : ObjSense) : Prop :=
  IsUnboundedMin (canonicalize sense p)

end LeanSoplex.Verify
