/-
  Denominator-budget check on certificate rationals.

  PLAN.md §"User-facing driver" specifies a `denomBudget` parameter
  on `solveVerified`: a ceiling on the combined `numerator + denominator`
  bit length of every `Rat` coordinate in a returned `Certificate`.

  The check is a pure `Bool` predicate so the user-facing driver can
  wrap a `false` result as `Verified.unchecked .budgetExceeded` without
  touching the certificate checker proper. `Rat` values produced by
  core Lean are reduced by construction, so `num` and `den` can be
  read directly without an explicit `gcd` normalisation step.
-/

import Soplex.Verify.Types

namespace Nat

/-- Bit length of `n` in binary: the smallest `k` such that `n < 2^k`.
    `bitLen 0 = 0`, `bitLen 1 = 1`, `bitLen 2 = 2`, `bitLen 3 = 2`,
    `bitLen 4 = 3`, ... Not in core Lean as of `v4.29.1`; defined here
    in terms of `Nat.log2` so the budget check is purely arithmetic. -/
def bitLen (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

end Nat

namespace Rat

/-- Combined numerator + denominator bit length of a reduced rational.
    Matches the formula in PLAN.md §"User-facing driver":
    `numerator.natAbs.bitLen + denominator.bitLen`. -/
def bitLen (q : Rat) : Nat :=
  q.num.natAbs.bitLen + q.den.bitLen

end Rat

namespace Soplex.Verify

open Soplex

@[inline] private def vectorWithinBudget {k : Nat}
    (n : Nat) (xs : Vector Rat k) : Bool :=
  xs.all (fun q => decide (q.bitLen ≤ n))

@[inline] private def optionVectorWithinBudget {k : Nat}
    (n : Nat) (o : Option (Vector Rat k)) : Bool :=
  match o with
  | none    => true
  | some xs => vectorWithinBudget n xs

@[inline] private def dualWithinBudget {m n_ : Nat}
    (n : Nat) (o : Option (DualBundle m n_)) : Bool :=
  match o with
  | none   => true
  | some d => vectorWithinBudget n d.rowLower
           && vectorWithinBudget n d.rowUpper
           && vectorWithinBudget n d.colLower
           && vectorWithinBudget n d.colUpper

/-- Every populated coordinate of `cert` satisfies `Rat.bitLen ≤ n`,
    where `budget = some n`. `budget = none` disables the check
    (always `true`). Used by `solveVerified` to wrap a `false` as
    `Verified.unchecked .budgetExceeded`. -/
def certificateWithinBudget {m n_ : Nat}
    (budget : Option Nat) (cert : Certificate m n_) : Bool :=
  match budget with
  | none   => true
  | some n =>
    optionVectorWithinBudget n cert.primal
    && dualWithinBudget n cert.dual
    && optionVectorWithinBudget n cert.ray

end Soplex.Verify
