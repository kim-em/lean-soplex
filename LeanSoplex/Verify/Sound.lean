/-
  Soundness theorems bridging the `Bool` checkers in
  `LeanSoplex.Verify.Bool` to the `Prop` predicates in
  `LeanSoplex.Verify.Prop`.

  The central proof obligation is `weak_duality` on `Rat`. The three
  certificate-soundness lemmas (`checkOptimal_sound`,
  `checkInfeasible_sound`, `checkUnbounded_sound`) follow from
  `weak_duality` plus the certificate-specific equalities / strict
  inequalities.

  All theorems are currently stated with their proofs deferred via
  `sorry`. They are the main pure-Lean work item that remains
  outstanding from `PLAN.md`; see issue tracker.
-/

import LeanSoplex.Verify.Bool
import LeanSoplex.Verify.Prop

namespace LeanSoplex.Verify

open LeanSoplex

/-- Weak duality on `Rat`: any primal-feasible `x` and any dual-feasible
    `d` satisfy `dualObj d ≤ primalObj x`.

    Proof shape (per `PLAN.md` §"Verification layer"):

    1. Stationarity `Aᵀ(yL − yU) + (zL − zU) = c` lets us rewrite
       `c·x` as `Σⱼ (Aᵀ(yL − yU) + (zL − zU))ⱼ · xⱼ`.
    2. Swap finite sums to get
       `Σᵢ (yLᵢ − yUᵢ) · (Ax)ᵢ + Σⱼ (zLⱼ − zUⱼ) · xⱼ`.
    3. Use componentwise bound inequalities
       (`yLᵢ ≥ 0 ∧ (Ax)ᵢ ≥ rₗᵢ ⇒ yLᵢ · (Ax)ᵢ ≥ yLᵢ · rₗᵢ`, three
       symmetric variants) to lower-bound each term by its dual-obj
       contribution.
    4. The remaining shifted sum is exactly `dualObj p d`. -/
theorem weak_duality {p : Problem} {x : Array Rat} {d : DualBundle}
    (_hx : isPrimalFeasible p x = true)
    (_hd : isDualFeasible    p d = true) :
    dualObj p d ≤ primalObj p x := by
  sorry

/-- Optimality certificate is sound: a Boolean-accepted certificate
    really witnesses feasibility and min-optimality. -/
theorem checkOptimal_sound {p : Problem} {x : Array Rat} {d : DualBundle}
    (_h : checkOptimal p x d = true) :
    IsFeasible p x ∧ IsOptimalMin p x := by
  sorry

/-- Infeasibility (Farkas) certificate is sound. -/
theorem checkInfeasible_sound {p : Problem} {d : DualBundle}
    (_h : checkInfeasible p d = true) :
    IsInfeasible p := by
  sorry

/-- Unbounded certificate is sound. -/
theorem checkUnbounded_sound {p : Problem} {x ray : Array Rat}
    (_h : checkUnbounded p x ray = true) :
    IsUnboundedMin p := by
  sorry

end LeanSoplex.Verify
