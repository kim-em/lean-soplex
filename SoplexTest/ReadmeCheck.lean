import Soplex
open Soplex Soplex.Verify

example (x₀ x₁ : Rat) (_ : x₀ ≤ 4) (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18)
    (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) : 3 * x₀ + 5 * x₁ ≤ 36 := by lp

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp
