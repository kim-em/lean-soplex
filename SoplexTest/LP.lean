import Soplex

/-!
Stage 1 `lp` tactic probes for affine `Rat` goals with non-strict
hypotheses.
-/

example (a b : Rat) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by
  lp

example (a b : Rat) (_h₁ : 5 ≥ 2 * a + b) (_h₂ : 1 ≥ a - b) : 6 ≥ 3 * a := by
  lp

example (n : Nat) (x : Rat) (_hn : 0 ≤ n) (_h : x ≤ 0) : x ≤ 0 := by
  lp

example (x : Rat) (_h : x ≤ 0) : x < 1 := by
  lp

example (x y : Rat) (_h : (1 / 2 : Rat) * x + y ≤ 1) : x + 2 * y ≤ 2 := by
  lp

example (a : Rat) (_h : a ≤ 0 ∧ 0 ≤ a) : a = 0 := by
  lp

example (x : Rat) (h : x ≤ 1) : True := by
  fail_if_success (have : x < 1 := by lp)
  fail_if_success (have : 1 > x := by lp)
  have _ := h
  trivial

example (x y : Rat) (_h : x ≤ 1) : True := by
  fail_if_success (have : y ≤ 0 := by lp)
  have _ := y
  trivial

example (x y : Rat) (_h : x * y ≤ 1) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (x : Rat) (_h : x < 1) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (x : Rat) (_h : 1 > x) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (_c _x : Rat) : True := by
  fail_if_success (have : _c * _x ≤ _c * _x := by lp)
  trivial
