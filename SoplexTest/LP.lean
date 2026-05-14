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

-- Inconsistent hypotheses → `Verified.infeasible` branch closes any
-- atomic Rat goal by contradiction.
example (x : Rat) (_h₁ : x ≤ 0) (_h₂ : 1 ≤ x) : x = 5 := by lp

-- Unbounded objective → `Verified.unbounded` branch surfaces a clear
-- message rather than fabricating a proof.
/-- error: lp: objective is unbounded above; base=[0], ray=[1] -/
#guard_msgs in
example (x : Rat) : x ≤ 0 := by lp

-- Division → rejected at the linear-expression extractor with a
-- targeted message.
/-- error: lp: division is outside the supported affine Rat grammar -/
#guard_msgs in
example (x : Rat) (_h : x / 2 ≤ 1) : x ≤ 2 := by lp

-- Opaque function application → rejected at the linear-expression
-- extractor's catchall.
example (f : Rat → Rat) (x : Rat) (_h : f x ≤ 1) : True := by
  fail_if_success (have : f x ≤ 1 := by lp)
  trivial

-- Locally `let`-bound scalar → unfolded by `parseScalar?` and accepted
-- as the multiplier on `x`.
example (x : Rat) (_h : x ≤ 1) : True := by
  let c : Rat := 3
  have : c * x ≤ 3 := by lp
  trivial
