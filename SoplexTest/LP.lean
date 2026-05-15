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

example (x : Rat) (_h : (3 : Rat) * x ≤ 6) : x ≤ 2 := by
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

example (x₁ x₂ x₃ x₄ : Rat)
    (_h1 : 0 ≤ x₁) (_h2 : 0 ≤ x₂) (_h3 : 0 ≤ x₃) (_h4 : 0 ≤ x₄)
    (_cal  : 3 * x₁ + x₂ + 4 * x₃ + 2 * x₄ ≥ 10)
    (_prot : x₁ + 2 * x₂ + 3 * x₄ ≥ 6)
    (_vit  : x₂ + 2 * x₃ + x₄ ≥ 4) :
    2 * x₁ + 3 * x₂ + x₃ + 4 * x₄ ≥ 5 := by
  lp

example (a₁ a₂ a₃ b₁ b₂ b₃ : Rat)
    (_n1 : 0 ≤ a₁) (_n2 : 0 ≤ a₂) (_n3 : 0 ≤ a₃)
    (_n4 : 0 ≤ b₁) (_n5 : 0 ≤ b₂) (_n6 : 0 ≤ b₃)
    (_s1 : a₁ + a₂ + a₃ ≤ 10)
    (_s2 : b₁ + b₂ + b₃ ≤ 15)
    (_d1 : a₁ + b₁ ≥ 8) (_d2 : a₂ + b₂ ≥ 9) (_d3 : a₃ + b₃ ≥ 8) :
    2 * a₁ + 3 * a₂ + 4 * a₃ + 5 * b₁ + b₂ + 3 * b₃ ≥ 30 := by
  lp

example (x y z : Rat)
    (_nx : 0 ≤ x) (_ny : 0 ≤ y) (_nz : 0 ≤ z)
    (_h1 : (1/3 : Rat) * x + (1/5 : Rat) * y + (1/7 : Rat) * z ≤ 1)
    (_h2 : (2/3 : Rat) * x - (1/5 : Rat) * y + (3/7 : Rat) * z ≤ 2)
    (_h3 : -(1/3 : Rat) * x + (4/5 : Rat) * y - (1/7 : Rat) * z ≤ 1) :
    (1/2 : Rat) * x + y + z ≥ 0 := by
  lp

example (x y _z u v w p q r : Rat)
    (_key₁ : 2 * x + y ≤ 4) (_key₂ : x - y ≤ 1)
    (_n1 : 0 ≤ u) (_n2 : 0 ≤ v) (_n3 : 0 ≤ w)
    (_n4 : 0 ≤ p) (_n5 : 0 ≤ q) (_n6 : 0 ≤ r)
    (_b1 : u ≤ 10) (_b2 : v ≤ 10) (_b3 : w ≤ 10)
    (_b4 : p ≤ 10) (_b5 : q ≤ 10) (_b6 : r ≤ 10)
    (_c1 : u + v + w ≤ 25) (_c2 : p + q + r ≤ 25)
    (_c3 : u + p ≤ 15) (_c4 : v + q ≤ 15) (_c5 : w + r ≤ 15) :
    3 * x ≤ 7 := by
  lp
