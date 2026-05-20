import Soplex

/-!
`lp` tactic probes for closed existential goals over `Rat`, with flat
conjunctions of non-strict (in)equality constraints as bodies.
-/

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 1 := by lp

-- Single binder with a single atomic constraint.
example : ∃ x : Rat, x ≤ 5 := by lp

-- Single binder with a tight equality.
example : ∃ x : Rat, x = 3 := by lp

-- Single binder, multi-conjunct body.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 1 ∧ x + x ≤ 2 := by lp

-- Nested binders collapse into a single witness LP.
example : ∃ x : Rat, ∃ y : Rat, x + y = 1 ∧ 0 ≤ x ∧ 0 ≤ y := by lp

-- Triple-nested binders with a flat conjunction body.
example : ∃ x y z : Rat, x = 0 ∧ y = 0 ∧ z = 0 := by lp

-- Reducible numeric constants and `let`-expanded numeric locals must
-- be canonicalized away before the closed-body invariant runs.
example : ∃ x : Rat, x ≤ (1 + 2 : Rat) := by lp

example : True := by
  let c : Rat := 7
  have : ∃ x : Rat, x ≤ c := by lp
  trivial

-- Inconsistent-hypothesis case: the existential body itself is
-- infeasible (`x = x + 1` reduces to `0 = 1`), but the outer hyps are
-- inconsistent, so the probe-fallback closes the goal by `absurd`.
example (_h₁ : (a : Rat) ≤ 0) (_h₂ : (1 : Rat) ≤ a) :
    ∃ x : Rat, x = x + 1 := by lp

-- Outer-parameter rejection: a non-binder `Rat` local appears in the
-- existential body after canonicalization.
example (a : Rat) (_ha : 0 ≤ a) : True := by
  fail_if_success (have : ∃ x : Rat, x = a := by lp)
  trivial

-- A genuinely infeasible body under consistent outer hyps fails with
-- a "body infeasible, context consistent" message (not "unprovable").
example (x : Rat) (_h : 0 ≤ x) : True := by
  fail_if_success (have : ∃ y : Rat, y = y + 1 := by lp)
  trivial

-- Strict inequalities in the body are explicitly out of scope.
example : True := by
  fail_if_success (have : ∃ x : Rat, x < 1 := by lp)
  trivial

-- Nested universal in the body without any guards is not in this fragment.
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, x ≤ y := by lp)
  trivial
