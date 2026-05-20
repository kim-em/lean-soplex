import Soplex

set_option linter.unusedVariables false

/-!
`maximize` forward-direction tactic probes.

These tests cover the injected bound, the named-hypothesis form, failure
policy, and regressions where `maximize` must fall back through
inconsistency rather than introducing a vacuous bound.
-/

example (x₀ x₁ : Rat) (_h₁ : 0 ≤ x₀) (_h₂ : 0 ≤ x₁) (_h₃ : x₀ ≤ 4)
    (_h₄ : 2 * x₁ ≤ 12) (_h₅ : 3 * x₀ + 2 * x₁ ≤ 18) :
    3 * x₀ + 5 * x₁ ≤ 36 := by
  maximize 3 * x₀ + 5 * x₁
  exact hbound

-- Named hypothesis form `maximize h : <expr>`.
example (x₀ x₁ : Rat) (_h₁ : 0 ≤ x₀) (_h₂ : 0 ≤ x₁) (_h₃ : x₀ ≤ 4)
    (_h₄ : 2 * x₁ ≤ 12) (_h₅ : 3 * x₀ + 2 * x₁ ≤ 18) :
    3 * x₀ + 5 * x₁ ≤ 36 := by
  maximize h : 3 * x₀ + 5 * x₁
  exact h

example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : 3 * x + 7 ≤ 19 := by
  maximize 3 * x + 7
  exact hbound

-- Negative objective exercises the canonicalization sign-flip.
example (x : Rat) (_h : 0 ≤ x) : -x ≤ 0 := by
  maximize -x
  exact hbound

-- `maximize` only injects a bound; it does not solve unrelated goals.
example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : True := by
  maximize 3 * x
  trivial

example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : 3 * x ≤ 100 := by
  maximize 3 * x
  exact Rat.le_trans hbound (by decide)

-- Name collisions follow `have`: the injected `hbound` shadows the old one.
example (x : Rat) (hbound : True) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) :
    3 * x ≤ 12 := by
  maximize 3 * x
  exact hbound

example (x : Rat) (hbound : True) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) :
    3 * x ≤ 12 := by
  maximize h : 3 * x
  exact h

-- Inconsistent hypotheses → infeasibility fallback closes the
-- surrounding goal by `False.elim`. The surrounding goal is `False`
-- here; the fallback would close any proposition.
example (x : Rat) (_h₁ : x ≤ 0) (_h₂ : 1 ≤ x) : False := by
  maximize (0 : Rat)

-- Inconsistent hypotheses with an unrelated surrounding goal: the
-- fallback closes whatever the surrounding goal is.
example (x : Rat) (_h₁ : x ≤ 0) (_h₂ : 1 ≤ x) : 42 = 7 := by
  maximize (0 : Rat)

-- Unbounded objective (no upper bound on `x`) → clean diagnostic.
/-- error: maximize: the LP is unbounded above; no finite upper bound exists for this expression under the collected hypotheses -/
#guard_msgs in
example (x : Rat) (_h : 0 ≤ x) : True := by
  maximize 3 * x
  trivial

-- Expression mentions a variable absent from hypotheses → unbounded.
/-- error: maximize: the LP is unbounded above; no finite upper bound exists for this expression under the collected hypotheses -/
#guard_msgs in
example (x y : Rat) (_h : 0 ≤ x ∧ x ≤ 5) : True := by
  maximize y
  trivial

-- Strict hypothesis present → rejected by `collectHyps` with the
-- strict-hypothesis diagnostic. (No clean `#guard_msgs` because the
-- error message includes the hypothesis name.)
example (x : Rat) (_h : 0 < x) : True := by
  fail_if_success (maximize x)
  trivial

-- Non-linear expression → rejected by the affine grammar walker.
example (x y : Rat) (_h : 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1) : True := by
  fail_if_success (maximize x * y)
  trivial

example : True := by
  maximize (5 : Rat)
  trivial

-- Closed-row inconsistency bypass: a hypothesis like `(1 : Rat) ≤ 0`
-- is itself `False`, and the `vars.size = 0` short-circuit must probe
-- inconsistency before injecting the vacuous `0 ≤ 0` bound.
example (_h : (1 : Rat) ≤ 0) : False := by
  maximize (0 : Rat)

-- Closed-row inconsistency with the surrounding goal being something
-- other than `False`: the fallback still closes via `False.elim`.
example (_h : (1 : Rat) ≤ 0) : 42 = 7 := by
  maximize (0 : Rat)

example (x₀ x₁ : Rat) (_h₁ : 0 ≤ x₀) (_h₂ : 0 ≤ x₁) (_h₃ : x₀ ≤ 4)
    (_h₄ : 2 * x₁ ≤ 12) (_h₅ : 3 * x₀ + 2 * x₁ ≤ 18) :
    2 * x₀ + 4 * x₁ ≤ 28 := by
  maximize 2 * x₀ + 4 * x₁
  exact hbound

example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 2) : (1/2 : Rat) * x ≤ 1 := by
  maximize (1/2 : Rat) * x
  exact hbound
