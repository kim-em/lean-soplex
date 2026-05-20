import Soplex

set_option linter.unusedVariables false

/-!
`maximize` forward-direction tactic probes.

`maximize <expr>` runs a sup-LP over the local non-strict linear
hypotheses and injects `have hbound : <expr> ≤ N := <proof>` into the
local context. `maximize h : <expr>` uses `h` as the hypothesis name.

The translation from the verified-optimal LP outcome to the injected
`expr ≤ N` is shared with the atomic-goal `proveEntailed` discharger:
the forward proof is reproved against `rhs := mkRatLit N` rather than
added into a witness LP. This carries the canonicalise/sign-flip,
constant offset, and reflection-equality obligations through the
existing machinery.
-/

-- Bounded LP: max (3 x₀ + 5 x₁) s.t. {0 ≤ x₀, 0 ≤ x₁,
-- x₀ ≤ 4, 2 x₁ ≤ 12, 3 x₀ + 2 x₁ ≤ 18} → N = 36. Tactic injects
-- `hbound : 3 * x₀ + 5 * x₁ ≤ 36`; we then close by `exact hbound`.
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

-- Constant offset baked into N. Same hypotheses cap `3 * x` at 12;
-- offset adds 7, so N = 19.
example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : 3 * x + 7 ≤ 19 := by
  maximize 3 * x + 7
  exact hbound

-- Negative objective exercises the canonicalisation sign-flip
-- non-trivially: `max (-x) s.t. 0 ≤ x = 0`, so N = 0.
example (x : Rat) (_h : 0 ≤ x) : -x ≤ 0 := by
  maximize -x
  exact hbound

-- `maximize` does not solve the surrounding goal — here the goal is
-- `True`, completely unrelated to the LP. After `maximize`, the goal is
-- still `True`; we need a separate step to close it.
example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : True := by
  maximize 3 * x
  trivial

-- Surrounding goal is a slack inequality `expr ≤ N'` with `N' > N`.
-- `maximize` injects the tight bound; the user uses transitivity.
example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) : 3 * x ≤ 100 := by
  maximize 3 * x
  -- hbound : 3 * x ≤ 12
  exact Rat.le_trans hbound (by decide)

-- Hypothesis-name collision: an existing `hbound` is shadowed; the new
-- `hbound` shadows it (matches `have`'s standard behavior).
example (x : Rat) (hbound : True) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 4) :
    3 * x ≤ 12 := by
  maximize 3 * x
  -- The new `hbound : 3 * x ≤ 12` shadows the old `hbound : True`.
  exact hbound

-- Explicit-name form sidesteps any collision concern.
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

-- Closed scalar (no Rat locals, no hypotheses): `maximize 5` injects
-- `hbound : 5 ≤ 5` via the closed-goal short-circuit.
example : True := by
  maximize (5 : Rat)
  trivial

-- Regression for the closed-row inconsistency bypass: a hypothesis like
-- `(1 : Rat) ≤ 0` is itself `False`, and the closed-objective path must
-- probe inconsistency before injecting the vacuous `0 ≤ 0` bound.
example (_h : (1 : Rat) ≤ 0) : False := by
  maximize (0 : Rat)

-- Closed-row inconsistency with the surrounding goal being something
-- other than `False`: the fallback still closes via `False.elim`.
example (_h : (1 : Rat) ≤ 0) : 42 = 7 := by
  maximize (0 : Rat)

-- Two-binder textbook LP, same shape as the issue's worked example.
-- Tests the bounded-case goldening end-to-end on a non-trivial dual.
example (x₀ x₁ : Rat) (_h₁ : 0 ≤ x₀) (_h₂ : 0 ≤ x₁) (_h₃ : x₀ ≤ 4)
    (_h₄ : 2 * x₁ ≤ 12) (_h₅ : 3 * x₀ + 2 * x₁ ≤ 18) :
    2 * x₀ + 4 * x₁ ≤ 28 := by
  maximize 2 * x₀ + 4 * x₁
  exact hbound

-- Rational coefficients with a tight bound. The emitted `N` is
-- `mkRatLit 1`, which is defEq to the goal's `1 : Rat`.
example (x : Rat) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 2) : (1/2 : Rat) * x ≤ 1 := by
  maximize (1/2 : Rat) * x
  exact hbound
