import Soplex

/-!
Stage 4a `lp` tactic probes (issue #47): existential bodies with inner
`∀ y : Rat, G(x, y) → atomic(x, y)` subformulas, where the guards may
mention the surrounding existential variables. Each universal is
discharged via iterative Benders constraint generation: the loop solves
a master LP on `x`, plugs the candidate into each parametric subproblem
on `y`, derives optimal-point cuts on `x` from the subproblem duals,
canonicalises and deduplicates them, and loops until every universal is
satisfied at the candidate. Cuts are search-direction guidance only —
the final proof discharges each universal directly at the accepted
candidate via Stage 3's sup-LP machinery.
-/

-- Worked example 1 (issue spec): x-dependent guard `x ≤ y`, body
-- `y ≤ 2 * x`. Two Benders iterations: candidate `x = 0` is rejected
-- by the cut `−2 x ≤ −5` (equivalently `x ≥ 5/2`); candidate `x = 5/2`
-- is accepted.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp

-- The original trivial-body case that used to be rejected by Stage 3
-- (existential binder in a guard); Stage 4a accepts it. The body
-- `y ≤ x` matches the second guard exactly, so the subproblem at the
-- default `x = 0` candidate already satisfies the body.
example : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ x → y ≤ x := by lp

-- Body matches the upper guard exactly; the x-dependent lower guard
-- `x ≤ y` shifts the feasible y-region but doesn't change the body's
-- correctness.
example : ∃ x : Rat, 1 ≤ x ∧ x ≤ 4 ∧
    ∀ y : Rat, x ≤ y → y ≤ x + 1 → y ≤ x + 1 := by lp

-- Multiple x-dependent guards.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 2 ∧
    ∀ y : Rat, x ≤ y → y ≤ x + 1 → 0 ≤ y → y ≤ 3 → y ≤ x + 1 := by lp

-- Inner `∀` with x-dependent guard alongside x-independent atoms in
-- the same existential body (mixed Stage-3-style atoms + Stage-4a
-- universal).
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 5 ∧
    ∀ y : Rat, x ≤ y → y ≤ x + 2 → y ≤ x + 2 := by lp

-- Two x-dependent universals in the same body. Each is checked
-- independently at every candidate; the loop terminates once both
-- are satisfied.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 10 ∧
    (∀ y : Rat, x ≤ y → y ≤ x + 1 → y ≤ x + 1) ∧
    (∀ z : Rat, x ≤ z → z ≤ x + 2 → z ≤ x + 2) := by lp

-- Outer-parameter rejection in the universal body (numeric-witness
-- restriction; the pre-Benders gate rejects this).
example (a : Rat) (_ha : 0 ≤ a) : True := by
  fail_if_success
    (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ x + 1 → y ≤ x + 1 + a := by lp)
  trivial

-- Outer-parameter rejection in a guard (Benders does not promote outer
-- parameters either).
example (a : Rat) (_ha : 0 ≤ a) : True := by
  fail_if_success
    (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ x + a → y ≤ x := by lp)
  trivial

-- Strict universal guard: still rejected (carryover from Stage 3).
example : True := by
  fail_if_success
    (have : ∃ x : Rat, ∀ y : Rat, x < y → y ≤ x + 1 → y ≤ x + 1 := by lp)
  trivial

-- Strict universal body: still rejected.
example : True := by
  fail_if_success
    (have : ∃ x : Rat, ∀ y : Rat, x ≤ y → y ≤ x + 1 → y < x + 2 := by lp)
  trivial

-- Vacuous guard at every candidate (`x ≤ y` and `y ≤ x − 1` are jointly
-- infeasible for any x). Stage 4a's subproblem returns `.infeasibleGuard`;
-- the loop accepts the default candidate, and post-splice Stage 1
-- derives `False` from the contradictory guard hypotheses.
example : ∃ x : Rat, ∀ y : Rat, x ≤ y → y ≤ x - 1 → y ≤ 0 := by lp

-- Master infeasibility falls back to the Stage-2 inconsistency probe
-- on the outer hypotheses: when the existential's atomic constraints
-- are themselves inconsistent and the surrounding context (`h`) is too,
-- the tactic closes by `False.elim`.
example (h : (1 : Rat) ≤ 0) : ∃ x : Rat, 0 ≤ x ∧ x ≤ -1 ∧
    ∀ y : Rat, x ≤ y → y ≤ 0 := by lp

-- A Stage-3 universal (x-independent guard) and a Stage-4a universal
-- (x-dependent guard) coexist in the same existential body. The Stage 3
-- residual joins the master before Benders starts; the Stage 4a problem
-- runs the iterative loop on top.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 10 ∧
    (∀ y : Rat, 0 ≤ y → y ≤ 1 → y ≤ x + 1) ∧
    (∀ z : Rat, x ≤ z → z ≤ x + 2 → z ≤ x + 2) := by lp

-- Nonzero `λᵀ B` in the optimal-point cut. At the initial candidate
-- `x = 0`, the active dual on the x-dependent upper guard `y ≤ x + 1`
-- contributes a nonzero `x`-coefficient to `cutLin = bodyX − λ · guardX`:
-- `cutLin = (−3x − 1) − 2 · (−x − 1) = −x + 1`, giving the cut `x ≥ 1`.
-- At `x = 1` the body `2 · y ≤ 3 · x + 1 = 4` is tight at `y = 2`. Two
-- iterations.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 10 ∧
    ∀ y : Rat, x ≤ y → y ≤ x + 1 → 2 * y ≤ 3 * x + 1 := by lp

-- Three-iteration Benders convergence. At `x = 0`, U1's body
-- `2y ≤ 3x + 1` is violated (max `2y = 2 > 1`); cut `x ≥ 1`. At `x = 1`,
-- U1 is satisfied but U2's body `3z ≤ x + 1 = 2` is violated by
-- `max 3z = 3`; cut `x ≥ 2`. At `x = 2` both universals are tight and
-- accept. The exact iteration count is sensitive to SoPlex's vertex
-- choice on the witness LP — the test simply asserts convergence, not
-- a specific iteration count.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 10 ∧
    (∀ y : Rat, x ≤ y → y ≤ x + 1 → 2 * y ≤ 3 * x + 1) ∧
    (∀ z : Rat, x - 1 ≤ z → z ≤ 1 → 3 * z ≤ x + 1) := by lp

-- Equality body — splits into two `BendersUniversal` entries (one per
-- direction of `y = x`). Both subproblems must succeed for the
-- universal to be accepted at the candidate. Guards force `y = x`, so
-- the body is satisfied identically.
example : ∃ x : Rat, ∀ y : Rat, x ≤ y → y ≤ x → y = x := by lp

-- Unbounded Stage 4a subproblem at the initial candidate: the
-- x-dependent lower bound `x ≤ y` routes the universal through
-- Stage 4a, but with no upper bound on `y` the sup-LP at any candidate
-- is `+∞`. v1 policy is to fail fast with a precise message rather
-- than emit an `x`-independent ray cut (the corresponding cut on `x`
-- would require a Farkas projection over the guard polyhedron,
-- deferred).
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, x ≤ y → y ≤ 0 := by lp)
  trivial
