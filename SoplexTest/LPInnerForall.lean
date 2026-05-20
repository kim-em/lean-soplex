import Soplex

/-!
`lp` tactic probes for existential bodies with inner
`∀ y : Rat, G₁ → … → Gₖ → atomic(x, y)` subformulas whose guards do
not depend on the outer existential witness. Each universal is
eliminated by a sup-LP that bounds `β(y)` over the guard region; the
resulting `α(x) + γ + M ≤ 0` constraint joins the witness LP.
-/

-- Disjoint regions, two LP calls.
-- sup-LP: `max y subject to 0 ≤ y, y ≤ 1/2` → M = 1/2, giving the
-- residual `−x + 1/2 ≤ 0`. Witness LP: `1 ≤ x, x ≤ 2, 1/2 ≤ x`.
example : ∃ x : Rat, 1 ≤ x ∧ x ≤ 2 ∧ ∀ y : Rat, 0 ≤ y → y ≤ 1/2 → y ≤ x := by lp

-- Two-binder LP-optimum: three sup-LPs around the textbook LP, witness
-- LP delivers an interior point.
example :
    ∃ x₀ x₁ : Rat,
      0 ≤ x₀ ∧ 0 ≤ x₁ ∧
      x₀ ≤ 4 ∧ 2 * x₁ ≤ 12 ∧ 3 * x₀ + 2 * x₁ ≤ 18 ∧
      ∀ y₀ y₁ : Rat,
        0 ≤ y₀ → 0 ≤ y₁ → y₀ ≤ 4 → 2 * y₁ ≤ 12 → 3 * y₀ + 2 * y₁ ≤ 18 →
        3 * y₀ + 5 * y₁ ≤ 3 * x₀ + 5 * x₁ := by lp

-- Vacuous guard: the guard region `y ≤ 0 ∧ 1 ≤ y` is empty, so the
-- universal is vacuously true and contributes no witness-LP row. The
-- post-splice residual `∀ y, y ≤ 0 → 1 ≤ y → y ≤ x` falls through to
-- the atomic-goal path, which derives `False` from the contradictory
-- hypotheses.
example : ∃ x : Rat, ∀ y : Rat, y ≤ 0 → 1 ≤ y → y ≤ x := by lp

-- Vacuous guard with a `β`-constant body: the universal body `x = 1`
-- has no `y` term, but the guards `y ≤ 0 ∧ 1 ≤ y` are still infeasible
-- so the universal is vacuously true. Without solving the sup-LP we
-- would incorrectly add `x = 1` as a witness-LP row and then conflict
-- with the surrounding `x = 0` atom.
example : ∃ x : Rat, x = 0 ∧ ∀ y : Rat, y ≤ 0 → 1 ≤ y → x = 1 := by lp

-- Guard equality + body equality: equality directions cost two LP
-- calls each (`=`-split into two `≤`s).
example : ∃ x : Rat, ∀ y : Rat, y = 1 → x = y := by lp

-- Body `≥` (flipped from `≤`).
example : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ 1 → x ≥ y := by lp

-- Multiple inner-`∀` conjuncts in the same body. Parenthesised so each
-- `∀` block ends *before* the surrounding `∧` — without the parens the
-- inner `∧` would land inside the first universal's body.
example :
    ∃ x : Rat,
      (∀ y : Rat, 0 ≤ y → y ≤ 1 → y ≤ x) ∧
      (∀ z : Rat, 0 ≤ z → z ≤ 2 → x ≤ z + 3) := by lp

-- Nested existentials with inner-`∀`s on each.
example : ∃ x y : Rat, x = 0 ∧ ∀ z : Rat, 0 ≤ z → z ≤ 1 → z ≤ y + 1 := by lp

-- Universal with no `Rat` `∀` binders but with guards: `Rat → ...` is
-- not a `∀ y : Rat, …` quantifier. `isForallRat?` rejects it (the
-- binder isn't used in the body), so the body parses as an atomic
-- shape, which then fails parsing. The inner-`∀` path is not triggered.
example : True := by
  fail_if_success (have : ∃ x : Rat, (1 : Rat) ≤ 0 → x = 0 := by lp)
  trivial

-- Strict universal guard: rejected with targeted error.
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, 0 < y → y ≤ x := by lp)
  trivial

-- Strict universal body: rejected with targeted error.
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y < x := by lp)
  trivial

-- Unbounded sup-LP (no guards): universal constraint impossible under
-- the stated guard.
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, y ≤ x := by lp)
  trivial

-- Unbounded sup-LP under a one-sided guard.
example : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ x := by lp)
  trivial

-- Outer-parameter rejection: outer Rat `a` in the universal body's
-- `x`-dependent part (here in `α(x)` via `x + a`). Syntactic rejection,
-- not a uniform-strengthening failure.
example (a : Rat) (_ha : 0 ≤ a) : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ 1 → y ≤ x + a := by lp)
  trivial

-- Outer-parameter rejection in a guard: outer parameters are not
-- promoted to sup-LP variables.
example (a : Rat) (_ha : 0 ≤ a) : True := by
  fail_if_success (have : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ a → y ≤ x := by lp)
  trivial

-- Existential-binder occurrence in a guard is handled by the Benders
-- path; see `LPBenders.lean` for the dispatch + worked examples.
