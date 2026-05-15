import Soplex

/-!
Downstream-package smoke tests for the `lp` tactic.

These exist to catch the class of bug where `lp` works inside the
Soplex package but fails when invoked from a project that requires
Soplex as a dependency (e.g. due to FFI dylib resolution differences,
stale `.lake/packages/SoplexFFI` artefacts on a bump, or any other
in-tree-vs-downstream divergence).

The set of `(2*a+b ≤ k, a-b ≤ 1, 3*a ≤ k+1)` instances below is the
issue #56 sweep: small two-row LPs whose Farkas certificate is the
trivial `h₁ + h₂` combination. Several specific constants previously
fell through as `.unchecked .optimal` when called from a downstream
package even though the in-tree CI was green.
-/

example (a b : Rat) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a ≤ 5 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 3) (_h₂ : a - b ≤ 1) : 3 * a ≤ 4 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 2) (_h₂ : a - b ≤ 1) : 3 * a ≤ 3 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 1) (_h₂ : a - b ≤ 1) : 3 * a ≤ 2 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 10) (_h₂ : a - b ≤ 1) : 3 * a ≤ 11 := by lp

-- `≥`-flipped form of the original Stage 1 example.
example (a b : Rat) (_h₁ : 5 ≥ 2 * a + b) (_h₂ : 1 ≥ a - b) : 6 ≥ 3 * a := by lp

-- Infeasibility branch: contradictory hypotheses close any goal.
example (x : Rat) (_h₁ : x ≤ 0) (_h₂ : 1 ≤ x) : x = 5 := by lp
