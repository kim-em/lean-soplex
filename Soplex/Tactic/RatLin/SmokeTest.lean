/-
Internal sanity tests for `Soplex.Tactic.RatLin.proveLinearIdentity`.
These exercise the tactic on small LP-shaped algebraic identities
without going through SoPlex.
-/
import Soplex.Tactic.RatLin.Tactic

namespace Soplex.Tactic.RatLin

open Lean Meta Elab Tactic

/-- An `elab` tactic that delegates to `proveLinearIdentity`. -/
elab "rat_lin" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← g.getType
    let proof ← Soplex.Tactic.RatLin.proveLinearIdentity target
    g.assign proof

-- Closed-Rat sanity checks:
example : ((2 : Rat) - 1) + 0 = 1 := by rat_lin
example : ((5 : Rat) - 2 - 3) + 0 = 0 := by rat_lin

-- LP scaling N=2 miniature: x0 ≤ 1 and x1 ≤ 1 ⊨ x0 + x1 ≤ 2.
-- Certificate: (2 - (x0 + x1)) + (1 * (x0 - 1) + 1 * (x1 - 1)) = 0.
example (x0 x1 : Rat) :
    ((2 : Rat) - (x0 + x1)) + (1 * (x0 - 1) + 1 * (x1 - 1)) = 0 := by
  rat_lin

-- Variables with coefficients > 1.
-- Certificate: (5 - (2*x0 + 3*x1)) + (2*(x0 - 1) + 3*(x1 - 1)) = 0.
example (x0 x1 : Rat) :
    ((5 : Rat) - (2 * x0 + 3 * x1)) + (2 * (x0 - 1) + 3 * (x1 - 1)) = 0 := by
  rat_lin

-- Negation.
example (x : Rat) :
    (-x) + x = 0 := by rat_lin

-- Subtraction.
example (x : Rat) :
    x - x = 0 := by rat_lin

-- N=5 miniature.
example (x0 x1 x2 x3 x4 : Rat) :
    ((5 : Rat) - (x0 + x1 + x2 + x3 + x4))
      + (1 * (x0 - 1) + (1 * (x1 - 1) + (1 * (x2 - 1) + (1 * (x3 - 1) + 1 * (x4 - 1)))))
    = 0 := by
  rat_lin

end Soplex.Tactic.RatLin
