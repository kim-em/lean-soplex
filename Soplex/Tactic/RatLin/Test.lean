/-
Internal sanity checks for `Soplex.Tactic.RatLin`.

These examples are NOT part of the build — they exist to verify that
`Lin.toNF` reduces in the kernel on closed inputs and that the soundness
theorem closes equality goals when both sides normalise identically.
-/
import Soplex.Tactic.RatLin.NF

namespace Soplex.Tactic.RatLin

open Lin

/-- Local convenience for building `Q` literals. -/
private def Qℤ (n : Int) : Q := ⟨n, 1, by decide⟩

/-! ### `toNF` reduces in the kernel on closed inputs -/

example : toNF (.add (.atom 0) (.atom 1))
        = toNF (.add (.atom 1) (.atom 0)) := rfl

example : toNF (.sub (.atom 0) (.atom 0))
        = toNF (.lit Q.zero) := rfl

example : toNF (.smul (Qℤ 2) (.add (.atom 0) (.atom 1)))
        = toNF (.add (.smul (Qℤ 2) (.atom 0)) (.smul (Qℤ 2) (.atom 1))) := rfl

example :
    toNF (
      .add (.sub (.lit (Qℤ 2)) (.add (.atom 0) (.atom 1)))
           (.add (.smul Q.one (.sub (.atom 0) (.lit Q.one)))
                 (.smul Q.one (.sub (.atom 1) (.lit Q.one)))))
    = toNF (.lit Q.zero) := rfl

/-! ### End-to-end: rewrite via `eval_eq_evalNF`, close by `rfl` -/

-- The two sides have the same `NF`, so after rewriting via
-- `eval_eq_evalNF` on each side the closing `rfl` succeeds.
example (ρ : Nat → Rat) :
    eval (.add (.atom 0) (.atom 1)) ρ
    = eval (.add (.atom 1) (.atom 0)) ρ := by
  rw [eval_eq_evalNF, eval_eq_evalNF]
  -- Goal: NF.eval (toNF (...)) ρ = NF.eval (toNF (...)) ρ
  -- Closed by rfl because toNF reduces to the same NF on both sides.
  rfl

example (ρ : Nat → Rat) :
    eval (.sub (.atom 0) (.atom 0)) ρ
    = eval (.lit Q.zero) ρ := by
  rw [eval_eq_evalNF, eval_eq_evalNF]
  rfl

example (ρ : Nat → Rat) :
    eval (.add (.sub (.lit (Qℤ 2)) (.add (.atom 0) (.atom 1)))
               (.add (.smul Q.one (.sub (.atom 0) (.lit Q.one)))
                     (.smul Q.one (.sub (.atom 1) (.lit Q.one))))) ρ
    = eval (.lit Q.zero) ρ := by
  rw [eval_eq_evalNF, eval_eq_evalNF]
  rfl

end Soplex.Tactic.RatLin
