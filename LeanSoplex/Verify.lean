/-
  Pure-Lean certificate checker for SoPlex's exact-mode LP output.

  This is the standalone library: no FFI dependency, no `IO`. Consumers
  that want to verify certificates produced elsewhere can depend on
  this module alone via the `LeanSoplexVerify` Lake target.

  Re-exports:

  * `LeanSoplex.Verify.Types`     — `Problem`, `Options`, `DualBundle`,
                                    `Certificate`, `Solution`, errors.
  * `LeanSoplex.Verify.Validate`  — `validate`, `validateOptions`.
  * `LeanSoplex.Verify.Bool`      — decidable `is*` / `check*` checks.
  * `LeanSoplex.Verify.Arith`     — Rat / Array toolkit and Bool→Prop
                                    bridge lemmas used by the soundness
                                    layer.
  * `LeanSoplex.Verify.Prop`      — mathematical `IsFeasible` etc.
  * `LeanSoplex.Verify.Sound`     — soundness theorems (currently
                                    `sorry`-stubbed; see PLAN.md).

  See `PLAN.md` §"Verification layer" for the design.
-/

import LeanSoplex.Verify.Types
import LeanSoplex.Verify.Validate
import LeanSoplex.Verify.Bool
import LeanSoplex.Verify.Arith
import LeanSoplex.Verify.Prop
import LeanSoplex.Verify.Sound
