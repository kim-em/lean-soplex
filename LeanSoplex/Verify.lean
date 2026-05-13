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
  * `LeanSoplex.Verify.Budget`    — `certificateWithinBudget`: ceiling
                                    on rational coordinate bit lengths.
  * `LeanSoplex.Verify.Arith`     — Rat / Array toolkit and Bool-to-Prop
                                    lemmas used by the soundness layer.
  * `LeanSoplex.Verify.Prop`      — mathematical `IsFeasible` etc.
  * `LeanSoplex.Verify.Sound`     — soundness theorems for accepted
                                    certificates.
  * `LeanSoplex.Verify.Driver`    — `Verified` / `VerifiedSolve`
                                    types and the pure
                                    `Solution`→`Verified` mapping
                                    `verifyOutcome`.

  See `PLAN.md` §"Verification layer" for the design.
-/

import LeanSoplex.Verify.Types
import LeanSoplex.Verify.Validate
import LeanSoplex.Verify.Bool
import LeanSoplex.Verify.Budget
import LeanSoplex.Verify.Arith
import LeanSoplex.Verify.Prop
import LeanSoplex.Verify.Sound
import LeanSoplex.Verify.Driver
