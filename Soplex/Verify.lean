/-
  Pure-Lean certificate checker for SoPlex's exact-mode LP output.

  This is the standalone library: no FFI dependency, no `IO`. Consumers
  that want to verify certificates produced elsewhere can depend on
  this module alone via the `SoplexVerify` Lake target.

  Re-exports:

  * `Soplex.Verify.Types`     — `Problem`, `Options`, `DualBundle`,
                                    `Certificate`, `Solution`, errors.
  * `Soplex.Verify.Validate`  — `validate`, `validateOptions`.
  * `Soplex.Verify.Bool`      — decidable `is*` / `check*` checks.
  * `Soplex.Verify.Budget`    — `certificateWithinBudget`: ceiling
                                    on rational coordinate bit lengths.
  * `Soplex.Verify.Arith`     — Rat / Array toolkit and Bool-to-Prop
                                    lemmas used by the soundness layer.
  * `Soplex.Verify.Prop`      — mathematical `IsFeasible` etc.
  * `Soplex.Verify.Sound`     — soundness theorems for accepted
                                    certificates.
  * `Soplex.Verify.Driver`    — `Verified` / `VerifiedSolve`
                                    types and the pure
                                    `Solution`→`Verified` mapping
                                    `verifyOutcome`.

  See `PLAN.md` §"Verification layer" for the design.
-/

import Soplex.Verify.Types
import Soplex.Verify.Validate
import Soplex.Verify.Bool
import Soplex.Verify.Budget
import Soplex.Verify.Arith
import Soplex.Verify.Prop
import Soplex.Verify.Sound
import Soplex.Verify.Driver
