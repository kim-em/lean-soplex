/-
  Pure-Lean certificate checker for SoPlex's exact-mode LP output.

  This module contains the verifier-facing API and is pure Lean
  logically: it performs no `IO` and treats SoPlex as an oracle whose
  certificates must be checked before proofs are produced. In the
  current package layout it is still built through the main `Soplex`
  dependency graph, which includes the native FFI package. There is no
  separate verifier-only Lake target yet.

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

  SoPlex is treated as an oracle; accepted certificates are checked
  here before producing proofs.
-/

import Soplex.Verify.Types
import Soplex.Verify.Validate
import Soplex.Verify.Bool
import Soplex.Verify.Budget
import Soplex.Verify.Arith
import Soplex.Verify.Prop
import Soplex.Verify.Sound
import Soplex.Verify.Driver
