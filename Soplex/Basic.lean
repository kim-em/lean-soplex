/-
  High-level Soplex API.

  The direct SoPlex wrappers live in `SoplexFFI.Basic`. This module
  re-exports them and adds the verified solve driver.
-/

import SoplexFFI.Basic
import Soplex.Verify
import Soplex.LP.Core

namespace Soplex

open Soplex.LP

/-! ## Verified-solve driver.

  Composes `validateOptions`, `validate`, `solveExact`, and
  `verifyOutcome` from `Soplex.Verify.Driver`.
-/

/-- Default `denomBudget` for `solveVerified`: combined numerator +
    denominator bit length per rational coordinate. `10000` is comfortable
    headroom over what well-behaved LPs produce while still ruling out
    refinement runaway. -/
def defaultDenomBudget : Option Nat := some 10000

/-- Drive `validate`, `solveExact`, then the checker, packaged as a
    `VerifiedSolve` carrying a real soundness-lemma proof.

    * `validateOptions` and `validate` run first; either failure
      surfaces as `Except.error`.
    * `Options.presolve` is forced `false` internally: the checker must
      run against the normalized input LP, not whatever SoPlex's
      presolve transformed it into.
    * `denomBudget` is a ceiling on the bit length of every rational
      coordinate in the returned certificate; exceeding it yields
      `Verified.unchecked .budgetExceeded`. `none` disables the check.
    * The returned `normalized` field is `validate p`, the `Problem`
      the proof is indexed by. Downstream code reasons about that
      value, not about the raw user input. -/
def solveVerified {m n : Nat} (opts : Options) (p : Problem m n)
    (denomBudget : Option Nat := defaultDenomBudget) :
    Except SolveError (Verify.VerifiedSolve (m := m) (n := n) opts.sense) := do
  let _ ← validateOptions opts |>.mapError SolveError.invalidOptions
  let normalized ← validate p |>.mapError SolveError.invalidProblem
  let opts' := { opts with presolve := false }
  let sol ← solveExact opts' normalized
  pure { normalized
         verified := Verify.verifyOutcome opts denomBudget normalized sol }

/-- Backend-pluggable variant of `solveVerified`.

    Identical to `solveVerified` except `solveExact` is dispatched
    through an `LPBackend`. Lives in `IO` because backends are
    `IO`-typed (so a future subprocess or remote solver can plug in);
    synchronous backends like `Soplex.Backend.SoplexFFI.backend` just
    lift their `Except` result with `pure`.

    Source-level callers should keep using `solveVerified` for now;
    `solveVerifiedWith` is the migration target once the package split
    lands (#50). -/
def solveVerifiedWith {m n : Nat} (backend : LPBackend) (opts : Options)
    (p : Problem m n) (denomBudget : Option Nat := defaultDenomBudget) :
    IO (Except SolveError (Verify.VerifiedSolve (m := m) (n := n) opts.sense)) := do
  match validateOptions opts with
  | .error e => return .error (.invalidOptions e)
  | .ok _ =>
    match validate p with
    | .error e => return .error (.invalidProblem e)
    | .ok normalized =>
      let opts' := { opts with presolve := false }
      match ← backend.solveExact opts' normalized with
      | .error e => return .error e
      | .ok sol =>
        return .ok { normalized
                     verified := Verify.verifyOutcome opts denomBudget normalized sol }

end Soplex
