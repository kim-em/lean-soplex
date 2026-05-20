/-
  Backend-agnostic core for the SoPlex verifier and the `lp` tactic.

  This module exists so the verifier (`Soplex.Verify`) and the tactic
  (`Soplex.Tactic.LP`) can run against multiple solver backends without
  hard-coding the SoPlex FFI. Today it lives inside the `lean-soplex`
  Lake package; a follow-up step (tracked in #50) extracts it into a
  standalone `lp-core` package with no native dependencies, alongside
  `lp-verify` and `lp-tactic`.

  The vocabulary types (`Problem`, `Options`, `Solution`, `Certificate`,
  `SolveError`) currently still live in `SoplexFFI.Types` — that file
  is documented as pure Lean with no FFI dependency, so consuming it
  from a future native-deps-free package is structurally possible. The
  `LPBackend` record below is the new abstraction; backends export a
  `def backend : LPBackend` and (optionally) self-register so the
  tactic layer can pick a default.
-/

import SoplexFFI.Types
import Std.Data.HashMap

open Std

namespace Soplex.LP

/-- Concrete LP solver backend.

    A backend takes a normalized `Problem` (and the `Options` that
    came with it) and returns either an error or a `Solution` whose
    `Certificate` the pure-Lean verifier (`Soplex.Verify.verifyOutcome`)
    can check.

    `solveExact` is `IO`-typed because the most useful non-FFI backends
    (out-of-process subprocess wrappers, future remote solvers) need
    `IO`. Synchronous backends like the current SoPlex FFI lift their
    `Except` result with `pure`. -/
structure LPBackend where
  /-- Stable, machine-readable identifier. Used as the registry key
      and as the value of `set_option lp.backend`. Conventionally a
      short lowercase string with `-` separators (e.g. `"soplex-ffi"`,
      `"soplex-json"`, `"pure"`). -/
  name : String
  /-- Default priority when this backend is one of several registered.
      Lower runs first. Reserved bands:

      *  10  — fast native binding (FFI),
      *  50  — out-of-process subprocess (JSON),
      * 100  — pure-Lean reference,
      * 1000 — experimental / opt-in.

      Tactic users override via `set_option lp.backend` or per-call
      argument; do not re-register the same name with a different
      priority. -/
  defaultPriority : Nat := 100
  /-- Solve a validated LP and return its certificate. The argument is
      the post-`validate` problem; backends should not re-run
      `validate`. Backends are responsible for any solver-side
      canonicalization (`negateObjective` etc.). -/
  solveExact : {m n : Nat} → Options → Problem m n →
               IO (Except SolveError (Solution m n))
  /-- Lazy pre-flight probe: is this backend usable in the current
      process? `.ok ()` on success, a human-readable string on miss
      (e.g. `"executable `soplex` not on PATH"`, `"shared library
      failed to load: ..."`). Default `pure (.ok ())`.

      Probes run only when the tactic actually consults fallback. They
      never run during `initialize`. -/
  probe : IO (Except String Unit) := pure (.ok ())

namespace LPBackend

/-- Strict-less order on backends for fallback iteration: lower
    `defaultPriority` runs first; ties break on lexicographic `name`. -/
def lt (a b : LPBackend) : Bool :=
  a.defaultPriority < b.defaultPriority ||
    (a.defaultPriority == b.defaultPriority && a.name < b.name)

end LPBackend

/-- Process-global registry of installed backends, keyed by `name`.

    Populated by each backend module's `initialize` block, so only
    backends the user has actually imported show up. Lookups produce a
    fresh sorted array; do not rely on `Std.HashMap` iteration order. -/
initialize backendRegistry : IO.Ref (HashMap String LPBackend) ←
  IO.mkRef ∅

/-- Register a backend under its `name`. Raises if a backend with the
    same name is already registered: users override priority via
    `set_option lp.backend` or per-call argument, never by silently
    swapping in a different descriptor. -/
def registerBackend (b : LPBackend) : IO Unit := do
  let m ← backendRegistry.get
  if m.contains b.name then
    throw <| IO.userError s!"lp: backend '{b.name}' is already registered"
  backendRegistry.set (m.insert b.name b)

/-- Look up a backend by name. -/
def resolveBackend (name : String) : IO (Except String LPBackend) := do
  let m ← backendRegistry.get
  match m[name]? with
  | some b => pure (.ok b)
  | none =>
    let names := (m.toList.map Prod.fst).toArray.qsort (· < ·) |>.toList
    pure (.error s!"lp: no backend named '{name}' (registered: {names})")

/-- Run a backend's probe, converting any unhandled `IO` exception into
    a probe failure. A misbehaving backend cannot abort the fallback
    search; it can only fail its own probe. -/
private def safeProbe (b : LPBackend) : IO (Except String Unit) := do
  try
    b.probe
  catch e =>
    pure (.error s!"probe raised: {e}")

/-- Snapshot of registered backends, sorted by `(defaultPriority, name)`.

    The second component encodes probe state, deliberately distinct
    from "probe succeeded":

    * `none`               — probe not run (because `runProbe := false`);
    * `some (.ok ())`      — probe ran and succeeded;
    * `some (.error msg)`  — probe ran and reported `msg`.

    Fallback selection (e.g. in the tactic layer) picks the first
    backend whose entry is `some (.ok ())`. Probes have no caching:
    callers that want memoised results should wrap the result. -/
def availableBackends (runProbe : Bool := true) :
    IO (Array (LPBackend × Option (Except String Unit))) := do
  let m ← backendRegistry.get
  let sorted := (m.toList.map Prod.snd).toArray.qsort LPBackend.lt
  if runProbe then
    sorted.mapM (fun b => return (b, some (← safeProbe b)))
  else
    pure (sorted.map (fun b => (b, none)))

end Soplex.LP
