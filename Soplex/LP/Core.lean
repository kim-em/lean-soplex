/-
  Backend-agnostic core for the SoPlex verifier and the `lp` tactic.

  The `LPBackend` record and the LP type vocabulary live in
  `kim-em/lp-core` (`LPCore.Types`, `LPCore.Backend`); this module
  re-exports them and adds the process-global registry that the
  tactic layer consults.

  Tracked migration: the registry itself will move into the future
  `kim-em/lp-tactic` package in step 2 of
  https://github.com/kim-em/soplex/issues/50, leaving this module
  as a pure re-export shim.
-/

import LPCore.Backend
import Std.Data.HashMap

open Std

namespace Soplex.LP

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
