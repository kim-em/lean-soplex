/-
  `LPBackend` adapter for the SoPlex FFI binding.

  Wraps the synchronous `SoplexFFI.solveExact` into the abstract
  `LPBackend` interface defined in `Soplex.LP.Core`, and registers
  itself with the process-global backend registry on import. Once
  the package split (#50) lands, this module moves to the standalone
  `lp-backend-soplex-ffi` package; until then it lives here.
-/

import Soplex.LP.Core
import SoplexFFI.Basic

namespace Soplex.Backend.SoplexFFI

open Soplex Soplex.LP

/-- The FFI-backed backend. Synchronous `Except` lifted into `IO` via
    `pure`; the wrapped call already runs the FFI on the calling
    thread. Registered under priority `10` (FFI band). -/
def backend : LPBackend where
  name := "soplex-ffi"
  defaultPriority := 10
  solveExact opts p := pure (Soplex.solveExact opts p)
  -- Linking succeeded at build time and dynamic loading is exercised
  -- elsewhere (`ffi-check`); if either fails the user sees a load-time
  -- error long before the probe runs. The probe stays trivially `.ok`.
  probe := pure (.ok ())

/-- Self-register on import. Throws on duplicate registration, which
    only happens if a caller already manually registered a backend
    under the name `"soplex-ffi"` before this module loaded. -/
initialize registerBackend backend

end Soplex.Backend.SoplexFFI
