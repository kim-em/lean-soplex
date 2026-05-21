/-
  Compatibility re-export of the verified-solve drivers and direct
  FFI wrappers.

  `Soplex.solveVerifiedWith` (backend-pluggable, `IO`-typed) comes
  from `LPTactic.Basic`; `Soplex.solveVerified` (FFI-specialised,
  `Except`-typed) comes from `LPBackendSoplexFFI`. `SoplexFFI.Basic`
  is re-exported for the test suite's direct `Soplex.solveExact`,
  `Soplex.solveFloat`, `Soplex.readMps`, `Soplex.readLp` calls.

  All declarations remain in `namespace Soplex`, so consumers writing
  `Soplex.solveVerified`, `Soplex.solveExact`, etc. keep working
  unchanged.
-/

import LPTactic.Basic
import LPBackendSoplexFFI
import SoplexFFI.Basic
