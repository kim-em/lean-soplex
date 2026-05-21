/-
  Compatibility re-export of `LPTactic.Basic` (the verified-solve
  drivers `solveVerified` and `solveVerifiedWith`) and
  `SoplexFFI.Basic` (the direct FFI wrappers `solveExact`,
  `solveFloat`, `readMps`, `readLp` that the test suite calls
  through `import Soplex`).

  All declarations remain in `namespace Soplex`, so consumers writing
  `Soplex.solveVerified`, `Soplex.solveExact`, etc. keep working
  unchanged.
-/

import LPTactic.Basic
import SoplexFFI.Basic
