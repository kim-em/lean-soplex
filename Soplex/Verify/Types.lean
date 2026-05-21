/-
  Compatibility import for shared solver data types.

  The definitions live in `LPCore.Types` (the new `kim-em/lp-core`
  package) so the FFI binding, the verifier, and every future
  backend agree on the same `Problem`, `Solution`, and certificate
  structures without anyone depending on the FFI build.
-/

import LPCore.Types
