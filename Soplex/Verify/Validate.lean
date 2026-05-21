/-
  Compatibility import for solver input validation.

  The validators (`validate`, `validateOptions`, `validateRaw`,
  `Problem.ofRaw`) live in `LPCore.Validate` (the new
  `kim-em/lp-core` package). The verified layer builds proofs and
  certificate checks over the same normalised `Problem` values.
-/

import LPCore.Validate
