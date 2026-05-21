/-
  Compatibility re-export of `LPBackendSoplexFFI.Adapter`
  (`kim-em/lp-backend-soplex-ffi`).

  The adapter self-registers on import — anyone writing
  `import Soplex` (which transitively imports this module) gets the
  `"soplex-ffi"` backend installed in the registry at priority 10.
-/

import LPBackendSoplexFFI.Adapter
