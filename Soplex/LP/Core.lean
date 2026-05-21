/-
  Compatibility re-export of the `LPBackend` record (from
  `kim-em/lp-core`) and the process-global registry (from
  `kim-em/lp-tactic`).

  Pre-split, this module owned both the record definition and the
  registry. Per the issue #50 non-goal "global registry state lives
  in the tactic layer", the registry now lives in `LPTactic.Registry`
  while the abstract record stays in `LPCore.Backend`. Both are
  re-exported here so any consumer writing
  `Soplex.LP.LPBackend` / `Soplex.LP.registerBackend` /
  `Soplex.LP.resolveBackend` / `Soplex.LP.availableBackends` keeps
  working unchanged.
-/

import LPCore.Backend
import LPTactic.Registry
