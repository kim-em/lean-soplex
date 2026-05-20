/-
  Top-level entry point for the `Soplex` library.

  Bundles the verifier, the `lp` tactic, and the SoPlex FFI backend
  under a single `import Soplex` so existing callers see no change.
  The backend registry (defined in `Soplex.LP.Core`) is populated as a
  side effect of importing `Soplex.Backend.SoplexFFI`, which runs its
  `initialize` block at module-load time.

  Tracked migration: this repo will eventually be split into
  `lp-core`, `lp-verify`, `lp-tactic`, and per-backend packages; see
  https://github.com/kim-em/soplex/issues/50 for the design. Until
  then this meta-import is the seam.
-/

import Soplex.Basic
import Soplex.Tactic.LP
import Soplex.Backend.SoplexFFI
