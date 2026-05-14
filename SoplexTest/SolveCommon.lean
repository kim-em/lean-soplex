/-
  Shared scaffolding for the SoPlex-backed tests. Pulls in `Soplex`;
  pure-verifier tests stay on `SoplexTest.Common` alone.
-/

import SoplexTest.Common
import Soplex

namespace SoplexTest

open Soplex

/-- Solver options used by every backed-by-SoPlex test in this suite:
    presolve off (so the exact certificate is against the original LP),
    non-verbose, no precision boost. -/
def noPresolve : Options :=
  { ({} : Options) with presolve := false, verbose := false, precisionBoost := false }

end SoplexTest
