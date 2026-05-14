import Soplex
import Lean

open Soplex Lean Lean.Elab.Tactic

elab "ffi_probe" : tactic => do
  let lp : Problem 3 2 :=
    { c         := #v[3, 5]
      a         := #[(0, 0, 1), (1, 1, 2), (2, 0, 3), (2, 1, 2)]
      rowBounds := #v[(none, some 4), (none, some 12), (none, some 18)]
      colBounds := #v[(some 0, none), (some 0, none)] }
  match solveVerified (opts := { sense := .maximize }) lp with
  | .error e => throwError s!"FFI probe: solveVerified returned error: {repr e}"
  | .ok r =>
    match r.verified with
    | .optimal x _ =>
      unless x.toArray == #[2, 6] do
        throwError s!"FFI probe: unexpected optimum {repr x.toArray} (expected #[2, 6])"
      logInfo s!"FFI probe OK: optimal x = {repr x.toArray}"
    | .infeasible _ =>
      throwError "FFI probe: expected .optimal, got .infeasible"
    | .unbounded .. =>
      throwError "FFI probe: expected .optimal, got .unbounded"
    | .unchecked status =>
      throwError s!"FFI probe: expected .optimal, got .unchecked {repr status}"

example : True := by
  ffi_probe
  trivial
