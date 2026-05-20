/-
  End-to-end FFI runtime check.

  Prints `SOPLEX_VERSION`, runs a cross-stdlib C++ throw/catch round
  trip on non-macOS (libstdc++ vs libc++ mismatches otherwise corrupt
  exception handling silently), and runs a small LP sanity check via
  `ffiCheckSolve`.
  Exits 0 on success; non-zero (1/2/3) tags which step failed.
-/

import Soplex

open Soplex

def main : IO UInt32 := do
  IO.println s!"SoPlex version: {Soplex.version}"

  -- Cross-stdlib ABI check. SoPlex + the FFI layer compile against
  -- libstdc++ on Linux and Windows but Lean's clang has its own
  -- opinions about the C++ runtime; if those ever desynchronise,
  -- throws stop matching catch handlers and silently terminate the
  -- process. Skipped on macOS where the whole toolchain uses libc++.
  unless System.Platform.isOSX do
    let exnRc := Soplex.exceptionCheck ()
    IO.println s!"exception check = {exnRc}"
    if exnRc ≠ 0 then
      IO.eprintln s!"std::exception throw/catch broken (rc={exnRc}); cross-stdlib ABI mismatch"
      return 3

  let result := ffiCheckSolve
    (c    := #[1.0, 1.0])
    (b    := #[1.0])
    (rows := #[0, 0])
    (cols := #[0, 1])
    (vals := #[1.0, 1.0])

  IO.println s!"ret    = {result.ret}"
  IO.println s!"obj    = {result.obj}"
  IO.println s!"primal = {result.primal.toList}"

  if result.ret ≠ 0 then
    IO.eprintln s!"expected optimal (ret=0), got ret={result.ret}"
    return 1
  -- Objective is `1` up to floating-point slop.
  if (result.obj - 1.0).abs > 1e-9 then
    IO.eprintln s!"expected objective ≈ 1.0, got {result.obj}"
    return 2
  return 0
