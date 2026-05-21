/-! # `lake test` driver

Runs the full test suite: the elaboration-time Lean probes and each test
executable in `SoplexTest/` are run in turn. The first non-zero exit aborts
and is propagated.

Invoked via `lake test`.
-/

def testExes : Array String := #[
  "verify-tests",
  "solve-exact-tests",
  "solve-float-tests",
  "solve-compare-tests",
  "solve-verified-tests",
  "accessor-goldens",
  "file-io-tests"
]

def leanProbes : Array String := #[
  "SoplexTest/FFIProbe.lean",
  "SoplexTest/LP.lean",
  "SoplexTest/LPExistential.lean",
  "SoplexTest/LPInnerForall.lean",
  "SoplexTest/LPMaximize.lean",
  "SoplexTest/LPBenders.lean",
  "SoplexTest/LPScaling.lean",
  "SoplexTest/ReadmeCheck.lean"
]

def binPath (name : String) : System.FilePath :=
  let exeName := if System.Platform.isWindows then name ++ ".exe" else name
  "." / ".lake" / "build" / "bin" / exeName

def dynlibFileName (libName : String) : String :=
  let name :=
    if System.Platform.isWindows then libName
    else "lib" ++ libName
  let ext :=
    if System.Platform.isOSX then "dylib"
    else if System.Platform.isWindows then "dll"
    else "so"
  s!"{name}.{ext}"

def soplexFFIDynlibPath : System.FilePath :=
  "." / ".lake" / "packages" / "SoplexFFI" / ".lake" / "build" / "lib" /
    dynlibFileName "SoplexFFI_SoplexFFI"

/-- Pure-Lean shared library hosting the `LPCore.*` modules.
    The Lean elaboration probes import `Soplex.Verify.Types` /
    `Soplex.Verify.Validate`, which re-export `LPCore.Types` /
    `LPCore.Validate`; their compiled code lives here and must be
    `--load-dynlib`'d alongside the FFI library. -/
def lpCoreDynlibPath : System.FilePath :=
  "." / ".lake" / "packages" / "LPCore" / ".lake" / "build" / "lib" /
    dynlibFileName "LPCore_LPCore"

def run (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args }
  child.wait

/-- Extra args (e.g. `-Ksanitize=1`) passed after `--` are forwarded
    to the inner `lake build` so sanitizers propagate to the test exes. -/
def main (args : List String) : IO UInt32 := do
  let buildArgs := #["build"] ++ args.toArray ++ testExes
  IO.println s!"==> lake {String.intercalate " " buildArgs.toList}"
  let buildCode ← run "lake" buildArgs
  if buildCode ≠ 0 then
    IO.eprintln s!"build failed (exit {buildCode})"
    return buildCode
  for probe in leanProbes do
    -- `--tstack=65536` (64 MB) raises the elaboration thread's stack
    -- size. The `lp` tactic's emitted certificate for the dense
    -- `LPScaling` cases recurses deeply during the `isDefEq` check of
    -- the proof term, overflowing the smaller default thread stack on
    -- Windows (~2 MB suffices to fail, ~8 MB to pass).
    let probeArgs := #[
      "env", "lean",
      "--load-dynlib", lpCoreDynlibPath.toString,
      "--load-dynlib", soplexFFIDynlibPath.toString,
      "--tstack=65536", probe
    ]
    IO.println s!"\n==> lake {String.intercalate " " probeArgs.toList}"
    let code ← run "lake" probeArgs
    if code ≠ 0 then
      IO.eprintln s!"{probe} failed (exit {code})"
      return code
  for exe in testExes do
    IO.println s!"\n==> {exe}"
    let code ← run (binPath exe).toString #[]
    if code ≠ 0 then
      IO.eprintln s!"{exe} failed (exit {code})"
      return code
  IO.println "\nAll tests passed."
  return 0
