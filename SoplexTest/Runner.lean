/-! # `lake test` driver

Runs the full test suite: each test executable in `SoplexTest/` is built
and run in turn. The first non-zero exit aborts and is propagated.

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

def binPath (name : String) : System.FilePath :=
  let exeName := if System.Platform.isWindows then name ++ ".exe" else name
  "." / ".lake" / "build" / "bin" / exeName

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
  for exe in testExes do
    IO.println s!"\n==> {exe}"
    let code ← run (binPath exe).toString #[]
    if code ≠ 0 then
      IO.eprintln s!"{exe} failed (exit {code})"
      return code
  IO.println "\nAll tests passed."
  return 0
