import Lake
open System Lake DSL

/-! # `soplex-ffi` build configuration

  This package owns the direct SoPlex binding: the vendored SoPlex
  build, the C++ bridge, and the thin Lean API in `SoplexFFI`.
-/

def macSdkPath : String :=
  "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk"

def packageRoot : FilePath := __dir__

/-! ## Sanitizer (ASan/UBSan) opt-in.

    Pass `-Ksanitize=1` to `lake build` and set
    `LEAN_SOPLEX_SANITIZE=1` when running `scripts/build-soplex.sh` to
    instrument SoPlex, the bridge, and final executables consistently.
-/
def sanitizerEnabled : Bool :=
  match get_config? sanitize with
  | some s => s != "0" && s != "false"
  | none => false

def sanitizerArgs : Array String :=
  if sanitizerEnabled then
    #["-fsanitize=address", "-fsanitize=undefined",
      "-fno-sanitize=vptr,function",
      "-fno-omit-frame-pointer", "-g"]
  else
    #[]

def soplexRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[s!"-Wl,-syslibroot,{macSdkPath}",
      "-L/opt/homebrew/lib",
      "-L/usr/local/lib",
      "-lgmpxx", "-lgmp",
      "-lc++"]
  else if System.Platform.isWindows then
    let mingwLibDir := packageRoot / "vendor" / "mingw-libs"
    #["-Wl,--allow-multiple-definition",
      (mingwLibDir / "libstdc++.a").toString,
      (mingwLibDir / "libgmpxx.a").toString,
      (mingwLibDir / "libgmp.a").toString,
      s!"-L{mingwLibDir}",
      "-lgcc_s",
      "-lmingwex",
      "-lmsvcrt"]
  else
    #["-L/usr/lib/x86_64-linux-gnu",
      "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64",
      "-L/usr/lib",
      "-lgmpxx", "-lgmp",
      "-lm"] ++ sanitizerArgs

package soplexFfi where
  moreLinkArgs := soplexRuntimeLinkArgs

def soplexObjsDir (pkgDir : FilePath) : FilePath :=
  pkgDir / defaultBuildDir / "soplex-objs"

def soplexBuildDir (pkgDir : FilePath) : FilePath := pkgDir / "build-soplex"

def listSoplexObjs (pkgDir : FilePath) : IO (Array FilePath) := do
  let dir := soplexObjsDir pkgDir
  let marker := dir / ".ready"
  if !(← marker.pathExists) then
    throw <| IO.userError <|
      s!"SoPlex objects not found at {dir}.\n" ++
      "Run `./soplex-ffi/scripts/build-soplex.sh` from the repo root once before `lake build`."
  let entries ← dir.readDir
  let mut out : Array FilePath := #[]
  for e in entries do
    let n := e.fileName
    if n.endsWith ".o" || n.endsWith ".obj" then
      out := out.push e.path
  pure out

def bridgeSrcs : Array String := #["lean_soplex.cpp", "lean_soplex_bridge.cpp"]

def systemIncludeArgs : Array String :=
  if System.Platform.isOSX then
    #["-I/opt/homebrew/include", "-I/usr/local/include"]
  else if System.Platform.isWindows then
    #["-IC:/msys64/mingw64/include"]
  else
    #["-I/usr/include"]

def bridgeCxxDriver : String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then "c++" else "clang++"

def bridgeStdlibArgs : Array String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then #[]
  else #["-stdlib=libc++"]

private def bridgeOTarget (pkg : Package) (src : String) :
    FetchM (Job FilePath) := do
  let stem := src.dropEnd 4
  let oFile := pkg.dir / defaultBuildDir / "ffi" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "ffi" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let leanInc        := (← getLeanIncludeDir).toString
    let ffiInc         := (pkg.dir / "ffi").toString
    let soplexSrcInc   := (pkg.dir / "vendor" / "soplex" / "src").toString
    let soplexBuildInc := (soplexBuildDir pkg.dir).toString
    compileO oFile srcFile (#[
      "-O2", "-fPIC", "-std=c++17",
      "-I", leanInc,
      "-I", ffiInc,
      "-I", soplexSrcInc,
      "-I", soplexBuildInc
    ] ++ bridgeStdlibArgs ++ systemIncludeArgs ++ sanitizerArgs) bridgeCxxDriver

extern_lib soplexffi (pkg) := do
  let name := nameToStaticLib "soplexffi"
  let outLib := pkg.staticLibDir / name
  let soplexOs ← listSoplexObjs pkg.dir
  let soplexOJobs : Array (Job FilePath) := soplexOs.map Job.pure
  let bridgeOJobs ← bridgeSrcs.mapM (bridgeOTarget pkg)
  buildStaticLib outLib (soplexOJobs ++ bridgeOJobs)

@[default_target]
lean_lib SoplexFFI where
  roots := #[`SoplexFFI]
  globs := #[`SoplexFFI, `SoplexFFI.Basic, `SoplexFFI.Types, `SoplexFFI.Validate]
  precompileModules := !sanitizerEnabled
  moreLinkArgs := soplexRuntimeLinkArgs
