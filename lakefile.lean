import Lake
open System Lake DSL

/-! # `lean-soplex` build configuration

  Two Lake libraries:

  * `LeanSoplexVerify` — pure-Lean certificate checker
    (`LeanSoplex.Verify` namespace). No FFI dependency, so consumers
    that only want the verifier can depend on this target alone.
  * `LeanSoplex`       — FFI bindings to SoPlex.

  A single `extern_lib leansoplex` packages SoPlex's object files
  together with the bridge's object files into one static library.
  Package-level `moreLinkArgs` adds the runtime library dependencies
  (GMP, the C++ runtime) that are not bundled in.

  Mirrors `kim-em/lean-csdp`'s pattern. Differences:

  * SoPlex is C++ (CSDP is C); bridge files are `.cpp`.
  * SoPlex is too large to compile file-by-file from Lake, and its
    build needs CMake. Lake's job system is not a comfortable home for
    multi-step out-of-tree builds, so SoPlex is built via the
    `scripts/build-soplex.sh` helper instead. Run it once before
    `lake build` (CI does this automatically). The script writes
    `.lake/build/soplex-objs/.ready` once SoPlex's object files have
    been extracted; the lakefile reads that directory at build time.
-/

/-! ## Platform-specific link arguments. -/

/-- Path to the macOS Command Line Tools SDK. Hard-coded for the same
    reason as in `lean-csdp`: Lake's configuration phase has no clean
    way to call `xcrun` at load time, and the CLT SDK is the most
    universally available path across user machines and CI runners. -/
def macSdkPath : String :=
  "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk"

/-- Linker arguments for SoPlex's runtime library dependencies.

    * SoPlex itself is built into the combined static library by the
      `extern_lib leansoplex` rule below, so it does not appear here.
    * GMP (with the `libgmpxx` C++ wrappers) is required for exact-
      rational arithmetic and is dynamically linked.
    * `-lstdc++` / `-lc++` pulls in the C++ runtime. Lean's linker
      driver (`clang`) does not infer that from the presence of `.cpp`
      objects, so we add it explicitly.
    * macOS: route the linker at the Command Line Tools SDK so the
      `--sysroot` Lake sets does not hide the system libraries.
    * Windows (MSYS2 / mingw-w64): GMP / runtime libs are staged into
      `vendor/mingw-libs/` by CI; `-L` points there as well as the
      standard MSYS2 install path. -/
def soplexRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[s!"-Wl,-syslibroot,{macSdkPath}",
      "-L/opt/homebrew/lib",
      "-L/usr/local/lib",
      "-lgmpxx", "-lgmp",
      "-lc++"]
  else if System.Platform.isWindows then
    #["-Lvendor/mingw-libs",
      "-LC:/msys64/mingw64/lib",
      "-lgmpxx", "-lgmp",
      "-lstdc++"]
  else
    -- Linux is a tricky case: SoPlex is compiled by the system g++
    -- (libstdc++), so the SoPlex objects pull in libstdc++ symbols.
    -- Lean's bundled clang, however, links the resulting `.so` with a
    -- `NEEDED libc++.so.1` entry (from its own runtime dependencies),
    -- so libc++ must also be present at *load* time. We resolve
    -- SoPlex's C++ symbols via `-l:libstdc++.so.6` (the versioned
    -- SONAME, so linking does not depend on a `libstdc++.so` symlink
    -- which Ubuntu base images typically omit); the CI workflow
    -- additionally installs `libc++1` so the load-time lookup succeeds.
    #["-L/usr/lib/x86_64-linux-gnu",
      "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64",
      "-L/usr/lib",
      "-lgmpxx", "-lgmp",
      "-l:libstdc++.so.6", "-lm"]

package leanSoplex where
  moreLinkArgs := soplexRuntimeLinkArgs

/-! ## SoPlex object discovery.

  The `scripts/build-soplex.sh` helper writes extracted object files
  to `.lake/build/soplex-objs/` and a marker file at
  `.lake/build/soplex-objs/.ready`. We list those at extern_lib
  build time and feed them to `buildStaticLib` alongside the bridge
  object files. -/

def soplexObjsDir (pkgDir : FilePath) : FilePath :=
  pkgDir / defaultBuildDir / "soplex-objs"

def soplexBuildDir (pkgDir : FilePath) : FilePath := pkgDir / "build-soplex"

/-- List of SoPlex object files extracted by `scripts/build-soplex.sh`.
    Errors with a clear message if the script has not been run.
    Runs at extern_lib build time (inside a Lake build action). -/
def listSoplexObjs (pkgDir : FilePath) : IO (Array FilePath) := do
  let dir := soplexObjsDir pkgDir
  let marker := dir / ".ready"
  if !(← marker.pathExists) then
    throw <| IO.userError <|
      s!"SoPlex objects not found at {dir}.\n" ++
      "Run `./scripts/build-soplex.sh` from the repo root once before `lake build`."
  let entries ← dir.readDir
  let mut out : Array FilePath := #[]
  for e in entries do
    let n := e.fileName
    if n.endsWith ".o" || n.endsWith ".obj" then
      out := out.push e.path
  pure out

/-! ## Bridge object compilation. -/

def bridgeSrcs : Array String := #["lean_soplex.cpp", "lean_soplex_bridge.cpp"]

/-- Extra `-I` paths for finding Boost (header-only multi-precision
    bits SoPlex pulls in) and GMP. Locations differ per platform:
    Homebrew on macOS, the standard `/usr/include` on Linux, MSYS2's
    `/mingw64/include` on Windows. -/
def systemIncludeArgs : Array String :=
  if System.Platform.isOSX then
    #["-I/opt/homebrew/include", "-I/usr/local/include"]
  else if System.Platform.isWindows then
    #["-IC:/msys64/mingw64/include"]
  else
    #["-I/usr/include"]

private def bridgeOTarget (pkg : Package) (src : String) :
    FetchM (Job FilePath) := do
  let stem := src.dropEnd 4  -- drop `.cpp`
  let oFile := pkg.dir / defaultBuildDir / "ffi" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "ffi" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let leanInc        := (← getLeanIncludeDir).toString
    let ffiInc         := (pkg.dir / "ffi").toString
    let soplexSrcInc   := (pkg.dir / "soplex" / "src").toString
    -- CMake generates `soplex/config.h` under the build dir.
    let soplexBuildInc := (soplexBuildDir pkg.dir).toString
    compileO oFile srcFile (#[
      "-O2", "-fPIC", "-std=c++17",
      "-I", leanInc,
      "-I", ffiInc,
      "-I", soplexSrcInc,
      "-I", soplexBuildInc
    ] ++ systemIncludeArgs) "c++"

/-! ## Combined static library. -/

extern_lib leansoplex (pkg) := do
  let name := nameToStaticLib "leansoplex"
  let outLib := pkg.staticLibDir / name
  -- Read SoPlex objects synchronously at FetchM time. `Job.pure` lifts
  -- each path into a trivial completed Job so `buildStaticLib` can
  -- consume them alongside the bridge .o jobs.
  let soplexOs ← listSoplexObjs pkg.dir
  let soplexOJobs : Array (Job FilePath) := soplexOs.map Job.pure
  let bridgeOJobs ← bridgeSrcs.mapM (bridgeOTarget pkg)
  buildStaticLib outLib (soplexOJobs ++ bridgeOJobs)

/-! ## Lean libraries and executables. -/

/-- Pure-Lean verifier. No FFI dependency. Consumers that only want
    the checker can depend on `LeanSoplexVerify` alone. -/
lean_lib LeanSoplexVerify where
  roots := #[`LeanSoplex.Verify]

/-- FFI binding. The `extern_lib leansoplex` produced above is linked
    automatically. -/
@[default_target]
lean_lib LeanSoplex where
  precompileModules := true
  moreLinkArgs := soplexRuntimeLinkArgs

lean_exe «soplex-smoke» where
  root := `Main
  moreLinkArgs := soplexRuntimeLinkArgs

/-- Hand-rolled tests for the pure-Lean certificate checker.
    `VerifyTests.lean` only imports `LeanSoplex.Verify`, but Lake
    auto-links the package-level `extern_lib leansoplex` against every
    exe in the package, so building `verify-tests` still transitively
    triggers the SoPlex build + the bridge `.o` compile + the DLL
    link. The `moreLinkArgs := #[]` override clears the GMP / C++
    runtime args; the DLL itself still has to link successfully. -/
lean_exe «verify-tests» where
  root := `VerifyTests
  moreLinkArgs := #[]
