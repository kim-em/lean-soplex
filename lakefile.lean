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

/-! ## Sanitizer (ASan/UBSan) opt-in.

    Pass `-Ksanitize=1` (any value, even empty) on the `lake` command
    line — i.e. `lake build -Ksanitize=1 …` — to compile the bridge
    `.o` files and link the executables under
    `-fsanitize=address,undefined`.  The companion
    `scripts/build-soplex.sh` reads `LEAN_SOPLEX_SANITIZE` from the
    environment to instrument SoPlex's own object files; the CI job
    `linux-asan` sets both consistently.

    Lean's bundled clang ships without compiler-rt's sanitizer
    runtime archives, so the final link will fail with
    `cannot open libclang_rt.asan_static.a` until you run
    `./scripts/install-sanitizer-runtime.sh` once. That helper
    detects which clang version Lean bundles, installs a matching
    upstream LLVM toolchain from apt.llvm.org, and symlinks the
    runtime archives into the path Lean's clang searches.

    Linux/clang only — macOS and Windows runners do not exercise this
    path, and the flag list below assumes clang's sanitizer drivers. -/
/-- Treats `-Ksanitize=0` / `-Ksanitize=false` as off so the flag matches
    the `LEAN_SOPLEX_SANITIZE` env var's semantics. Any other value
    (including the bare `-Ksanitize`) enables sanitizers. -/
def sanitizerEnabled : Bool :=
  match get_config? sanitize with
  | some s => s != "0" && s != "false"
  | none => false

def sanitizerArgs : Array String :=
  if sanitizerEnabled then
    -- Disable ubsan's `vptr` / `function` sub-checks: they require
    -- C++ RTTI runtime support (`__ubsan_vptr_type_cache`,
    -- `__ubsan_handle_function_type_mismatch`) that is not pulled
    -- in cleanly when Lean's bundled clang is the linker driver.
    -- The rest of `-fsanitize=undefined` — integer overflow,
    -- alignment, bounds, shift, etc. — stays active.
    #["-fsanitize=address", "-fsanitize=undefined",
      "-fno-sanitize=vptr,function",
      "-fno-omit-frame-pointer", "-g"]
  else
    #[]

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
    -- Tested on MSYS2 MINGW64 with `mingw-w64-x86_64-gcc` (modern: GCC
    -- 16). CLANG64 / UCRT64 / non-MSYS2 mingw installs are not exercised
    -- in CI and likely need different archives. Run
    -- `scripts/stage-mingw-libs.sh` from an MSYS2 MINGW64 shell before
    -- `lake build` to populate `vendor/mingw-libs/`; the script verifies
    -- the archives this lakefile references by relative path are
    -- actually present.
    --
    -- SoPlex's pre-built `.o` files (compiled by mingw's `g++`) and our
    -- bridge `.o` (compiled by Lake's `c++`, also mingw `g++`) both
    -- emit libstdc++-mangled symbols. The `libstdc++.dll.a` *import lib*
    -- carries pre-cxx11-ABI imports only, so the C++11-ABI symbols
    -- SoPlex uses (`std::__cxx11::basic_string<…>` and friends) are
    -- never satisfied by `-lstdc++`. We therefore pass the *static*
    -- archive `libstdc++.a` directly by relative path — this avoids
    -- any ambiguity with `-Wl,-Bstatic` and any reordering Lake may
    -- do, and the static archive contains the full C++11 ABI. Same
    -- trick for `libgmpxx.a` / `libgmp.a`. `libgcc_s` and `msvcrt` (the
    -- latter for `__declspec(dllimport) _vsnprintf`) stay dynamic.
    --
    -- Lean's `clang.exe` on Windows auto-links `libc++.a` regardless
    -- of `-stdlib=libstdc++` or `-nostdlib++` flags (it's in MSVC-style
    -- mode where those driver flags are reported "unused"). Both
    -- libc++ and our explicit libstdc++ define every C++ standard
    -- exception type, so the link fails with duplicate symbols.
    --
    -- `--allow-multiple-definition` is a pragmatic hack: lld picks
    -- whichever definition it sees first. Our explicit `libstdc++.a`
    -- comes first, so libstdc++ wins and libc++'s definitions are
    -- dropped on the floor. This means the *order* of entries in the
    -- array below is load-bearing — if Lake or Lean ever reorder
    -- libraries so libc++ wins, exception throw/catch will break at
    -- runtime. `Main.lean` calls `LeanSoplex.exceptionCheck` (which
    -- throws `std::runtime_error`, catches via `std::exception &`,
    -- and validates `what()`) before the toy LP solve, so a wrong
    -- C++ ABI shows up as a CI failure rather than a silently
    -- corrupted DLL.
    --
    -- A cleaner long-term fix is to compile SoPlex with libc++ from
    -- the start, so the entire DLL uses one C++ ABI.
    #["-Wl,--allow-multiple-definition",
      "vendor/mingw-libs/libstdc++.a",
      "vendor/mingw-libs/libgmpxx.a",
      "vendor/mingw-libs/libgmp.a",
      "-Lvendor/mingw-libs",
      "-lgcc_s",
      "-lmingwex",     -- C99 wrappers; provides `_vsnprintf` etc.
      "-lmsvcrt"]
  else
    -- SoPlex and the bridge are built with `clang++ -stdlib=libc++`
    -- (see `bridgeCxxDriver` / `bridgeStdlibArgs` and the matching
    -- override in `scripts/build-soplex.sh`), so the C++ runtime is
    -- libc++ end-to-end and matches the libc++abi.a Lake's link
    -- template statically pulls from Lean's bundled toolchain.
    #["-L/usr/lib/x86_64-linux-gnu",
      "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64",
      "-L/usr/lib",
      "-lgmpxx", "-lgmp",
      "-lm"] ++ sanitizerArgs

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

/-- Compiler driver for the bridge `.cpp` files. Lake's link template on
    Linux statically pulls libc++abi.a from Lean's bundled toolchain, so
    the bridge must compile against libc++ as well to keep typeinfo and
    personality functions on a single C++ runtime. macOS already uses
    libc++ end-to-end; Windows uses mingw g++ paired with libstdc++. -/
def bridgeCxxDriver : String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then "c++" else "clang++"

/-- Linux-only compile flags for the bridge: select libc++ as the C++
    standard library to match Lake's link-time libc++abi.a. Empty on
    macOS (libc++ is the default) and Windows (libstdc++). -/
def bridgeStdlibArgs : Array String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then #[]
  else #["-stdlib=libc++"]

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
    ] ++ bridgeStdlibArgs ++ systemIncludeArgs ++ sanitizerArgs) bridgeCxxDriver

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
    automatically.

    `precompileModules` is disabled under `-Ksanitize=1` because the
    asan-instrumented `libleansoplex.so` would be `dlopen`-ed by an
    *un*-instrumented `lean` host process during compilation, which
    fails with `undefined symbol: __asan_init`.  With precompile off,
    modules compile to `.olean` only and the bridge `.o` files get
    linked directly into each `lean_exe` at exe-link time — where
    `sanitizerArgs` already pull in the static asan runtime. -/
@[default_target]
lean_lib LeanSoplex where
  precompileModules := !sanitizerEnabled
  moreLinkArgs := soplexRuntimeLinkArgs

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and solves a toy LP. Used by CI
    to confirm the binding links, loads, and computes on every platform. -/
lean_exe «ffi-check» where
  root := `Main
  moreLinkArgs := soplexRuntimeLinkArgs

/-- Hand-rolled tests for the pure-Lean certificate checker.
    `VerifyTests.lean` only imports `LeanSoplex.Verify`, but Lake
    auto-links the package-level `extern_lib leansoplex` against every
    exe in the package, so building `verify-tests` still transitively
    triggers the SoPlex build + the bridge `.o` compile + the DLL
    link. Lake concatenates the package's `moreLinkArgs` with the exe's,
    so the package-level GMP / C++ runtime args (and the
    `-Ksanitize=1`-controlled sanitizer args appended to them on Linux)
    apply to this exe too; the empty array here adds nothing further. -/
lean_exe «verify-tests» where
  root := `VerifyTests
  moreLinkArgs := #[]

lean_exe «solve-exact-tests» where
  root := `SolveExactTests
  moreLinkArgs := soplexRuntimeLinkArgs

lean_exe «solve-float-tests» where
  root := `SolveFloatTests
  moreLinkArgs := soplexRuntimeLinkArgs

lean_exe «solve-verified-tests» where
  root := `SolveVerifiedTests
  moreLinkArgs := soplexRuntimeLinkArgs

/-- One LP per row-sense × column-status × objective-sense cell;
    pins down the SoPlex accessor → `DualBundle` translation for the
    pinned SoPlex release. See `docs/accessors.md`. -/
lean_exe «accessor-goldens» where
  root := `AccessorGoldens
  moreLinkArgs := soplexRuntimeLinkArgs

lean_exe «file-io-tests» where
  root := `FileIoTests
  moreLinkArgs := soplexRuntimeLinkArgs

lean_exe «solve-compare-tests» where
  root := `SolveCompareTests
  moreLinkArgs := soplexRuntimeLinkArgs
