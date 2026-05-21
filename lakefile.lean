import Lake
open System Lake DSL

/-! # `Soplex` build configuration

  The direct SoPlex binding lives in the `SoplexFFI` package.
  This package builds the high-level verified API on top of it.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "60fca2313ea3be14f578258dc6390f2fa07b26e7"

require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "3726846a10bb875d133a52a2c4b137da2806e22e"

require SoplexFFI from git "https://github.com/kim-em/soplex-ffi" @
  "a1389a99c2345f9d72ffdc2941be350ad0f97fd7"

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

def soplexFFIRoot : FilePath := __dir__ / defaultPackagesDir / "SoplexFFI"

def soplexFFIRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[]
  else if System.Platform.isWindows then
    let mingwLibDir := soplexFFIRoot / "vendor" / "mingw-libs"
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
      "-L/usr/lib"] ++ sanitizerArgs

package Soplex where
  moreLinkArgs := soplexFFIRuntimeLinkArgs

@[default_target]
lean_lib Soplex where
  roots := #[`Soplex]
  globs := #[`Soplex, `Soplex.Basic, `Soplex.Verify, `Soplex.Verify.+,
             `Soplex.LP.Core, `Soplex.Backend.SoplexFFI]
  precompileModules := true
  -- Keep the native runtime link arguments on the downstream library as
  -- well as the package. `Soplex.Basic` imports and calls the FFI during
  -- elaboration-time probes, so its shared-library link step must resolve
  -- the same platform libraries as the final executables.
  moreLinkArgs := soplexFFIRuntimeLinkArgs
  -- Force the `SoplexFFI` native library to build before any module in
  -- this library. With `precompileModules`, every module's `:dynlib`
  -- link picks up `moreLinkArgs`, which on Windows names the staged
  -- `vendor/mingw-libs/*.a` archives. Those archives are staged as a
  -- side effect of the `SoplexFFI` native build. Pure-Lean modules such
  -- as `Soplex.Tactic.*` import nothing from `SoplexFFI`, so
  -- without this dependency their dynlib link can run first and fail
  -- with `no such file or directory` on the not-yet-staged archives.
  needs := #[BuildKey.packageTarget `SoplexFFI `soplexffi]

/-- Shared scaffolding for the `SoplexTest/` executables. Keeping it as
    a `lean_lib` lets each test exe pick up `SoplexTest.Common` and
    `SoplexTest.SolveCommon` as compiled dependencies. -/
lean_lib SoplexTest where
  roots := #[`SoplexTest.Common, `SoplexTest.SolveCommon]

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and runs a small LP sanity check.
    Used by CI to confirm the binding links, loads, and computes on every
    platform. -/
lean_exe «ffi-check» where
  root := `SoplexTest.FFICheck

lean_exe «verify-tests» where
  root := `SoplexTest.Verify

lean_exe «solve-exact-tests» where
  root := `SoplexTest.SolveExact

lean_exe «solve-float-tests» where
  root := `SoplexTest.SolveFloat

lean_exe «solve-compare-tests» where
  root := `SoplexTest.SolveCompare

lean_exe «solve-verified-tests» where
  root := `SoplexTest.SolveVerified

lean_exe «accessor-goldens» where
  root := `SoplexTest.AccessorGoldens

lean_exe «file-io-tests» where
  root := `SoplexTest.FileIo

/-- `lake test` driver: builds and runs every test executable. -/
@[test_driver]
lean_exe «test-runner» where
  root := `SoplexTest.Runner

lean_exe «quickstart-example» where
  root := `Examples.Quickstart
