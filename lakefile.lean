import Lake
open System Lake DSL

/-! # `Soplex` build configuration

  The direct SoPlex binding lives in the `SoplexFFI` package.
  This package builds the high-level verified API on top of it.
-/

require SoplexFFI from git "https://github.com/kim-em/soplex-ffi" @
  "058eb8ab73e866c70fa8acb9cd138049a30b25f7"

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
  globs := #[`Soplex, `Soplex.Basic, `Soplex.Verify, `Soplex.Verify.+]
  precompileModules := true
  -- Keep the native runtime link arguments on the downstream library as
  -- well as the package. `Soplex.Basic` imports and calls the FFI during
  -- elaboration-time probes, so its shared-library link step must resolve
  -- the same platform libraries as the final executables.
  moreLinkArgs := soplexFFIRuntimeLinkArgs

/-- Shared scaffolding for the `SoplexTest/` executables. Keeping it as
    a `lean_lib` lets each test exe pick up `SoplexTest.Common` and
    `SoplexTest.SolveCommon` as compiled dependencies. -/
lean_lib SoplexTest where
  roots := #[`SoplexTest.Common, `SoplexTest.SolveCommon]

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and solves a toy LP. Used by CI
    to confirm the binding links, loads, and computes on every platform. -/
lean_exe «ffi-check» where
  root := `Main

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
  root := `QuickstartExample
