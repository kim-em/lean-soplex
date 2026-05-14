import Lake
open System Lake DSL

/-! # `Soplex` build configuration

  The direct SoPlex binding lives in the `SoplexFFI` package.
  This package builds the high-level verified API on top of it.
-/

require SoplexFFI from git "https://github.com/kim-em/soplex-ffi" @ "main"

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

def soplexFfiRoot : FilePath := __dir__ / defaultPackagesDir / "SoplexFFI"

def soplexFfiRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[]
  else if System.Platform.isWindows then
    let mingwLibDir := soplexFfiRoot / "vendor" / "mingw-libs"
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
  moreLinkArgs := soplexFfiRuntimeLinkArgs

@[default_target]
lean_lib Soplex where
  roots := #[`Soplex]
  globs := #[`Soplex, `Soplex.Basic, `Soplex.Verify, `Soplex.Verify.+]
  precompileModules := true

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and solves a toy LP. Used by CI
    to confirm the binding links, loads, and computes on every platform. -/
lean_exe «ffi-check» where
  root := `Main

lean_exe «verify-tests» where
  root := `VerifyTests

lean_exe «solve-exact-tests» where
  root := `SolveExactTests

lean_exe «solve-float-tests» where
  root := `SolveFloatTests

lean_exe «solve-compare-tests» where
  root := `SolveCompareTests

lean_exe «solve-verified-tests» where
  root := `SolveVerifiedTests

lean_exe «accessor-goldens» where
  root := `AccessorGoldens

lean_exe «file-io-tests» where
  root := `FileIoTests
