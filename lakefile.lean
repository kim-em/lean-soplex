import Lake
open Lake DSL

/-! # `lean-soplex` build configuration

  The direct SoPlex binding lives in the local `soplex-ffi` package.
  This package builds the high-level verified API on top of it.
-/

require soplexFfi from "./soplex-ffi"

package leanSoplex

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
