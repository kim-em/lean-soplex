/-
  Minimal v0 surface for `lean-soplex`.

  This file currently exposes two FFI entry points:

  * `version` — returns SoPlex's compile-time version macro. Exists to
    confirm the FFI is linked and the SoPlex headers used at build time
    match the runtime.

  * `smokeSolve` — solves a small equality-constrained LP in floating-
    point mode. Used as the cross-platform CI build verifier; it exercises
    SoPlex's constructors, parameter setting, column / row builders, the
    solver loop, and result extraction in a single call.

  The real exact-mode API (`solveExact`, `solveFloat`, file I/O, the
  certificate types) lands in subsequent commits per `PLAN.md`.
-/

namespace LeanSoplex

/-- SoPlex's compile-time `SOPLEX_VERSION` macro, e.g. `802` for v8.0.2. -/
@[extern "lean_soplex_version_ffi"]
opaque versionImpl : Unit → UInt32

/-- SoPlex's compile-time `SOPLEX_VERSION` macro, e.g. `802` for v8.0.2. -/
def version : UInt32 := versionImpl ()

/-- Cross-stdlib ABI self-test: throws a `std::runtime_error` in C++,
    catches via the `std::exception` base, verifies `what()` survives.
    Returns `0` on success.

    Exposed as a `Unit → UInt32` function rather than a `UInt32` value
    so the call is deferred to invocation time. A bare `def : UInt32 :=
    exceptionCheckImpl ()` would be evaluated at module load — i.e.
    inside `lean` while it elaborates any module that imports this one,
    which would crash the compiler if the throw/catch ABI is broken,
    rather than surfacing as a clean executable-level failure.

    Run from `Main.lean` on every non-macOS platform as a cross-stdlib
    ABI canary; see the Linux / Windows branches of `soplexRuntimeLinkArgs`
    in `lakefile.lean` for the link-time arrangements this validates. -/
@[extern "lean_soplex_exception_check_ffi"]
opaque exceptionCheck : Unit → UInt32

/-- Result of `smokeSolve`. `ret` follows the bridge convention:
    `0` = optimal, `1` = infeasible, `2` = unbounded, anything else is an
    FFI / SoPlex error. -/
structure SmokeResult where
  /-- Primal solution (length = `numVars`). Meaningful iff `ret = 0`. -/
  primal : FloatArray
  /-- Return code; see structure docstring. -/
  ret    : UInt32
  /-- Objective value; meaningful iff `ret = 0`. -/
  obj    : Float
deriving Inhabited

@[extern "lean_soplex_smoke_solve_ffi"]
private opaque smokeSolveImpl
    (c : @& FloatArray) (b : @& FloatArray)
    (aRows : @& ByteArray) (aCols : @& ByteArray) (aVals : @& FloatArray) :
    SmokeResult

/-- Pack a `UInt32` little-endian onto a `ByteArray`. -/
@[inline] private def pushU32LE (bs : ByteArray) (u : UInt32) : ByteArray :=
  bs.push (u &&& 0xff).toUInt8
    |>.push ((u >>> 8) &&& 0xff).toUInt8
    |>.push ((u >>> 16) &&& 0xff).toUInt8
    |>.push ((u >>> 24) &&& 0xff).toUInt8

private def packUInt32Array (xs : Array UInt32) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for x in xs do bs := pushU32LE bs x
  return bs

private def floatArrayOfArray (xs : Array Float) : FloatArray := Id.run do
  let mut a := FloatArray.empty
  for x in xs do a := a.push x
  return a

/--
Solve the equality-constrained LP

```
    minimise   c·x
    subject to A x = b
               0 ≤ x
```

with `c` length `numVars`, `b` length `numConstraints`, and `A` given in
sparse `(row, col, value)` form. Floating-point precision; **not** an
exact-mode certificate-producing solve. Used to verify the FFI / link /
runtime pipeline on every supported platform; see `PLAN.md` for the
real solver entry points.
-/
def smokeSolve
    (c : Array Float) (b : Array Float)
    (rows : Array UInt32) (cols : Array UInt32) (vals : Array Float) :
    SmokeResult :=
  smokeSolveImpl
    (floatArrayOfArray c) (floatArrayOfArray b)
    (packUInt32Array rows) (packUInt32Array cols)
    (floatArrayOfArray vals)

end LeanSoplex
