/-
  Minimal v0 surface for `lean-soplex`.

  This file currently exposes two FFI entry points:

  * `version` — returns SoPlex's compile-time version macro. Exists to
    confirm the FFI is linked and the SoPlex headers used at build time
    match the runtime.

  * `ffiCheckSolve` — solves a small equality-constrained LP in
    floating-point mode. Used as the cross-platform CI build verifier
    (see `Main.lean`); it exercises SoPlex's constructors, parameter
    setting, column / row builders, the solver loop, and result
    extraction in a single call.

  The real exact-mode API (`solveExact`, `solveFloat`, file I/O, the
  certificate types) lands in subsequent commits per `PLAN.md`.
-/

import LeanSoplex.Verify

namespace LeanSoplex

open LeanSoplex.Verify

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

/-- Result of `ffiCheckSolve`. `ret` follows the FFI layer convention:
    `0` = optimal, `1` = infeasible, `2` = unbounded, anything else is an
    FFI / SoPlex error. -/
structure FfiCheckResult where
  /-- Primal solution (length = `numVars`). Meaningful iff `ret = 0`. -/
  primal : FloatArray
  /-- Return code; see structure docstring. -/
  ret    : UInt32
  /-- Objective value; meaningful iff `ret = 0`. -/
  obj    : Float
deriving Inhabited

@[extern "lean_soplex_ffi_check_solve_ffi"]
private opaque ffiCheckSolveImpl
    (c : @& FloatArray) (b : @& FloatArray)
    (aRows : @& ByteArray) (aCols : @& ByteArray) (aVals : @& FloatArray) :
    FfiCheckResult

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

private def ratStrings (xs : Array Rat) : Array String :=
  xs.map toString

private def optionRatMask (xs : Array (Option Rat)) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for x in xs do
    bs := bs.push (if x.isSome then 1 else 0)
  return bs

private def optionRatStrings (xs : Array (Option Rat)) : Array String :=
  xs.map (fun x => x.elim "0" toString)

/-- Flat marshalling of a `Problem`'s sparse / bound data into the
    ByteArray + decimal-string form the C++ bridge expects. Shared
    between `solveExact`, `writeMps`, and `writeLp`. -/
private structure ProblemFlat where
  numVars        : UInt32
  numConstraints : UInt32
  c              : Array String
  objOffset      : String
  aRows          : ByteArray
  aCols          : ByteArray
  aVals          : Array String
  rowLoMask      : ByteArray
  rowLo          : Array String
  rowHiMask      : ByteArray
  rowHi          : Array String
  colLoMask      : ByteArray
  colLo          : Array String
  colHiMask      : ByteArray
  colHi          : Array String

private def problemFlatten (p : Problem) : ProblemFlat :=
  let rows  := p.a.map (fun e => UInt32.ofNat e.1)
  let cols  := p.a.map (fun e => UInt32.ofNat e.2.1)
  let vals  := p.a.map (fun e => e.2.2)
  let rowLo := p.rowBounds.map Prod.fst
  let rowHi := p.rowBounds.map Prod.snd
  let colLo := p.colBounds.map Prod.fst
  let colHi := p.colBounds.map Prod.snd
  { numVars        := UInt32.ofNat p.numVars
    numConstraints := UInt32.ofNat p.numConstraints
    c              := ratStrings p.c
    objOffset      := toString p.objOffset
    aRows          := packUInt32Array rows
    aCols          := packUInt32Array cols
    aVals          := ratStrings vals
    rowLoMask      := optionRatMask rowLo
    rowLo          := optionRatStrings rowLo
    rowHiMask      := optionRatMask rowHi
    rowHi          := optionRatStrings rowHi
    colLoMask      := optionRatMask colLo
    colLo          := optionRatStrings colLo
    colHiMask      := optionRatMask colHi
    colHi          := optionRatStrings colHi }

@[extern "lean_soplex_solve_exact"]
private opaque solveExactFlat
    (numVars numConstraints : UInt32)
    (sense simplex : UInt8)
    (hasTimeLimit : Bool) (timeLimit : Float)
    (hasIterLimit : Bool) (iterLimit : UInt32)
    (verbose : Bool) (randomSeed : UInt32)
    (precisionBoost presolve : Bool)
    (c : @& Array String) (objOffset : @& String)
    (aRows aCols : @& ByteArray) (aVals : @& Array String)
    (rowLoMask : @& ByteArray) (rowLo : @& Array String)
    (rowHiMask : @& ByteArray) (rowHi : @& Array String)
    (colLoMask : @& ByteArray) (colLo : @& Array String)
    (colHiMask : @& ByteArray) (colHi : @& Array String) :
    Except String Solution

private def solveErrorFromBridge (e : String) : SolveError :=
  .bridge e

private def mapObjectiveForSense (sense : ObjSense) (s : Solution) : Solution :=
  match sense with
  | .minimize => s
  | .maximize => { s with objective := s.objective.map Neg.neg }

private def objSenseTag : ObjSense → UInt8
  | .minimize => 0
  | .maximize => 1

private def simplexTag : Simplex → UInt8
  | .primal => 0
  | .dual => 1
  | .auto => 2

/-- Exact rational solve through SoPlex. The bridge receives rationals
    as canonical decimal strings (`"n"` or `"n/d"`), deliberately avoiding
    any dependence on Lean's small-vs-boxed integer representation across
    the C++ ABI. For `.maximize`, the LP sent to SoPlex is the verifier's
    minimization canonicalization; the reported objective is flipped back
    into the caller's original sense. -/
opaque solveExact (opts : Options) (p : Problem) : Except SolveError Solution := do
  let opts ← validateOptions opts |>.mapError SolveError.invalidOptions
  let p ← validate p |>.mapError SolveError.invalidProblem
  let f := problemFlatten (canonicalize opts.sense p)
  let sol ← solveExactFlat
    f.numVars f.numConstraints
    (objSenseTag .minimize) (simplexTag opts.simplex)
    opts.timeLimit.isSome (opts.timeLimit.getD 0.0)
    opts.iterLimit.isSome (UInt32.ofNat (opts.iterLimit.getD 0))
    opts.verbose opts.randomSeed opts.precisionBoost opts.presolve
    f.c f.objOffset
    f.aRows f.aCols f.aVals
    f.rowLoMask f.rowLo
    f.rowHiMask f.rowHi
    f.colLoMask f.colLo
    f.colHiMask f.colHi
    |>.mapError solveErrorFromBridge
  pure (mapObjectiveForSense opts.sense sol)

@[extern "lean_soplex_solve_float"]
private opaque solveFloatFlat
    (numVars numConstraints : UInt32)
    (sense simplex : UInt8)
    (hasTimeLimit : Bool) (timeLimit : Float)
    (hasIterLimit : Bool) (iterLimit : UInt32)
    (verbose : Bool) (randomSeed : UInt32)
    (presolve : Bool)
    (c : @& Array String) (objOffset : @& String)
    (aRows aCols : @& ByteArray) (aVals : @& Array String)
    (rowLoMask : @& ByteArray) (rowLo : @& Array String)
    (rowHiMask : @& ByteArray) (rowHi : @& Array String)
    (colLoMask : @& ByteArray) (colLo : @& Array String)
    (colHiMask : @& ByteArray) (colHi : @& Array String) :
    Except String FloatSolution

private def mapFloatObjectiveForSense (sense : ObjSense) (s : FloatSolution) : FloatSolution :=
  match sense with
  | .minimize => s
  | .maximize => { s with objective := s.objective.map Neg.neg }

/-- Floating-point solve through SoPlex. Mirrors `solveExact`'s ABI
    (decimal-string `Rat` marshalling) but builds the LP via
    `addColReal` / `addRowReal` and runs SoPlex in its default mode.

    The returned `primalAsRat` entries are exact rationals representing
    the IEEE-754 doubles SoPlex computed (via `mpq_set_d`), **not**
    decimal rationals and **not** verifier-grade certificates: e.g.
    `0.1` round-trips as `7205759403792794 / 2^56`. The distinct
    `FloatSolution` return type — separate from `Solution` — makes
    feeding these into the certificate checker hard to do by accident. -/
opaque solveFloat (opts : Options) (p : Problem) : Except SolveError FloatSolution := do
  let opts ← validateOptions opts |>.mapError SolveError.invalidOptions
  let p ← validate p |>.mapError SolveError.invalidProblem
  let f := problemFlatten (canonicalize opts.sense p)
  let sol ← solveFloatFlat
    f.numVars f.numConstraints
    (objSenseTag .minimize) (simplexTag opts.simplex)
    opts.timeLimit.isSome (opts.timeLimit.getD 0.0)
    opts.iterLimit.isSome (UInt32.ofNat (opts.iterLimit.getD 0))
    opts.verbose opts.randomSeed opts.presolve
    f.c f.objOffset
    f.aRows f.aCols f.aVals
    f.rowLoMask f.rowLo
    f.rowHiMask f.rowHi
    f.colLoMask f.colLo
    f.colHiMask f.colHi
    |>.mapError solveErrorFromBridge
  pure (mapFloatObjectiveForSense opts.sense sol)

/-! ## MPS / LP file I/O.

  Four `opaque` entry points wired to SoPlex's `SPxLPBase<Rational>`
  format-specific readers / writers (see `ffi/lean_soplex_bridge.cpp`):

  * Bridge-level failures (file not found, parse error, write error)
    become `SolveError.parseError` carrying the path; the bridge
    captures the error message.
  * Reads return an *unvalidated* `Problem` — sparse entries appear in
    the order SoPlex emits them. Callers that want the normalised form
    should pass the result through `validate`.
  * Writes pre-normalise via `validate`. A malformed `Problem` surfaces
    as `SolveError.invalidProblem`.

  Round-trip equivalence under `validate` is *structural-after-validate*,
  not permutation-invariant: see `FileIoTests.lean`. Format-specific
  caveats — notably `writeLp` expanding ranged rows into two non-ranged
  rows — are SoPlex format properties, not bridge artefacts. -/

@[extern "lean_soplex_read_mps_ffi"]
private opaque readMpsImpl (path : @& String) : Except String Problem

@[extern "lean_soplex_read_lp_ffi"]
private opaque readLpImpl (path : @& String) : Except String Problem

@[extern "lean_soplex_write_mps_ffi"]
private opaque writeMpsFlat
    (path : @& String)
    (numVars numConstraints : UInt32)
    (c : @& Array String) (objOffset : @& String)
    (aRows aCols : @& ByteArray) (aVals : @& Array String)
    (rowLoMask : @& ByteArray) (rowLo : @& Array String)
    (rowHiMask : @& ByteArray) (rowHi : @& Array String)
    (colLoMask : @& ByteArray) (colLo : @& Array String)
    (colHiMask : @& ByteArray) (colHi : @& Array String) :
    Except String Unit

@[extern "lean_soplex_write_lp_ffi"]
private opaque writeLpFlat
    (path : @& String)
    (numVars numConstraints : UInt32)
    (c : @& Array String) (objOffset : @& String)
    (aRows aCols : @& ByteArray) (aVals : @& Array String)
    (rowLoMask : @& ByteArray) (rowLo : @& Array String)
    (rowHiMask : @& ByteArray) (rowHi : @& Array String)
    (colLoMask : @& ByteArray) (colLo : @& Array String)
    (colHiMask : @& ByteArray) (colHi : @& Array String) :
    Except String Unit

/-- Parse a `Problem` from an MPS file via SoPlex's rational reader. -/
opaque readMps (path : System.FilePath) : Except SolveError Problem :=
  (readMpsImpl path.toString).mapError fun e => .parseError path.toString e

/-- Write a `Problem` to an MPS file via SoPlex's rational writer.
    The `Problem` is `validate`d before serialisation. -/
opaque writeMps (path : System.FilePath) (p : Problem) : Except SolveError Unit := do
  let p ← validate p |>.mapError SolveError.invalidProblem
  let s := path.toString
  let f := problemFlatten p
  writeMpsFlat s f.numVars f.numConstraints f.c f.objOffset
    f.aRows f.aCols f.aVals
    f.rowLoMask f.rowLo f.rowHiMask f.rowHi
    f.colLoMask f.colLo f.colHiMask f.colHi
    |>.mapError fun e => .parseError s e

/-- Parse a `Problem` from an LP-format file via SoPlex's rational reader. -/
opaque readLp (path : System.FilePath) : Except SolveError Problem :=
  (readLpImpl path.toString).mapError fun e => .parseError path.toString e

/-- Write a `Problem` to an LP-format file via SoPlex's rational writer.
    The `Problem` is `validate`d before serialisation. Note that SoPlex's
    LP-format writer expands a ranged row (both `lo` and `hi` finite,
    `lo ≠ hi`) into two separate non-ranged rows. Use MPS for ranged
    rows if you need structural round-trip. -/
opaque writeLp (path : System.FilePath) (p : Problem) : Except SolveError Unit := do
  let p ← validate p |>.mapError SolveError.invalidProblem
  let s := path.toString
  let f := problemFlatten p
  writeLpFlat s f.numVars f.numConstraints f.c f.objOffset
    f.aRows f.aCols f.aVals
    f.rowLoMask f.rowLo f.rowHiMask f.rowHi
    f.colLoMask f.colLo f.colHiMask f.colHi
    |>.mapError fun e => .parseError s e

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
def ffiCheckSolve
    (c : Array Float) (b : Array Float)
    (rows : Array UInt32) (cols : Array UInt32) (vals : Array Float) :
    FfiCheckResult :=
  ffiCheckSolveImpl
    (floatArrayOfArray c) (floatArrayOfArray b)
    (packUInt32Array rows) (packUInt32Array cols)
    (floatArrayOfArray vals)

/-! ## Verified-solve driver.

  Composes `validateOptions`, `validate`, `solveExact`, and
  `verifyOutcome` from `LeanSoplex.Verify.Driver`. See PLAN.md
  §"User-facing driver".
-/

/-- Default `denomBudget` for `solveVerified`: combined numerator +
    denominator bit length per rational coordinate. `10000` is comfortable
    headroom over what well-behaved LPs produce while still ruling out
    refinement runaway. -/
def defaultDenomBudget : Option Nat := some 10000

/-- Drive `validate`, `solveExact`, then the checker, packaged as a
    `VerifiedSolve` carrying a real soundness-lemma proof.

    * `validateOptions` and `validate` run first; either failure
      surfaces as `Except.error`.
    * `Options.presolve` is forced `false` internally — the checker
      must run against the (normalised) input LP, not whatever
      SoPlex's presolve transformed it into. See PLAN.md §"What this
      catches" §4.
    * `denomBudget` is a ceiling on the bit length of every rational
      coordinate in the returned certificate; exceeding it yields
      `Verified.unchecked .budgetExceeded`. `none` disables the check.
    * The returned `normalized` field is `validate p`, the `Problem`
      the proof is indexed by. Downstream code reasons about that
      value, not about the raw user input.

    Every failure path (non-terminal status, missing certificate
    field, failed `check*`, budget overrun) lands in
    `Verified.unchecked _`; the three positive constructors are only
    populated from `checkOptimal_sound` / `checkInfeasible_sound` /
    `checkUnbounded_sound`. -/
def solveVerified (opts : Options) (p : Problem)
    (denomBudget : Option Nat := defaultDenomBudget) :
    Except SolveError (VerifiedSolve opts.sense) := do
  let _ ← validateOptions opts |>.mapError SolveError.invalidOptions
  let normalized ← validate p |>.mapError SolveError.invalidProblem
  let opts' := { opts with presolve := false }
  let sol ← solveExact opts' normalized
  pure { normalized
         verified := verifyOutcome opts denomBudget normalized sol }

end LeanSoplex
