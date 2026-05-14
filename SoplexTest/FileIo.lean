import SoplexTest.SolveCommon

open Soplex Soplex.Verify SoplexTest

/-- Validate both problems and compare them field-by-field. The
    contract for our file-I/O round trip: writer + reader preserves
    structure modulo `validate`'s normalisation (sparse-entry sort,
    duplicate summing, zero pruning). Both inputs are sigma-wrapped
    because `readMps` / `readLp` return `Σ m n, Problem m n`. -/
private def equalAfterValidate
    (p q : Σ m n, Problem m n) : Outcome :=
  let ⟨pm, pn, pProb⟩ := p
  let ⟨qm, qn, qProb⟩ := q
  if pm ≠ qm then .fail s!"numConstraints: {pm} ≠ {qm}"
  else if pn ≠ qn then .fail s!"numVars: {pn} ≠ {qn}"
  else
    match validate pProb, validate qProb with
    | .ok p', .ok q' =>
      if p'.c.toArray ≠ q'.c.toArray then
        .fail s!"c: {repr p'.c.toArray} ≠ {repr q'.c.toArray}"
      else if p'.objOffset ≠ q'.objOffset then
        .fail s!"objOffset: {p'.objOffset} ≠ {q'.objOffset}"
      else if sparseVals p'.a ≠ sparseVals q'.a then
        .fail s!"a: {repr (sparseVals p'.a)} ≠ {repr (sparseVals q'.a)}"
      else if p'.rowBounds.toArray ≠ q'.rowBounds.toArray then
        .fail s!"rowBounds: {repr p'.rowBounds.toArray} ≠ {repr q'.rowBounds.toArray}"
      else if p'.colBounds.toArray ≠ q'.colBounds.toArray then
        .fail s!"colBounds: {repr p'.colBounds.toArray} ≠ {repr q'.colBounds.toArray}"
      else .ok
    | .error e, _ => .fail s!"validate(p) failed: {repr e}"
    | _, .error e => .fail s!"validate(q) failed: {repr e}"

/-- Helper: wrap an explicitly-typed `Problem m n` as the
    sigma-typed value `Σ m n, Problem m n` that `readMps` /
    `readLp` return and that the round-trip helpers consume. -/
@[inline] private def asSigma {m n : Nat} (p : Problem m n) :
    Σ m n, Problem m n := ⟨m, n, p⟩

/-- The reference Problem corresponding to `SoplexTest/fixtures/tiny.mps`
    and `SoplexTest/fixtures/tiny.lp`: minimise `x1 + x2` subject to
    `x1 + x2 = 1`, `x1, x2 ≥ 0`. -/
private def tinyProblem : Σ m n, Problem m n := asSigma <|
  mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])

/-- A slightly richer Problem used for round-trip tests: includes a
    pure inequality row (`≤`) and a one-sided column lower bound. -/
private def richProblem : Σ m n, Problem m n := asSigma <|
  mkProblem 2 2
    (c := #[3, -2])
    (a := #[(0, 0, 1), (0, 1, 1), (1, 0, 2), (1, 1, -1)])
    (rowBounds := #[(none, some 4), (some 0, none)])
    (colBounds := #[(some 0, some 5), (some 0, none)])

private structure ProblemCase where
  name : String
  problem : Σ m n, Problem m n

private def exactCorpus : Array ProblemCase := #[
  ⟨"optimal equality",
    asSigma <| mkProblem 2 1
      (c := #[1, 1])
      (a := #[(0, 0, 1), (0, 1, 1)])
      (rowBounds := #[(some 1, some 1)])
      (colBounds := #[(some 0, none), (some 0, none)])⟩,
  ⟨"ranged row",
    asSigma <| mkProblem 1 1
      (c := #[1])
      (a := #[(0, 0, 1)])
      (rowBounds := #[(some 1, some 3)])
      (colBounds := #[(some 0, some 2)])⟩,
  ⟨"infeasible rows only",
    asSigma <| mkProblem 1 2
      (c := #[0])
      (a := #[(0, 0, 1), (1, 0, 1)])
      (rowBounds := #[(some 1, none), (none, some 0)])
      (colBounds := #[(none, none)])⟩,
  ⟨"infeasible row and bounds",
    asSigma <| mkProblem 1 1
      (c := #[0])
      (a := #[(0, 0, 1)])
      (rowBounds := #[(some 2, none)])
      (colBounds := #[(some 0, some 1)])⟩,
  ⟨"unbounded",
    asSigma <| mkProblem 1 0
      (c := #[-1])
      (a := #[])
      (rowBounds := #[])
      (colBounds := #[(some 0, none)])⟩,
  ⟨"duplicate sparse entries and big rationals",
    asSigma <| mkProblem 1 1
      (c := #[1234567890123456789])
      (a := #[(0, 0, 1/3), (0, 0, 2/3)])
      (rowBounds := #[(some 1, some 1)])
      (colBounds := #[(some 0, none)])⟩,
  ⟨"max canonical form",
    asSigma <| mkProblem 1 1
      (c := #[-1])
      (a := #[(0, 0, 1)])
      (rowBounds := #[(none, some 1)])
      (colBounds := #[(some 0, none)])⟩
]

/-- SoPlex's LP writer expands ranged rows into two one-sided rows, so
    those cases are covered by the full MPS corpus instead. -/
private def lpStructuralCorpus : Array ProblemCase :=
  exactCorpus.filter fun c =>
    c.name != "ranged row"

private def withTempFile (suffix : String) (k : System.FilePath → IO Outcome) : IO Outcome := do
  let dir ← IO.currentDir
  let tmp := dir / s!".file-io-tests-tmp{suffix}"
  try
    let r ← k tmp
    pure r
  finally
    try IO.FS.removeFile tmp catch _ => pure ()

private def tRoundtripMps : IO Outcome :=
  withTempFile ".mps" fun path => do
    let ⟨_, _, prob⟩ := richProblem
    match writeMps path prob with
    | .error e => return .fail s!"writeMps failed: {repr e}"
    | .ok () =>
      match readMps path with
      | .error e => return .fail s!"readMps failed: {repr e}"
      | .ok p' => return equalAfterValidate richProblem p'

private def tRoundtripLp : IO Outcome :=
  withTempFile ".lp" fun path => do
    let ⟨_, _, prob⟩ := richProblem
    match writeLp path prob with
    | .error e => return .fail s!"writeLp failed: {repr e}"
    | .ok () =>
      match readLp path with
      | .error e => return .fail s!"readLp failed: {repr e}"
      | .ok p' => return equalAfterValidate richProblem p'

private def checkRoundtripMps (path : System.FilePath) (c : ProblemCase) : IO Outcome := do
  let ⟨_, _, prob⟩ := c.problem
  match writeMps path prob with
  | .error e => return .fail s!"{c.name}: writeMps failed: {repr e}"
  | .ok () =>
    match readMps path with
    | .error e => return .fail s!"{c.name}: readMps failed: {repr e}"
    | .ok p' =>
      match equalAfterValidate c.problem p' with
      | .ok => return .ok
      | .fail msg => return .fail s!"{c.name}: {msg}"

private def checkRoundtripLp (path : System.FilePath) (c : ProblemCase) : IO Outcome := do
  let ⟨_, _, prob⟩ := c.problem
  match writeLp path prob with
  | .error e => return .fail s!"{c.name}: writeLp failed: {repr e}"
  | .ok () =>
    match readLp path with
    | .error e => return .fail s!"{c.name}: readLp failed: {repr e}"
    | .ok p' =>
      match equalAfterValidate c.problem p' with
      | .ok => return .ok
      | .fail msg => return .fail s!"{c.name}: {msg}"

private def tCorpusRoundtripMps : IO Outcome :=
  withTempFile ".corpus.mps" fun path => do
    for c in exactCorpus do
      match ← checkRoundtripMps path c with
      | .ok => pure ()
      | .fail msg => return .fail msg
    return .ok

private def tCorpusRoundtripLp : IO Outcome :=
  withTempFile ".corpus.lp" fun path => do
    for c in lpStructuralCorpus do
      match ← checkRoundtripLp path c with
      | .ok => pure ()
      | .fail msg => return .fail msg
    return .ok

private def tFixtureMps : IO Outcome := do
  let path : System.FilePath := "SoplexTest" / "fixtures" / "tiny.mps"
  match readMps path with
  | .error e => return .fail s!"readMps failed: {repr e}"
  | .ok p => return equalAfterValidate tinyProblem p

private def tFixtureLp : IO Outcome := do
  let path : System.FilePath := "SoplexTest" / "fixtures" / "tiny.lp"
  match readLp path with
  | .error e => return .fail s!"readLp failed: {repr e}"
  | .ok p => return equalAfterValidate tinyProblem p

/-- `Maximize 2 x1 + 3 x2` must read back as min-form `c = [-2, -3]`.
    Regression test: an earlier `problem_from_lp` flipped the LP's sense
    in place, which (because SoPlex's `obj()` itself sense-corrects)
    cancelled out and returned `+c` instead of `-c`. -/
private def tMaximizeFixture : IO Outcome := do
  let path : System.FilePath := "SoplexTest" / "fixtures" / "maximize.lp"
  let expected : Σ m n, Problem m n := asSigma <|
    mkProblem 2 1
      (c := #[-2, -3])
      (a := #[(0, 0, 1), (0, 1, 1)])
      (rowBounds := #[(none, some 4)])
      (colBounds := #[(some 0, none), (some 0, none)])
  match readLp path with
  | .error e => return .fail s!"readLp failed: {repr e}"
  | .ok p => return equalAfterValidate expected p

/-- Writing a `Problem` with nonzero `objOffset` must fail loudly:
    SoPlex's `writeLPF` / `writeMPS` for the rational LP drop the
    offset on the floor, so we reject it at the bridge boundary. -/
private def tWriteNonzeroOffsetRejected : IO Outcome :=
  withTempFile ".mps" fun path => do
    let p : Problem 1 2 :=
      { mkProblem 2 1
          (c := #[1, 1])
          (a := #[(0, 0, 1), (0, 1, 1)])
          (rowBounds := #[(some 1, some 1)])
          (colBounds := #[(some 0, none), (some 0, none)])
        with objOffset := 5 }
    match writeMps path p with
    | .ok () => return .fail "expected parseError for nonzero objOffset"
    | .error (.parseError _ _) => return .ok
    | .error e => return .fail s!"expected .parseError, got {repr e}"

private def tMissingFile : IO Outcome := do
  let path : System.FilePath := "tests" / "fixtures" / "does-not-exist.mps"
  match readMps path with
  | .ok _ => return .fail "expected parseError for missing file"
  | .error (.parseError _ _) => return .ok
  | .error e => return .fail s!"expected .parseError, got {repr e}"

/-! ## Verify-corpus round-trip (issue #20).

  Each `Problem` below appears in `SoplexTest/Verify.lean`'s hand-rolled
  certificate corpus. We assert that writing it to MPS, reading it back,
  and validating both sides recovers the same normalised problem
  (sparse-entry sort, duplicate summing, zero pruning).

  Caveats — these are SoPlex format properties, not bridge bugs:

  * `writeLp` decomposes ranged rows (`lo` and `hi` both finite with
    `lo < hi`) into two non-ranged rows on round-trip, so we test ranged
    rows only via MPS.
  * `writeMps` rejects nonzero `objOffset` (already tested above), so
    no corpus entry exercises that path here. -/

private def equalityLp : Σ m n, Problem m n := asSigma <|
  mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])

private def rangedRowLp : Σ m n, Problem m n := asSigma <|
  mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 3)])
    (colBounds := #[(some 0, some 2)])

private def infeasibleRowsOnlyLp : Σ m n, Problem m n := asSigma <|
  mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])

private def infeasibleRowAndBoundsLp : Σ m n, Problem m n := asSigma <|
  mkProblem 1 1
    (c := #[0])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 2, none)])
    (colBounds := #[(some 0, some 1)])

private def unboundedLp : Σ m n, Problem m n := asSigma <|
  mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])

private def unboundedWithEqualityLp : Σ m n, Problem m n := asSigma <|
  mkProblem 2 1
    (c := #[-1, 0])
    (a := #[(0, 0, 1), (0, 1, -1)])
    (rowBounds := #[(some 0, some 0)])
    (colBounds := #[(some 0, none), (none, none)])

/-- Exercises `validate`'s normalisation paths via the file-format
    pipeline: a duplicate sparse entry pair `((0,0,1/3) + (0,0,2/3))`
    collapsing to `(0,0,1)`, large numerator coefficients (multi-digit
    GMP), and one-sided bounds. After `validate`, the round-trip side
    sees the normalised LP, so we assert structural equality of the
    normalised forms — which is mathematical equivalence given that
    `validate` is a canonicalising idempotent. -/
private def normalisationCorpusLp : Σ m n, Problem m n := asSigma <|
  mkProblem 2 2
    (c := #[1234567890123456789, -1/3])
    (a := #[(0, 0, 1/3), (0, 0, 2/3), (0, 1, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, some 1), (some 0, none)])
    (colBounds := #[(some 0, none), (some 0, none)])

private def roundtripMpsOf (p : Σ m n, Problem m n) : IO Outcome :=
  withTempFile ".mps" fun path => do
    let ⟨_, _, prob⟩ := p
    match writeMps path prob with
    | .error e => return .fail s!"writeMps failed: {repr e}"
    | .ok () =>
      match readMps path with
      | .error e => return .fail s!"readMps failed: {repr e}"
      | .ok p' => return equalAfterValidate p p'

private def roundtripLpOf (p : Σ m n, Problem m n) : IO Outcome :=
  withTempFile ".lp" fun path => do
    let ⟨_, _, prob⟩ := p
    match writeLp path prob with
    | .error e => return .fail s!"writeLp failed: {repr e}"
    | .ok () =>
      match readLp path with
      | .error e => return .fail s!"readLp failed: {repr e}"
      | .ok p' => return equalAfterValidate p p'

private def tRoundtripMpsEquality           : IO Outcome := roundtripMpsOf equalityLp
private def tRoundtripMpsRangedRow          : IO Outcome := roundtripMpsOf rangedRowLp
private def tRoundtripMpsInfeasRows         : IO Outcome := roundtripMpsOf infeasibleRowsOnlyLp
private def tRoundtripMpsInfeasRowAndBounds : IO Outcome := roundtripMpsOf infeasibleRowAndBoundsLp
private def tRoundtripMpsUnbounded          : IO Outcome := roundtripMpsOf unboundedLp
private def tRoundtripMpsUnboundedEq        : IO Outcome := roundtripMpsOf unboundedWithEqualityLp
private def tRoundtripMpsNormalisation      : IO Outcome := roundtripMpsOf normalisationCorpusLp

/-- LP-format round-trip covers the corpus minus two known SoPlex
    writer limitations:

    * `rangedRowLp` — SoPlex's LP writer expands a ranged row into two
      non-ranged rows on output. The structural-equality assertion
      would fail (`numConstraints` grows from `1` to `2`); meanwhile
      the solution set is preserved, so this is a writer-format quirk
      rather than a bridge bug. Tested via MPS above instead.
    * `infeasibleRowAndBoundsLp` and `unboundedLp` — both have zero
      rows, which SoPlex's LP writer rejects. Tested via MPS above. -/
private def tRoundtripLpEquality      : IO Outcome := roundtripLpOf equalityLp
private def tRoundtripLpInfeasRows    : IO Outcome := roundtripLpOf infeasibleRowsOnlyLp
private def tRoundtripLpUnboundedEq   : IO Outcome := roundtripLpOf unboundedWithEqualityLp
private def tRoundtripLpNormalisation : IO Outcome := roundtripLpOf normalisationCorpusLp

def allTests : Array TestCase := #[
  ⟨"MPS round-trip preserves structure",        tRoundtripMps⟩,
  ⟨"LP  round-trip preserves structure",        tRoundtripLp⟩,
  ⟨"MPS corpus round-trip preserves structure", tCorpusRoundtripMps⟩,
  ⟨"LP  corpus round-trip preserves structure", tCorpusRoundtripLp⟩,
  ⟨"hand-authored MPS fixture parses",          tFixtureMps⟩,
  ⟨"hand-authored LP fixture parses",           tFixtureLp⟩,
  ⟨"Maximize LP reads back as -c",              tMaximizeFixture⟩,
  ⟨"writeMps rejects nonzero objOffset",        tWriteNonzeroOffsetRejected⟩,
  ⟨"missing file surfaces as parseError",       tMissingFile⟩,
  ⟨"MPS round-trip: equality LP",               tRoundtripMpsEquality⟩,
  ⟨"MPS round-trip: ranged-row LP",             tRoundtripMpsRangedRow⟩,
  ⟨"MPS round-trip: infeasible rows-only LP",   tRoundtripMpsInfeasRows⟩,
  ⟨"MPS round-trip: row+bounds infeasible LP",  tRoundtripMpsInfeasRowAndBounds⟩,
  ⟨"MPS round-trip: unbounded LP",              tRoundtripMpsUnbounded⟩,
  ⟨"MPS round-trip: unbounded with equality",   tRoundtripMpsUnboundedEq⟩,
  ⟨"MPS round-trip: normalisation corpus",      tRoundtripMpsNormalisation⟩,
  ⟨"LP  round-trip: equality LP",               tRoundtripLpEquality⟩,
  ⟨"LP  round-trip: infeasible rows-only LP",   tRoundtripLpInfeasRows⟩,
  ⟨"LP  round-trip: unbounded with equality",   tRoundtripLpUnboundedEq⟩,
  ⟨"LP  round-trip: normalisation corpus",      tRoundtripLpNormalisation⟩
]

def main : IO UInt32 := runAll "file-I/O" allTests
