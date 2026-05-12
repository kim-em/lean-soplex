/-
  Hand-rolled tests for the pure-Lean certificate checker.

  This executable exists to exercise `validate`, `checkOptimal`,
  `checkInfeasible`, `checkUnbounded`, and the supporting `is*`
  Booleans on small LPs with known answers. Two purposes:

  * Catch bugs in the `Bool` definitions before they are baked into the
    soundness proofs (see `PLAN.md` §"Implementation order" step 3:
    "Drive [the checker] from hand-rolled tiny certificates with no
    SoPlex involvement").
  * Provide a SoPlex-free CI signal that runs even on platforms where
    the FFI link is currently broken (notably Windows).

  All certificates are computed by hand and the expected `Bool`
  results commented inline.
-/

import LeanSoplex.Verify

open LeanSoplex LeanSoplex.Verify

/-! ## Test infrastructure. -/

inductive Outcome
  | ok
  | fail (msg : String)

instance : Inhabited Outcome := ⟨.ok⟩

structure TestCase where
  name    : String
  outcome : Unit → Outcome

@[inline] private def expect (cond : Bool) (msg : String) : Outcome :=
  if cond then .ok else .fail msg

@[inline] private def expectTrue (cond : Bool) : Outcome :=
  expect cond "expected true, got false"

@[inline] private def expectFalse (cond : Bool) : Outcome :=
  expect (!cond) "expected false, got true"

/-! ## `validate` happy paths. -/

/-- A small `Problem` constructor that does *not* run `validate`. Used
    so test cases can probe both validated and unvalidated inputs. -/
private def mkProblem
    (numVars numConstraints : Nat)
    (c : Array Rat)
    (a : Array (Nat × Nat × Rat))
    (rowBounds : Array (Option Rat × Option Rat))
    (colBounds : Array (Option Rat × Option Rat))
    (objOffset : Rat := 0) : Problem :=
  { numVars, numConstraints, c, a, rowBounds, colBounds, objOffset }

/-- `validate` collapses duplicate `(row, col)` entries and drops the
    resulting zeros. -/
def tValidateNormalise : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 0, 2), (0, 0, -3), (0, 1, 5)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  match validate p with
  | .ok p' => expect (p'.a == #[(0, 1, (5 : Rat))])
                s!"expected #[(0,1,5)], got {repr p'.a}"
  | .error e => .fail s!"validate rejected: {repr e}"

/-- `validate` lexicographically sorts sparse entries. -/
def tValidateSort : Outcome :=
  let p := mkProblem 2 2
    (c := #[1, 1])
    (a := #[(1, 1, 4), (0, 1, 2), (1, 0, 3), (0, 0, 1)])
    (rowBounds := #[(some 0, some 0), (some 0, some 0)])
    (colBounds := #[(none, none), (none, none)])
  match validate p with
  | .ok p' =>
      let expected : Array (Nat × Nat × Rat) :=
        #[(0, 0, 1), (0, 1, 2), (1, 0, 3), (1, 1, 4)]
      expect (p'.a == expected) s!"expected {repr expected}, got {repr p'.a}"
  | .error e => .fail s!"validate rejected: {repr e}"

/-- `validate ∘ validate = validate` on already-normalised input. -/
def tValidateIdempotent : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none)])
  match validate p with
  | .ok p₁ =>
    match validate p₁ with
    | .ok p₂ => expect (p₁.a == p₂.a) "validate is not idempotent on `a`"
    | .error e => .fail s!"second validate rejected: {repr e}"
  | .error e => .fail s!"first validate rejected: {repr e}"

/-! ## `validate` rejection paths. -/

def tRejectWrongLengthC : Outcome :=
  let p := mkProblem 2 0
    (c := #[1])                              -- wrong length
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(none, none), (none, none)])
  match validate p with
  | .error (.wrongLength "c" 2 1) => .ok
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

def tRejectWrongLengthRowBounds : Outcome :=
  let p := mkProblem 1 2
    (c := #[1])
    (a := #[])
    (rowBounds := #[(none, none)])           -- wrong length
    (colBounds := #[(none, none)])
  match validate p with
  | .error (.wrongLength "rowBounds" 2 1) => .ok
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

def tRejectSparseRowOOR : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(5, 0, 1)])                      -- row 5 ≥ numConstraints
    (rowBounds := #[(none, none)])
    (colBounds := #[(none, none)])
  match validate p with
  | .error (.indexOutOfRange .row 5 1) => .ok
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

def tRejectSparseColOOR : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 7, 1)])                      -- col 7 ≥ numVars
    (rowBounds := #[(none, none)])
    (colBounds := #[(none, none)])
  match validate p with
  | .error (.indexOutOfRange .col 7 1) => .ok
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

def tRejectInvertedColBound : Outcome :=
  let p := mkProblem 1 0
    (c := #[1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 5, some 3)])       -- 5 > 3
  match validate p with
  | .error (.boundInverted .col 0 lo hi) =>
      expect (lo == 5 && hi == 3) s!"bound values wrong: {repr lo} {repr hi}"
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

/-! ## `checkOptimal` — positive cases. -/

/-- `min x + y  s.t.  x + y = 1, x, y ≥ 0`. Optimum at `(0,1)` with
    obj `1`. Dual: `yL = [1], yU = [0], zL = [0,0], zU = [0,0]`. -/
def tOptimalEquality : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  let x : Array Rat := #[0, 1]
  let d : DualBundle :=
    { rowLower := #[1], rowUpper := #[0]
    , colLower := #[0, 0], colUpper := #[0, 0] }
  expectTrue (checkOptimal p x d)

/-- `min x  s.t.  1 ≤ x ≤ 3, 0 ≤ x ≤ 2`. Ranged row + boxed column.
    Optimum at `x = 1` (row lower active). Dual: `yL = [1]`,
    everything else zero. -/
def tOptimalRangedRow : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 3)])
    (colBounds := #[(some 0, some 2)])
  let x : Array Rat := #[1]
  let d : DualBundle :=
    { rowLower := #[1], rowUpper := #[0]
    , colLower := #[0], colUpper := #[0] }
  expectTrue (checkOptimal p x d)

/-- `max x + y  s.t.  x + y ≤ 1, x, y ≥ 0`, canonicalised to
    `min -x - y` with the same constraints. Optimum at `(1/2, 1/2)`,
    canonicalised obj = `-1`. Dual: `yU = [1]` (only row upper active),
    everything else zero. -/
def tOptimalMaxCanonicalized : Outcome :=
  let pMax := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(none, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  let p := canonicalize .maximize pMax        -- negates `c` and `objOffset`
  let x : Array Rat := #[1/2, 1/2]
  let d : DualBundle :=
    { rowLower := #[0], rowUpper := #[1]
    , colLower := #[0, 0], colUpper := #[0, 0] }
  expectTrue (checkOptimal p x d)

/-! ## `checkInfeasible` — positive cases. -/

/-- `min 0  s.t.  x ≥ 1, x ≤ 0` (two rows, free column). Infeasibility
    from rows alone. Farkas: `yL = [1, 0], yU = [0, 1]`, so the
    homogeneous sum `Aᵀ(yL − yU) = 1·1 + 1·(-1) = 0`, and the bound
    combination `1·1 - 1·0 = 1 > 0`. -/
def tInfeasibleRowsOnly : Outcome :=
  let p := mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])
  let d : DualBundle :=
    { rowLower := #[1, 0], rowUpper := #[0, 1]
    , colLower := #[0], colUpper := #[0] }
  expectTrue (checkInfeasible p d)

/-- Raw Bool-checker stress test (the LP itself fails `validate` —
    `0 ≤ x ≤ -1` is an inverted column bound, which `validate` rejects
    as `boundInverted` long before the checker would run). Constructs
    the four-vector Farkas form from PLAN.md §"Worked example" directly
    against the unvalidated `Problem`, to pin the sign convention for
    column-bounds-only infeasibility. In the `validate → solveExact →
    checkInfeasible` pipeline this case never arises — infeasibility
    that reaches the checker must include at least one row, since
    `validate` rejects any inverted bound first. Farkas: `zL = [1],
    zU = [1]`. Stationarity `zL − zU = 0`, bound combination
    `1·0 - 1·(-1) = 1 > 0`. -/
def tInfeasibleColBoundsOnly : Outcome :=
  let p : Problem :=
    { numVars := 1, numConstraints := 0
    , c := #[0], objOffset := 0
    , a := #[], rowBounds := #[]
    , colBounds := #[(some 0, some (-1))] }
  let d : DualBundle :=
    { rowLower := #[], rowUpper := #[]
    , colLower := #[1], colUpper := #[1] }
  expectTrue (checkInfeasible p d)

/-- `min 0  s.t.  x ≥ 2, 0 ≤ x ≤ 1`. Row + bounds infeasibility.
    Farkas multipliers: `yL = [1]` on the row, `zU = [1]` on the
    column upper bound. Aᵀ(yL−yU) + (zL−zU) = 1·1 + (0−1) = 0;
    bound combination = `1·2 + 0·0 − 1·1 = 1 > 0`. -/
def tInfeasibleRowAndBounds : Outcome :=
  let p := mkProblem 1 1
    (c := #[0])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 2, none)])
    (colBounds := #[(some 0, some 1)])
  let d : DualBundle :=
    { rowLower := #[1], rowUpper := #[0]
    , colLower := #[0], colUpper := #[1] }
  expectTrue (checkInfeasible p d)

/-! ## `checkUnbounded` — positive cases. -/

/-- `min -x  s.t.  x ≥ 0`. Base `x = (0)`, ray `r = (1)`. -/
def tUnboundedSimple : Outcome :=
  let p := mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Array Rat := #[0]
  let r : Array Rat := #[1]
  expectTrue (checkUnbounded p x r)

/-- `min -x  s.t.  x - y = 0, x ≥ 0` (y free). Base `(0,0)`, ray
    `(1,1)`. Equality row collapses to `(Ar)₀ = 0`. -/
def tUnboundedWithEquality : Outcome :=
  let p := mkProblem 2 1
    (c := #[-1, 0])
    (a := #[(0, 0, 1), (0, 1, -1)])
    (rowBounds := #[(some 0, some 0)])
    (colBounds := #[(some 0, none), (none, none)])
  let x : Array Rat := #[0, 0]
  let r : Array Rat := #[1, 1]
  expectTrue (checkUnbounded p x r)

/-! ## Negative cases — `check*` correctly rejects bad certificates. -/

/-- Primal violates the column lower bound. -/
def tRejectInfeasiblePrimal : Outcome :=
  let p := mkProblem 1 0
    (c := #[1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Array Rat := #[-1]                  -- below lower bound
  let d : DualBundle :=
    { rowLower := #[], rowUpper := #[]
    , colLower := #[1], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- Stationarity off by sign: pick a `d` that satisfies everything else
    but has `Aᵀ(yL−yU) + (zL−zU) = -c` instead of `c`. -/
def tRejectBadStationarity : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none)])
  let x : Array Rat := #[1]
  let d : DualBundle :=                       -- yL=0,yU=1 gives -1
    { rowLower := #[0], rowUpper := #[1]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- Pins the four-vector ranged-row decomposition: same primal as
    `tOptimalRangedRow` (`min x s.t. 1 ≤ x ≤ 3, 0 ≤ x ≤ 2`, x* = 1),
    but with multipliers `yL = 2, yU = 1` (same signed dual `yL − yU =
    1` so stationarity still passes) rather than `(1, 0)`. `dualObj =
    2·1 − 1·3 = −1`, while `primalObj = 1`, so `checkOptimal` must
    reject. Would not be caught if `dualObj` only consulted the signed
    dual. -/
def tRejectRangedRowDecomposition : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 3)])
    (colBounds := #[(some 0, some 2)])
  let x : Array Rat := #[1]
  let d : DualBundle :=
    { rowLower := #[2], rowUpper := #[1]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- `primalObj ≠ dualObj`: take a feasible primal and a feasible dual
    that disagree on the objective value. -/
def tRejectObjectiveMismatch : Outcome :=
  -- `min x  s.t. x = 1, x ≥ 0`. True optimum obj = 1 with yL=1.
  -- We pass `x = 1` (feasible) but `yL = 0, zL = 1` (also dual-feasible:
  -- stationarity 0 + 1 = 1 = c, nonneg ✓), yielding dualObj = 0 ≠ 1.
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none)])
  let x : Array Rat := #[1]
  let d : DualBundle :=
    { rowLower := #[0], rowUpper := #[0]
    , colLower := #[1], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- Farkas with bound combination = 0 (not strict): correctly rejected. -/
def tRejectFarkasNotStrict : Outcome :=
  -- Trivial all-zero dual on a feasible LP: satisfies homogeneity but
  -- bound combination is exactly 0.
  let p := mkProblem 1 1
    (c := #[0])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 0, some 1)])
    (colBounds := #[(some 0, none)])
  let d : DualBundle :=
    { rowLower := #[0], rowUpper := #[0]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkInfeasible p d)

/-- Recession ray with `c·r = 0` does not certify unboundedness. -/
def tRejectUnboundedNonStrict : Outcome :=
  let p := mkProblem 1 0
    (c := #[0])                                -- c·r = 0 for any r
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Array Rat := #[0]
  let r : Array Rat := #[1]
  expectFalse (checkUnbounded p x r)

/-- Totality on malformed `Problem`: `colBounds.size ≠ numVars`.
    Without the `problemShapeOk` guard the loop body would index
    `p.colBounds[1]!` and panic. -/
def tTotalityMalformedColBounds : Outcome :=
  let p := mkProblem 2 0
    (c := #[1, 1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(none, none)])              -- size 1, numVars = 2
  let x : Array Rat := #[0, 0]
  let d : DualBundle :=
    { rowLower := #[], rowUpper := #[]
    , colLower := #[0, 0], colUpper := #[0, 0] }
  expectFalse (checkOptimal p x d)

/-- Totality on malformed `Problem`: `rowBounds.size ≠ numConstraints`. -/
def tTotalityMalformedRowBounds : Outcome :=
  let p := mkProblem 1 2
    (c := #[1])
    (a := #[])
    (rowBounds := #[(none, none)])              -- size 1, numConstraints = 2
    (colBounds := #[(none, none)])
  let x : Array Rat := #[0]
  let d : DualBundle :=
    { rowLower := #[0, 0], rowUpper := #[0, 0]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- Totality on out-of-range sparse entry. Without the guard
    `evalAx` / `evalATy` would silently drop the entry and verify a
    *different* LP than the one declared. -/
def tTotalitySparseOutOfRange : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 5, 1)])                          -- col 5 ≥ numVars
    (rowBounds := #[(some 0, some 0)])
    (colBounds := #[(none, none)])
  let x : Array Rat := #[0]
  let d : DualBundle :=
    { rowLower := #[0], rowUpper := #[0]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkOptimal p x d)

/-- Totality on `checkInfeasible` with malformed problem. -/
def tTotalityInfeasibleMalformed : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[])
    (rowBounds := #[(none, none)])
    (colBounds := #[])                          -- size 0, numVars = 1
  let d : DualBundle :=
    { rowLower := #[1], rowUpper := #[0]
    , colLower := #[0], colUpper := #[0] }
  expectFalse (checkInfeasible p d)

/-- Totality on `checkUnbounded` with malformed problem. -/
def tTotalityUnboundedMalformed : Outcome :=
  let p := mkProblem 1 0
    (c := #[1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[])                          -- size 0, numVars = 1
  let x : Array Rat := #[0]
  let r : Array Rat := #[1]
  expectFalse (checkUnbounded p x r)

/-- Totality: a size-mismatched primal is rejected by `checkOptimal`. -/
def tTotalityPrimalSizeMismatch : Outcome :=
  let p := mkProblem 2 0
    (c := #[1, 1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(none, none), (none, none)])
  let x : Array Rat := #[0]                    -- size 1 ≠ numVars 2
  let d : DualBundle :=
    { rowLower := #[], rowUpper := #[]
    , colLower := #[0, 0], colUpper := #[0, 0] }
  expectFalse (checkOptimal p x d)

/-- Totality: a size-mismatched DualBundle is rejected. -/
def tTotalityDualSizeMismatch : Outcome :=
  let p := mkProblem 2 0
    (c := #[1, 1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(none, none), (none, none)])
  let x : Array Rat := #[0, 0]
  let d : DualBundle :=                        -- colLower size 1 ≠ numVars 2
    { rowLower := #[], rowUpper := #[]
    , colLower := #[0], colUpper := #[0, 0] }
  expectFalse (checkOptimal p x d)

/-! ## Driver. -/

def allTests : Array TestCase := #[
  ⟨"validate normalises duplicate / zero entries",  fun _ => tValidateNormalise⟩,
  ⟨"validate sorts sparse entries",                 fun _ => tValidateSort⟩,
  ⟨"validate is idempotent",                        fun _ => tValidateIdempotent⟩,
  ⟨"validate rejects wrong-length c",               fun _ => tRejectWrongLengthC⟩,
  ⟨"validate rejects wrong-length rowBounds",       fun _ => tRejectWrongLengthRowBounds⟩,
  ⟨"validate rejects sparse row out of range",      fun _ => tRejectSparseRowOOR⟩,
  ⟨"validate rejects sparse col out of range",      fun _ => tRejectSparseColOOR⟩,
  ⟨"validate rejects inverted column bound",        fun _ => tRejectInvertedColBound⟩,
  ⟨"checkOptimal: equality LP",                     fun _ => tOptimalEquality⟩,
  ⟨"checkOptimal: ranged-row LP",                   fun _ => tOptimalRangedRow⟩,
  ⟨"checkOptimal: max sense via canonicalize",      fun _ => tOptimalMaxCanonicalized⟩,
  ⟨"checkInfeasible: rows-only Farkas",             fun _ => tInfeasibleRowsOnly⟩,
  ⟨"checkInfeasible: column-bounds-only Farkas",    fun _ => tInfeasibleColBoundsOnly⟩,
  ⟨"checkInfeasible: row + bounds Farkas",          fun _ => tInfeasibleRowAndBounds⟩,
  ⟨"checkUnbounded: simple x ≥ 0",                  fun _ => tUnboundedSimple⟩,
  ⟨"checkUnbounded: with equality row",             fun _ => tUnboundedWithEquality⟩,
  ⟨"checkOptimal rejects infeasible primal",        fun _ => tRejectInfeasiblePrimal⟩,
  ⟨"checkOptimal rejects bad stationarity",         fun _ => tRejectBadStationarity⟩,
  ⟨"checkOptimal rejects ranged-row decomposition", fun _ => tRejectRangedRowDecomposition⟩,
  ⟨"checkOptimal rejects objective mismatch",       fun _ => tRejectObjectiveMismatch⟩,
  ⟨"checkInfeasible rejects non-strict bound sum",  fun _ => tRejectFarkasNotStrict⟩,
  ⟨"checkUnbounded rejects c·r = 0",                fun _ => tRejectUnboundedNonStrict⟩,
  ⟨"totality: primal size mismatch → false",        fun _ => tTotalityPrimalSizeMismatch⟩,
  ⟨"totality: dual size mismatch → false",          fun _ => tTotalityDualSizeMismatch⟩,
  ⟨"totality: malformed colBounds → false",         fun _ => tTotalityMalformedColBounds⟩,
  ⟨"totality: malformed rowBounds → false",         fun _ => tTotalityMalformedRowBounds⟩,
  ⟨"totality: sparse OOR → false",                  fun _ => tTotalitySparseOutOfRange⟩,
  ⟨"totality: checkInfeasible malformed → false",   fun _ => tTotalityInfeasibleMalformed⟩,
  ⟨"totality: checkUnbounded malformed → false",    fun _ => tTotalityUnboundedMalformed⟩
]

def main : IO UInt32 := do
  let mut failed : Nat := 0
  for t in allTests do
    match t.outcome () with
    | .ok =>
      IO.println s!"[ok]   {t.name}"
    | .fail msg =>
      failed := failed + 1
      IO.println s!"[FAIL] {t.name}: {msg}"
  let total := allTests.size
  if failed = 0 then
    IO.println s!"All {total} verifier tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {total} verifier tests FAILED."
    return 1
