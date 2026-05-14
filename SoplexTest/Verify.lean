/-
  Hand-rolled tests for the pure-Lean certificate checker. Exercises
  `validate`, `checkOptimal`, `checkInfeasible`, `checkUnbounded` and
  the supporting `is*` Booleans on small LPs with known answers, using
  hand-rolled tiny certificates.
-/

import SoplexTest.Common

open Soplex Soplex.Verify SoplexTest

@[inline] private def expectTrue (cond : Bool) : Outcome :=
  expect cond "expected true, got false"

@[inline] private def expectFalse (cond : Bool) : Outcome :=
  expect (!cond) "expected false, got true"

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
      let expected : Array (Fin 2 × Fin 2 × Rat) :=
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

def tRejectSparseRowOOR : Outcome :=
  let p : RawProblem 1 1 :=
  { c := ⟨#[1], by decide⟩
    a := #[(5, 0, 1)]                      -- row 5 ≥ numConstraints
    rowBounds := ⟨#[(none, none)], by decide⟩
    colBounds := ⟨#[(none, none)], by decide⟩ }
  match validateRaw p with
  | .error (.indexOutOfRange .row 5 1) => .ok
  | .error e => .fail s!"wrong error: {repr e}"
  | .ok _ => .fail "expected error"

def tRejectSparseColOOR : Outcome :=
  let p : RawProblem 1 1 :=
  { c := ⟨#[1], by decide⟩
    a := #[(0, 7, 1)]                      -- col 7 ≥ numVars
    rowBounds := ⟨#[(none, none)], by decide⟩
    colBounds := ⟨#[(none, none)], by decide⟩ }
  match validateRaw p with
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
  let x : Vector Rat 2 := #v[0, 1]
  let d : DualBundle _ _ :=
    { rowLower := #v[1], rowUpper := #v[0]
    , colLower := #v[0, 0], colUpper := #v[0, 0] }
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
  let x : Vector Rat 1 := #v[1]
  let d : DualBundle _ _ :=
    { rowLower := #v[1], rowUpper := #v[0]
    , colLower := #v[0], colUpper := #v[0] }
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
  let x : Vector Rat 2 := #v[1/2, 1/2]
  let d : DualBundle _ _ :=
    { rowLower := #v[0], rowUpper := #v[1]
    , colLower := #v[0, 0], colUpper := #v[0, 0] }
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
  let d : DualBundle _ _ :=
    { rowLower := #v[1, 0], rowUpper := #v[0, 1]
    , colLower := #v[0], colUpper := #v[0] }
  expectTrue (checkInfeasible p d)

/-- Raw Bool-checker stress test (the LP itself fails `validate` —
    `0 ≤ x ≤ -1` is an inverted column bound, which `validate` rejects
    as `boundInverted` long before the checker would run). Constructs
    the four-vector Farkas form directly
    against the unvalidated `Problem`, to pin the sign convention for
    column-bounds-only infeasibility. In the `validate → solveExact →
    checkInfeasible` pipeline this case never arises — infeasibility
    that reaches the checker must include at least one row, since
    `validate` rejects any inverted bound first. Farkas: `zL = [1],
    zU = [1]`. Stationarity `zL − zU = 0`, bound combination
    `1·0 - 1·(-1) = 1 > 0`. -/
def tInfeasibleColBoundsOnly : Outcome :=
  let p : Problem 0 1 :=
    { c := #v[0], objOffset := 0
    , a := #[], rowBounds := #v[]
    , colBounds := #v[(some 0, some (-1))] }
  let d : DualBundle _ _ :=
    { rowLower := #v[], rowUpper := #v[]
    , colLower := #v[1], colUpper := #v[1] }
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
  let d : DualBundle _ _ :=
    { rowLower := #v[1], rowUpper := #v[0]
    , colLower := #v[0], colUpper := #v[1] }
  expectTrue (checkInfeasible p d)

/-! ## `checkUnbounded` — positive cases. -/

/-- `min -x  s.t.  x ≥ 0`. Base `x = (0)`, ray `r = (1)`. -/
def tUnboundedSimple : Outcome :=
  let p := mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Vector Rat 1 := #v[0]
  let r : Vector Rat 1 := #v[1]
  expectTrue (checkUnbounded p x r)

/-- `min -x  s.t.  x - y = 0, x ≥ 0` (y free). Base `(0,0)`, ray
    `(1,1)`. Equality row collapses to `(Ar)₀ = 0`. -/
def tUnboundedWithEquality : Outcome :=
  let p := mkProblem 2 1
    (c := #[-1, 0])
    (a := #[(0, 0, 1), (0, 1, -1)])
    (rowBounds := #[(some 0, some 0)])
    (colBounds := #[(some 0, none), (none, none)])
  let x : Vector Rat 2 := #v[0, 0]
  let r : Vector Rat 2 := #v[1, 1]
  expectTrue (checkUnbounded p x r)

/-! ## Negative cases — `check*` correctly rejects bad certificates. -/

/-- Primal violates the column lower bound. -/
def tRejectInfeasiblePrimal : Outcome :=
  let p := mkProblem 1 0
    (c := #[1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Vector Rat 1 := #v[-1]              -- below lower bound
  let d : DualBundle _ _ :=
    { rowLower := #v[], rowUpper := #v[]
    , colLower := #v[1], colUpper := #v[0] }
  expectFalse (checkOptimal p x d)

/-- Stationarity off by sign: pick a `d` that satisfies everything else
    but has `Aᵀ(yL−yU) + (zL−zU) = -c` instead of `c`. -/
def tRejectBadStationarity : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none)])
  let x : Vector Rat 1 := #v[1]
  let d : DualBundle _ _ :=                       -- yL=0,yU=1 gives -1
    { rowLower := #v[0], rowUpper := #v[1]
    , colLower := #v[0], colUpper := #v[0] }
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
  let x : Vector Rat 1 := #v[1]
  let d : DualBundle _ _ :=
    { rowLower := #v[2], rowUpper := #v[1]
    , colLower := #v[0], colUpper := #v[0] }
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
  let x : Vector Rat 1 := #v[1]
  let d : DualBundle _ _ :=
    { rowLower := #v[0], rowUpper := #v[0]
    , colLower := #v[1], colUpper := #v[0] }
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
  let d : DualBundle _ _ :=
    { rowLower := #v[0], rowUpper := #v[0]
    , colLower := #v[0], colUpper := #v[0] }
  expectFalse (checkInfeasible p d)

/-- Recession ray with `c·r = 0` does not certify unboundedness. -/
def tRejectUnboundedNonStrict : Outcome :=
  let p := mkProblem 1 0
    (c := #[0])                                -- c·r = 0 for any r
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  let x : Vector Rat 1 := #v[0]
  let r : Vector Rat 1 := #v[1]
  expectFalse (checkUnbounded p x r)

/-! ## Denominator-budget check. -/

/-- A representative small certificate: single-digit numerators and
    denominators throughout. `Rat.bitLen` is at most a handful of bits
    on every coordinate, so a budget of `10000` is wildly generous. -/
private def smallCertificate : Certificate 2 3 :=
  { primal := some #v[(1 : Rat) / 2, 3, -7 / 4]
    dual := some
      { rowLower := #v[0, 1]
        rowUpper := #v[0, 0]
        colLower := #v[(2 : Rat) / 3, 0, 0]
        colUpper := #v[0, 0, 0] }
    ray := none }

def tBudgetSmallPasses : Outcome :=
  expectTrue (certificateWithinBudget (some 10000) smallCertificate)

def tBudgetNoneAlwaysPasses : Outcome :=
  expectTrue (certificateWithinBudget none smallCertificate)

/-- A certificate with a hand-constructed large rational. `1234567 / 89`
    is reduced (1234567 is not divisible by 89) with combined bit length
    21 + 7 = 28, well over the budget of 5. -/
def tBudgetLargeRejected : Outcome :=
  let big : Rat := (1234567 : Rat) / 89
  let cert : Certificate 0 1 :=
    { primal := some #v[big], dual := none, ray := none }
  expectFalse (certificateWithinBudget (some 5) cert)

/-- Pin the `Rat.bitLen` convention: zero has `num = 0` and `den = 1`,
    so the formula gives `0 + 1 = 1`. Integers always pick up the
    `den = 1` bit. -/
def tBudgetBitLenConvention : Outcome :=
  let r0 : Rat := 0
  let r1 : Rat := 1
  let r3 : Rat := 3
  let rNeg : Rat := -7 / 4
  expect (r0.bitLen = 1 && r1.bitLen = 2 && r3.bitLen = 3 && rNeg.bitLen = 6)
    s!"Rat.bitLen pins: 0→{r0.bitLen} 1→{r1.bitLen} 3→{r3.bitLen} -7/4→{rNeg.bitLen}"

/-! ## Driver. -/

def allTests : Array TestCase := #[
  ⟨"validate normalises duplicate / zero entries",  pure tValidateNormalise⟩,
  ⟨"validate sorts sparse entries",                 pure tValidateSort⟩,
  ⟨"validate is idempotent",                        pure tValidateIdempotent⟩,
  ⟨"validate rejects sparse row out of range",      pure tRejectSparseRowOOR⟩,
  ⟨"validate rejects sparse col out of range",      pure tRejectSparseColOOR⟩,
  ⟨"validate rejects inverted column bound",        pure tRejectInvertedColBound⟩,
  ⟨"checkOptimal: equality LP",                     pure tOptimalEquality⟩,
  ⟨"checkOptimal: ranged-row LP",                   pure tOptimalRangedRow⟩,
  ⟨"checkOptimal: max sense via canonicalize",      pure tOptimalMaxCanonicalized⟩,
  ⟨"checkInfeasible: rows-only Farkas",             pure tInfeasibleRowsOnly⟩,
  ⟨"checkInfeasible: column-bounds-only Farkas",    pure tInfeasibleColBoundsOnly⟩,
  ⟨"checkInfeasible: row + bounds Farkas",          pure tInfeasibleRowAndBounds⟩,
  ⟨"checkUnbounded: simple x ≥ 0",                  pure tUnboundedSimple⟩,
  ⟨"checkUnbounded: with equality row",             pure tUnboundedWithEquality⟩,
  ⟨"checkOptimal rejects infeasible primal",        pure tRejectInfeasiblePrimal⟩,
  ⟨"checkOptimal rejects bad stationarity",         pure tRejectBadStationarity⟩,
  ⟨"checkOptimal rejects ranged-row decomposition", pure tRejectRangedRowDecomposition⟩,
  ⟨"checkOptimal rejects objective mismatch",       pure tRejectObjectiveMismatch⟩,
  ⟨"checkInfeasible rejects non-strict bound sum",  pure tRejectFarkasNotStrict⟩,
  ⟨"checkUnbounded rejects c·r = 0",                pure tRejectUnboundedNonStrict⟩,
  ⟨"budget: small certificate within 10000",        pure tBudgetSmallPasses⟩,
  ⟨"budget: none disables the check",               pure tBudgetNoneAlwaysPasses⟩,
  ⟨"budget: large rationals rejected at 5",         pure tBudgetLargeRejected⟩,
  ⟨"budget: Rat.bitLen convention pinning",         pure tBudgetBitLenConvention⟩
]

def main : IO UInt32 := runAll "verifier" allTests
