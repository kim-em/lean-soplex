import LeanSoplex

open LeanSoplex LeanSoplex.Verify

inductive Outcome
  | ok
  | fail (msg : String)

structure TestCase where
  name : String
  run : Unit → Outcome

private def expect (b : Bool) (msg : String) : Outcome :=
  if b then .ok else .fail msg

private def mkProblem
    (numVars numConstraints : Nat)
    (c : Array Rat)
    (a : Array (Nat × Nat × Rat))
    (rowBounds : Array (Option Rat × Option Rat))
    (colBounds : Array (Option Rat × Option Rat))
    (objOffset : Rat := 0)
    (hc : c.size = numVars := by decide)
    (hRB : rowBounds.size = numConstraints := by decide)
    (hCB : colBounds.size = numVars := by decide) :
    Problem numConstraints numVars :=
  { c := ⟨c, hc⟩, a, rowBounds := ⟨rowBounds, hRB⟩,
    colBounds := ⟨colBounds, hCB⟩, objOffset }

private def noPresolve : Options :=
  { ({} : Options) with presolve := false, verbose := false, precisionBoost := false }

private def toyProblem : Problem 1 2 :=
  mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])

/-- Optimal LP: `min x + y  s.t.  x + y = 1, x, y ≥ 0`. The exact-mode
    answer is `obj = 1`. Float-mode must agree to within double precision. -/
private def tOptimalEquality (_ : Unit) : Outcome :=
  match solveFloat noPresolve toyProblem with
  | .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok s =>
    match s.status, s.primalAsRat, s.objective with
    | .optimal, some x, some obj =>
      expect ((obj - 1.0).abs < 1e-9 && x.size = 2)
        s!"bad optimal float result: obj={obj}, x={repr x}"
    | _, _, _ => .fail s!"unexpected solution: {repr s}"

/-- Infeasible LP: `x ≥ 1 ∧ x ≤ 0` via two rows. SoPlex should detect
    infeasibility in float mode too. -/
private def tInfeasibleRows (_ : Unit) : Outcome :=
  let p := mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])
  match solveFloat noPresolve p with
  | .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok s => expect (s.status = .infeasible) s!"expected infeasible, got: {repr s}"

/-- Power of two as a positive natural. -/
private partial def isPow2 (n : Nat) : Bool :=
  if n = 0 then false
  else if n = 1 then true
  else if n % 2 = 0 then isPow2 (n / 2)
  else false

/-- `0.1`-binary check: feeding the equality bound `x = 0.1` lets us
    read back what the bridge produced for SoPlex's float-mode primal.
    The point of this test is to verify the bridge uses the exact
    IEEE-754 → `Rat` conversion (`mpq_set_d`) rather than parsing the
    decimal `0.1` as `1/10`.

    Discriminator: the canonical denominator of `mpq_set_d` on any
    finite double is always a power of two (since IEEE-754 doubles
    are `m · 2^e`). A decimal parser would land on `1/10` with
    denominator `10`. SoPlex's float-mode primal may drift by an ULP
    from the bound, so we don't check the value exactly — only the
    denominator's shape. -/
private def tBinaryRoundTrip (_ : Unit) : Outcome :=
  let pointOne : Rat := mkRat 1 10
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some pointOne, some pointOne)])
    (colBounds := #[(none, none)])
  match solveFloat noPresolve p with
  | .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok s =>
    match s.status, s.primalAsRat with
    | .optimal, some x =>
      if h : x.size = 1 then
        let xq : Rat := x[0]'(by simp)
        -- A decimal parser would have produced `1/10` (denominator 10);
        -- `mpq_set_d` always produces a power-of-two denominator. The
        -- numerator should also be close to `0.1 · 2^k` for the
        -- denominator `2^k` — we check it's within one ULP of the
        -- canonical `7205759403792794 / 2^56 = 3602879701896397 / 2^55`.
        let denOk := isPow2 xq.den
        -- 2^55 ≈ 3.6e16; |xq − 1/10| ≤ 1 / 2^55 confirms one-ULP proximity.
        let diff : Rat := xq - mkRat 1 10
        let absDiff : Rat := if diff < 0 then -diff else diff
        let tol : Rat := mkRat 1 (2 ^ 50)  -- generous: ≈ 1e-15
        let valOk : Bool := absDiff < tol
        expect (denOk && valOk)
          (s!"binary round-trip failed: xq={xq}, denOk={denOk}, " ++
           s!"valOk={valOk} (|xq - 1/10| = {absDiff}); " ++
           s!"a decimal parser would produce {pointOne}")
      else
        .fail s!"expected primal length 1, got {x.size}"
    | _, _ => .fail s!"unexpected solution: {repr s}"

/-- Maximization: `max x  s.t.  x ≤ 2, x ≥ 0`. Confirms the sense flip
    on the float objective mirrors `solveExact`. -/
private def tMaximize (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(none, some 2)])
    (colBounds := #[(some 0, none)])
  let opts := { noPresolve with sense := .maximize }
  match solveFloat opts p with
  | .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok s =>
    match s.status, s.objective with
    | .optimal, some obj =>
      expect ((obj - 2.0).abs < 1e-9) s!"bad maximize float result: obj={obj}"
    | _, _ => .fail s!"unexpected solution: {repr s}"

/-- Verbose float-mode solves should carry the same captured SoPlex log
    contract as exact-mode solves. -/
private def tVerboseLog (_ : Unit) : Outcome :=
  let opts := { noPresolve with verbose := true }
  match solveFloat opts toyProblem with
  | .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok s =>
    expect (s.log.length > 0)
      "expected nonempty verbose log from solveFloat"

/-- FFI-facing options reject values that cannot be represented by the
    C++ `int` API before narrowing happens. -/
private def tIterLimitTooLarge (_ : Unit) : Outcome :=
  let opts := { noPresolve with iterLimit := some 2147483648 }
  match solveFloat opts toyProblem with
  | .error (.invalidOptions (.iterLimitTooLarge _ _)) => .ok
  | .error e => .fail s!"expected iterLimitTooLarge, got {repr e}"
  | .ok s => .fail s!"expected iterLimitTooLarge, got solution {repr s}"

def allTests : Array TestCase := #[
  ⟨"optimal equality", tOptimalEquality⟩,
  ⟨"infeasible rows", tInfeasibleRows⟩,
  ⟨"binary round-trip of 0.1", tBinaryRoundTrip⟩,
  ⟨"maximize", tMaximize⟩,
  ⟨"verbose log", tVerboseLog⟩,
  ⟨"oversized iterLimit rejected", tIterLimitTooLarge⟩
]

def main : IO UInt32 := do
  let mut failed := 0
  for t in allTests do
    match t.run () with
    | .ok => IO.println s!"[ok]   {t.name}"
    | .fail msg =>
      failed := failed + 1
      IO.println s!"[FAIL] {t.name}: {msg}"
  if failed = 0 then
    IO.println s!"All {allTests.size} solveFloat tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {allTests.size} solveFloat tests FAILED."
    return 1
