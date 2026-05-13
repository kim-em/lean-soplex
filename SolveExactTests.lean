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

private def solveChecked {m n : Nat} (opts : Options) (p : Problem m n)
    (k : Problem m n → Solution m n → Outcome) : Outcome :=
  match validate p with
  | .error e => .fail s!"validate failed: {repr e}"
  | .ok p' =>
    match solveExact opts p with
    | .error e => .fail s!"solveExact failed: {repr e}"
    | .ok s => k (canonicalize opts.sense p') s

private def tOptimalEquality (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.primal, s.certificate.dual, s.objective with
    | .optimal, some x, some d, some obj =>
      expect (obj == 1 && checkOptimal p' x d)
        s!"bad optimal cert: obj={repr obj}, x={repr x}, d={repr d}"
    | _, _, _, _ => .fail s!"unexpected solution: {repr s}"

private def tRangedRow (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 1, some 3)])
    (colBounds := #[(some 0, some 2)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.primal, s.certificate.dual with
    | .optimal, some x, some d =>
      expect (x.toArray == #[1] && checkOptimal p' x d)
        s!"bad ranged-row cert: x={repr x}, d={repr d}"
    | _, _, _ => .fail s!"unexpected solution: {repr s}"

private def tInfeasibleRowsOnly (_ : Unit) : Outcome :=
  let p := mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.dual with
    | .infeasible, some d =>
      expect (checkInfeasible p' d) s!"bad Farkas cert: {repr d}"
    | _, _ => .fail s!"unexpected solution: {repr s}"

private def tInfeasibleRowAndBounds (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[0])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some 2, none)])
    (colBounds := #[(some 0, some 1)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.dual with
    | .infeasible, some d =>
      expect (checkInfeasible p' d) s!"bad row/bounds Farkas cert: {repr d}"
    | _, _ => .fail s!"unexpected solution: {repr s}"

private def tUnbounded (_ : Unit) : Outcome :=
  let p := mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.primal, s.certificate.ray with
    | .unbounded, some x, some r =>
      expect (checkUnbounded p' x r) s!"bad unbounded cert: x={repr x}, ray={repr r}"
    | _, _, _ => .fail s!"unexpected solution: {repr s}"

private def tDuplicateAndBigRat (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[1234567890123456789])
    (a := #[(0, 0, 1/3), (0, 0, 2/3)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none)])
  solveChecked noPresolve p fun p' s =>
    match s.status, s.certificate.primal, s.certificate.dual with
    | .optimal, some x, some d =>
      expect (x.toArray == #[1] && checkOptimal p' x d)
        s!"bad duplicate/big-rat cert: x={repr x}, d={repr d}"
    | _, _, _ => .fail s!"unexpected solution: {repr s}"

private def tVerboseLogCaptured (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  let opts := { noPresolve with verbose := true }
  match solveExact opts p with
  | .error e => .fail s!"solveExact failed: {repr e}"
  | .ok s =>
    -- Verbose mode must produce a non-empty log containing a recognisable
    -- SoPlex signature substring. `"SoPlex"` (the banner / version line)
    -- and `"Optimal"` (the optimization-summary marker) are both stable
    -- across v8.0.x; either is accepted. `splitOn s` returns at least
    -- two pieces iff `s` occurs as a substring.
    let containsSub (needle : String) : Bool := (s.log.splitOn needle).length ≥ 2
    let hasSig := containsSub "SoPlex" || containsSub "Optimal"
    expect (s.log.length > 0 && hasSig)
      s!"verbose log empty or missing SoPlex signature: {s.log}"

private def tNonVerboseLogEmpty (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  solveChecked noPresolve p fun _ s =>
    expect (s.log == "") s!"non-verbose log non-empty: {s.log}"

private def tMaximize (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(none, some 1)])
    (colBounds := #[(some 0, none)])
  let opts := { noPresolve with sense := .maximize }
  solveChecked opts p fun p' s =>
    match s.status, s.certificate.primal, s.certificate.dual, s.objective with
    | .optimal, some x, some d, some obj =>
      expect (obj == 1 && x.toArray == #[1] && checkOptimal p' x d)
        s!"bad max cert: obj={repr obj}, x={repr x}, d={repr d}"
    | _, _, _, _ => .fail s!"unexpected solution: {repr s}"

def allTests : Array TestCase := #[
  ⟨"optimal equality", tOptimalEquality⟩,
  ⟨"optimal ranged row", tRangedRow⟩,
  ⟨"infeasible rows only", tInfeasibleRowsOnly⟩,
  ⟨"infeasible row and bounds", tInfeasibleRowAndBounds⟩,
  ⟨"unbounded", tUnbounded⟩,
  ⟨"duplicate sparse entries and big rationals", tDuplicateAndBigRat⟩,
  ⟨"maximization canonicalization", tMaximize⟩,
  ⟨"verbose log captured", tVerboseLogCaptured⟩,
  ⟨"non-verbose log empty", tNonVerboseLogEmpty⟩
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
    IO.println s!"All {allTests.size} solveExact tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {allTests.size} solveExact tests FAILED."
    return 1
