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

private def bigBase : Nat := 2 ^ 60

private def exactRhs : Rat := (bigBase : Rat) + 1

/-- `2^60 + 1` is not representable as an IEEE-754 double: spacing at
    this scale is much larger than one. Float-mode therefore solves the
    equality with a rounded RHS, while exact-mode verifies the original
    rational value. -/
private def roundedRhsProblem : Problem 1 1 :=
  mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(some exactRhs, some exactRhs)])
    (colBounds := #[(none, none)])

private def absRat (q : Rat) : Rat :=
  if q < 0 then -q else q

private def tFloatRoundsButExactVerifies (_ : Unit) : Outcome :=
  let p := roundedRhsProblem
  match solveFloat noPresolve p, solveExact noPresolve p, solveVerified noPresolve p with
  | .ok fs, .ok es, .ok vs =>
    match fs.status, fs.primalAsRat, es.status, es.objective, es.certificate.primal,
        es.certificate.dual, vs.verified with
    | .optimal, some fx, .optimal, some exactObj, some ex, some d, .optimal vx h =>
      if hfx : fx.size = 1 then
        if hex : ex.size = 1 then
          let fx0 := fx[0]'(by simp)
          let ex0 := ex[0]'(by simp)
          let gap := absRat (exactObj - fx0)
          let _ : IsFeasible vs.normalized vx.toArray ∧
              IsOptimal vs.normalized noPresolve.sense vx.toArray := h
          expect
            (exactObj = exactRhs &&
             ex0 = exactRhs &&
             vx.toArray = #[exactRhs] &&
             checkOptimal (canonicalize noPresolve.sense vs.normalized) ex d &&
             gap > (1 : Rat) / 10)
            (s!"expected exact RHS and float gap > 0.1; " ++
             s!"float={fx0}, exactObj={exactObj}, exactPrimal={ex0}, gap={gap}")
        else
          .fail s!"exact primal has wrong length: {ex.size}"
      else
        .fail s!"float primal has wrong length: {fx.size}"
    | _, _, _, _, _, _, _ =>
      .fail s!"unexpected results:\nfloat={repr fs}\nexact={repr es}"
  | .error e, _, _ => .fail s!"solveFloat failed: {repr e}"
  | _, .error e, _ => .fail s!"solveExact failed: {repr e}"
  | _, _, .error e => .fail s!"solveVerified failed: {repr e}"

def allTests : Array TestCase := #[
  ⟨"float rounding diverges from exact verified solve", tFloatRoundsButExactVerifies⟩
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
    IO.println s!"All {allTests.size} solve-compare tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {allTests.size} solve-compare tests FAILED."
    return 1
