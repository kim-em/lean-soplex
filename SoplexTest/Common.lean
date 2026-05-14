/-
  Shared scaffolding for the `SoplexTest/` executables. Imports only
  `Soplex.Verify`; anything that needs `Options` / `Soplex.Basic` lives
  in `SoplexTest/SolveCommon.lean`.
-/

import Soplex.Verify

namespace SoplexTest

open Soplex Soplex.Verify

inductive Outcome
  | ok
  | fail (msg : String)

instance : Inhabited Outcome := ⟨.ok⟩

@[inline] def expect (b : Bool) (msg : String) : Outcome :=
  if b then .ok else .fail msg

/-- Problem builder: takes arrays plus size hypotheses
    (which `decide` discharges automatically for literal-shape inputs)
    and packages them as a typed `Problem numConstraints numVars`. -/
def mkProblem
    (numVars numConstraints : Nat)
    (c : Array Rat)
    (a : Array (Fin numConstraints × Fin numVars × Rat))
    (rowBounds : Array (Option Rat × Option Rat))
    (colBounds : Array (Option Rat × Option Rat))
    (objOffset : Rat := 0)
    (hc : c.size = numVars := by decide)
    (hRB : rowBounds.size = numConstraints := by decide)
    (hCB : colBounds.size = numVars := by decide) :
    Problem numConstraints numVars :=
  { c := ⟨c, hc⟩, a, rowBounds := ⟨rowBounds, hRB⟩,
    colBounds := ⟨colBounds, hCB⟩, objOffset }

def sparseVals {m n : Nat} (a : Array (Fin m × Fin n × Rat)) :
    Array (Nat × Nat × Rat) :=
  a.map fun e => (e.1.val, e.2.1.val, e.2.2)

/-- A single named test. `run` is `IO`-bound so the same scaffolding
    handles pure tests and file-I/O tests; wrap pure tests via
    `TestCase.ofPure`. -/
structure TestCase where
  name : String
  run  : IO Outcome

/-- Wrap a pure `Unit → Outcome` test as an `IO`-bound `TestCase`. -/
@[inline] def TestCase.ofPure (name : String) (f : Unit → Outcome) : TestCase :=
  ⟨name, pure (f ())⟩

/-- Run every `TestCase`, print `[ok]` / `[FAIL]` per case, and return
    `0` on a clean sweep, `1` otherwise. `label` is the suite name used
    in the summary line. -/
def runAll (label : String) (cases : Array TestCase) : IO UInt32 := do
  let mut failed := 0
  for t in cases do
    match (← t.run) with
    | .ok        => IO.println s!"[ok]   {t.name}"
    | .fail msg  =>
      failed := failed + 1
      IO.println s!"[FAIL] {t.name}: {msg}"
  if failed = 0 then
    IO.println s!"All {cases.size} {label} tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {cases.size} {label} tests FAILED."
    return 1

end SoplexTest
