/-
  End-to-end tests for `solveVerified`. Each test drives a real
  SoPlex solve and pattern-matches on the returned `Verified` to
  prove (literally — the `h` field is a real soundness-lemma
  proof) optimality / infeasibility / unboundedness.
-/
import LeanSoplex

open LeanSoplex LeanSoplex.Verify

inductive Outcome
  | ok
  | fail (msg : String)

structure TestCase where
  name : String
  run  : Unit → Outcome

private def expect (b : Bool) (msg : String) : Outcome :=
  if b then .ok else .fail msg

private def mkProblem
    (numVars numConstraints : Nat)
    (c : Array Rat)
    (a : Array (Nat × Nat × Rat))
    (rowBounds : Array (Option Rat × Option Rat))
    (colBounds : Array (Option Rat × Option Rat))
    (objOffset : Rat := 0) : Problem :=
  { numVars, numConstraints, c, a, rowBounds, colBounds, objOffset }

private def baseOpts : Options :=
  { ({} : Options) with presolve := false, verbose := false, precisionBoost := false }

/-! ## Witnesses extracted from `Verified` constructors.

  These `wantsX` helpers do the pattern-matching the issue demands:
  on a real soundness proof the constructors deliver the matching
  `Verified.optimal`/`.infeasible`/`.unbounded` and we extract the
  primal / ray data alongside the proof. -/

private def wantsOptimal {p : Problem} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal x h =>
      -- The match binding `h` confirms the proof exists; we also
      -- verify the primal vector has the right shape.
      let _ : IsFeasible p x ∧ IsOptimal p sense x := h
      expect (x.size = p.numVars) s!"optimal x has wrong size: {repr x}"
  | .infeasible _ => .fail "expected optimal, got infeasible"
  | .unbounded .. => .fail "expected optimal, got unbounded"
  | .unchecked s  => .fail s!"expected optimal, got unchecked {repr s}"

private def wantsInfeasible {p : Problem} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..   => .fail "expected infeasible, got optimal"
  | .infeasible h =>
      let _ : IsInfeasible p := h
      .ok
  | .unbounded .. => .fail "expected infeasible, got unbounded"
  | .unchecked s  => .fail s!"expected infeasible, got unchecked {repr s}"

private def wantsUnbounded {p : Problem} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..       => .fail "expected unbounded, got optimal"
  | .infeasible _     => .fail "expected unbounded, got infeasible"
  | .unbounded x r h  =>
      let _ : IsUnbounded p sense := h
      expect (x.size = p.numVars && r.size = p.numVars)
        s!"unbounded shapes off: x={repr x}, ray={repr r}"
  | .unchecked s      => .fail s!"expected unbounded, got unchecked {repr s}"

private def wantsUnchecked (expected : SolveStatus)
    {p : Problem} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..    => .fail s!"expected unchecked {repr expected}, got optimal"
  | .infeasible _  => .fail s!"expected unchecked {repr expected}, got infeasible"
  | .unbounded ..  => .fail s!"expected unchecked {repr expected}, got unbounded"
  | .unchecked s   =>
      expect (s = expected)
        s!"unchecked status mismatch: got {repr s}, wanted {repr expected}"

private def runVerified (opts : Options) (p : Problem)
    (denomBudget : Option Nat := some 10000)
    (k : ∀ (norm : Problem), Verified norm opts.sense → Outcome) : Outcome :=
  match solveVerified opts p denomBudget with
  | .error e => .fail s!"solveVerified failed: {repr e}"
  | .ok r    => k r.normalized r.verified

/-! ## Tests. -/

private def tOptimal (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  runVerified baseOpts p (k := fun _ v => wantsOptimal v)

private def tInfeasible (_ : Unit) : Outcome :=
  let p := mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])
  runVerified baseOpts p (k := fun _ v => wantsInfeasible v)

private def tUnbounded (_ : Unit) : Outcome :=
  let p := mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  runVerified baseOpts p (k := fun _ v => wantsUnbounded v)

/-- Maximization. Crucially, the `Verified.optimal` constructor here
    carries `IsOptimal p .maximize x`, which unfolds to
    `IsOptimalMin (negateObjective p) x`. Pattern-matching to extract
    that proof shape is the actual contract the issue asks us to
    pin. -/
private def tMaximize (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(none, some 1)])
    (colBounds := #[(some 0, none)])
  let opts := { baseOpts with sense := .maximize }
  runVerified opts p (k := fun norm v =>
    match v with
    | .optimal x h =>
        let _ : IsOptimal norm .maximize x := h.2
        expect (x = #[1]) s!"bad max primal: {repr x}"
    | _ => .fail "expected .maximize Verified.optimal")

/-- A budget of `1` rejects every certificate carrying a non-zero
    rational: the optimum `x = 1` has bit length 2, well over the cap.
    The driver short-circuits to `.unchecked .budgetExceeded` before
    any `check*` runs. -/
private def tBudgetExceeded (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  runVerified baseOpts p (denomBudget := some 1)
    (k := fun _ v => wantsUnchecked .budgetExceeded v)

/-- Budget regression from issue #20 / PLAN.md §"Test corpus": a tiny
    LP solved with the absurdly low cap `some 5`. The optimum is the
    integer vertex `x = 100` (`bitLen 100 + bitLen 1 = 7 + 1 = 8`),
    over the 5-bit cap, so the budget-check short-circuits to
    `.budgetExceeded` before any `check*` runs. -/
private def tBudget5Exceeded (_ : Unit) : Outcome :=
  -- `min -x  s.t. x ≤ 100, x ≥ 0`. Optimum x = 100, obj = -100.
  let p := mkProblem 1 1
    (c := #[-1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(none, some 100)])
    (colBounds := #[(some 0, none)])
  runVerified baseOpts p (denomBudget := some 5)
    (k := fun _ v => wantsUnchecked .budgetExceeded v)

/-- Companion to `tBudget5Exceeded`: the *same* LP under the default
    budget (`defaultDenomBudget = some 10000`) clears comfortably and
    the driver returns a real `Verified.optimal` carrying the soundness
    proof. Pairing the two tests pins both directions of the budget
    contract: tight budgets reject, defaults accept. -/
private def tDefaultBudgetPasses (_ : Unit) : Outcome :=
  let p := mkProblem 1 1
    (c := #[-1])
    (a := #[(0, 0, 1)])
    (rowBounds := #[(none, some 100)])
    (colBounds := #[(some 0, none)])
  match solveVerified baseOpts p with
  | .error e => .fail s!"solveVerified failed: {repr e}"
  | .ok r    => wantsOptimal r.verified

/-- `denomBudget = none` disables the check and the optimal solve
    completes normally — pinned here to make sure the option really
    is a kill switch and not a "use this default" placeholder. -/
private def tBudgetNoneDisables (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1, 1])
    (a := #[(0, 0, 1), (0, 1, 1)])
    (rowBounds := #[(some 1, some 1)])
    (colBounds := #[(some 0, none), (some 0, none)])
  runVerified baseOpts p (denomBudget := none)
    (k := fun _ v => wantsOptimal v)

/-- `solveVerified` rejects malformed `Problem` values up front,
    before any FFI call. The error is `invalidProblem`, not a
    `bridge`/`unchecked`. -/
private def tInvalidProblem (_ : Unit) : Outcome :=
  let p := mkProblem 2 1
    (c := #[1])                       -- wrong length: expected 2
    (a := #[])
    (rowBounds := #[(some 0, none)])
    (colBounds := #[(some 0, none), (some 0, none)])
  match solveVerified baseOpts p with
  | .error (.invalidProblem _) => .ok
  | .error e => .fail s!"expected invalidProblem, got {repr e}"
  | .ok _ => .fail "expected invalidProblem error, got Ok"

/-! ## Pure `verifyOutcome` tests.

  Exercise failure paths that are hard to drive end-to-end through
  `solveVerified` by feeding `verifyOutcome` a hand-built `Solution`
  directly. -/

private def trivialProblem : Problem :=
  mkProblem 1 0 (c := #[0]) (a := #[]) (rowBounds := #[])
    (colBounds := #[(some 0, none)])

private def emptyCert : Certificate :=
  { primal := none, dual := none, ray := none }

/-- `.optimal` status with no primal certificate: missing-field path. -/
private def tMissingCertOptimal (_ : Unit) : Outcome :=
  let sol : Solution :=
    { status := .optimal, objective := none, certificate := emptyCert, log := "" }
  let v := verifyOutcome baseOpts none trivialProblem sol
  wantsUnchecked .optimal v

/-- `.infeasible` status with no dual certificate. -/
private def tMissingCertInfeasible (_ : Unit) : Outcome :=
  let sol : Solution :=
    { status := .infeasible, objective := none, certificate := emptyCert, log := "" }
  let v := verifyOutcome baseOpts none trivialProblem sol
  wantsUnchecked .infeasible v

/-- `.unbounded` status with no ray. -/
private def tMissingCertUnbounded (_ : Unit) : Outcome :=
  let sol : Solution :=
    { status := .unbounded, objective := none
      certificate := { primal := some #[0], dual := none, ray := none }
      log := "" }
  let v := verifyOutcome baseOpts none trivialProblem sol
  wantsUnchecked .unbounded v

/-- Primal infeasible for `trivialProblem`'s `0 ≤ x` bound, so
    `checkOptimal` rejects. The driver returns `.unchecked .optimal`
    rather than fabricating a proof. -/
private def tFailedCheckOptimal (_ : Unit) : Outcome :=
  let bogusDual : DualBundle :=
    { rowLower := #[], rowUpper := #[]
      colLower := #[0], colUpper := #[0] }
  let sol : Solution :=
    { status := .optimal, objective := none
      certificate := { primal := some #[-1], dual := some bogusDual, ray := none }
      log := "" }
  let v := verifyOutcome baseOpts none trivialProblem sol
  wantsUnchecked .optimal v

/-- Non-terminal statuses pass straight through to `.unchecked status`,
    even when the certificate happens to be over budget — the budget
    check only runs when the status is terminal, not unconditionally. -/
private def tNonTerminalPreservesStatus (_ : Unit) : Outcome :=
  let sol : Solution :=
    { status := .timeLimit, objective := none
      certificate := { primal := some #[(1234567 : Rat) / 89], dual := none, ray := none }
      log := "" }
  let v := verifyOutcome baseOpts (some 1) trivialProblem sol
  wantsUnchecked .timeLimit v

def allTests : Array TestCase := #[
  ⟨"optimal: feasibility + min proof carried",  tOptimal⟩,
  ⟨"infeasible: Farkas proof carried",          tInfeasible⟩,
  ⟨"unbounded: ray proof carried",              tUnbounded⟩,
  ⟨"maximize: IsOptimal _ .maximize transport", tMaximize⟩,
  ⟨"budget too small short-circuits",           tBudgetExceeded⟩,
  ⟨"budget=5 short-circuits (issue #20)",       tBudget5Exceeded⟩,
  ⟨"default budget accepts the same LP",        tDefaultBudgetPasses⟩,
  ⟨"budget=none disables the check",            tBudgetNoneDisables⟩,
  ⟨"invalid problem rejected before solve",     tInvalidProblem⟩,
  ⟨"verifyOutcome: optimal missing primal/dual", tMissingCertOptimal⟩,
  ⟨"verifyOutcome: infeasible missing dual",     tMissingCertInfeasible⟩,
  ⟨"verifyOutcome: unbounded missing ray",       tMissingCertUnbounded⟩,
  ⟨"verifyOutcome: failed checkOptimal",         tFailedCheckOptimal⟩,
  ⟨"verifyOutcome: non-terminal preserves status", tNonTerminalPreservesStatus⟩
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
    IO.println s!"All {allTests.size} solveVerified tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {allTests.size} solveVerified tests FAILED."
    return 1
