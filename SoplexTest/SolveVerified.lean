/-
  End-to-end tests for `solveVerified`. Each test drives a real
  SoPlex solve and pattern-matches on the returned `Verified` to
  prove (literally — the `h` field is a real soundness-lemma
  proof) optimality / infeasibility / unboundedness.
-/
import SoplexTest.SolveCommon

open Soplex Soplex.Verify SoplexTest

/-! ## `wantsX` helpers.

  Pattern-match a `Verified` against the expected constructor and pin
  the proof's type with a `let _ : ... := h`. A mismatched constructor
  reports the constructor we got. -/

private def wantsOptimal {m n : Nat} {p : Problem m n} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal x h =>
      let _ : IsFeasible p x.toArray ∧ IsOptimal p sense x.toArray := h
      .ok
  | .infeasible _ => .fail "expected optimal, got infeasible"
  | .unbounded .. => .fail "expected optimal, got unbounded"
  | .unchecked s  => .fail s!"expected optimal, got unchecked {repr s}"

private def wantsInfeasible {m n : Nat} {p : Problem m n} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..   => .fail "expected infeasible, got optimal"
  | .infeasible h =>
      let _ : IsInfeasible p := h
      .ok
  | .unbounded .. => .fail "expected infeasible, got unbounded"
  | .unchecked s  => .fail s!"expected infeasible, got unchecked {repr s}"

private def wantsUnbounded {m n : Nat} {p : Problem m n} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..       => .fail "expected unbounded, got optimal"
  | .infeasible _     => .fail "expected unbounded, got infeasible"
  | .unbounded _ _ h  =>
      let _ : IsUnbounded p sense := h
      .ok
  | .unchecked s      => .fail s!"expected unbounded, got unchecked {repr s}"

private def wantsUnchecked (expected : SolveStatus)
    {m n : Nat} {p : Problem m n} {sense : ObjSense} :
    Verified p sense → Outcome
  | .optimal ..    => .fail s!"expected unchecked {repr expected}, got optimal"
  | .infeasible _  => .fail s!"expected unchecked {repr expected}, got infeasible"
  | .unbounded ..  => .fail s!"expected unchecked {repr expected}, got unbounded"
  | .unchecked s   =>
      expect (s = expected)
        s!"unchecked status mismatch: got {repr s}, wanted {repr expected}"

private def runVerified {m n : Nat} (opts : Options) (p : Problem m n)
    (denomBudget : Option Nat := some 10000)
    (k : ∀ (norm : Problem m n), Verified norm opts.sense → Outcome) : Outcome :=
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
  runVerified noPresolve p (k := fun _ v => wantsOptimal v)

private def tInfeasible (_ : Unit) : Outcome :=
  let p := mkProblem 1 2
    (c := #[0])
    (a := #[(0, 0, 1), (1, 0, 1)])
    (rowBounds := #[(some 1, none), (none, some 0)])
    (colBounds := #[(none, none)])
  runVerified noPresolve p (k := fun _ v => wantsInfeasible v)

private def tUnbounded (_ : Unit) : Outcome :=
  let p := mkProblem 1 0
    (c := #[-1])
    (a := #[])
    (rowBounds := #[])
    (colBounds := #[(some 0, none)])
  runVerified noPresolve p (k := fun _ v => wantsUnbounded v)

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
  let opts := { noPresolve with sense := .maximize }
  runVerified opts p (k := fun norm v =>
    match v with
    | .optimal x h =>
        let _ : IsOptimal norm .maximize x.toArray := h.2
        expect (x.toArray = #[1]) s!"bad max primal: {repr x}"
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
  runVerified noPresolve p (denomBudget := some 1)
    (k := fun _ v => wantsUnchecked .budgetExceeded v)

/-- Budget regression for a tiny LP solved with the absurdly low cap
    `some 5`. The optimum is the
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
  runVerified noPresolve p (denomBudget := some 5)
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
  match solveVerified noPresolve p with
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
  runVerified noPresolve p (denomBudget := none)
    (k := fun _ v => wantsOptimal v)

/-! ## Pure `verifyOutcome` tests.

  Exercise failure paths that are hard to drive end-to-end through
  `solveVerified` by feeding `verifyOutcome` a hand-built `Solution`
  directly. -/

private def trivialProblem : Problem 0 1 :=
  mkProblem 1 0 (c := #[0]) (a := #[]) (rowBounds := #[])
    (colBounds := #[(some 0, none)])

private def emptyCert : Certificate 0 1 :=
  { primal := none, dual := none, ray := none }

/-- `.optimal` status with no primal certificate: missing-field path. -/
private def tMissingCertOptimal (_ : Unit) : Outcome :=
  let sol : Solution 0 1 :=
    { status := .optimal, objective := none, certificate := emptyCert, log := "" }
  let v := verifyOutcome noPresolve none trivialProblem sol
  wantsUnchecked .optimal v

/-- `.infeasible` status with no dual certificate. -/
private def tMissingCertInfeasible (_ : Unit) : Outcome :=
  let sol : Solution 0 1 :=
    { status := .infeasible, objective := none, certificate := emptyCert, log := "" }
  let v := verifyOutcome noPresolve none trivialProblem sol
  wantsUnchecked .infeasible v

/-- `.unbounded` status with no ray. -/
private def tMissingCertUnbounded (_ : Unit) : Outcome :=
  let sol : Solution 0 1 :=
    { status := .unbounded, objective := none
      certificate := { primal := some #v[0], dual := none, ray := none }
      log := "" }
  let v := verifyOutcome noPresolve none trivialProblem sol
  wantsUnchecked .unbounded v

/-- Primal infeasible for `trivialProblem`'s `0 ≤ x` bound, so
    `checkOptimal` rejects. The driver returns `.unchecked .optimal`
    rather than fabricating a proof. -/
private def tFailedCheckOptimal (_ : Unit) : Outcome :=
  let bogusDual : DualBundle 0 1 :=
    { rowLower := #v[], rowUpper := #v[]
      colLower := #v[0], colUpper := #v[0] }
  let sol : Solution 0 1 :=
    { status := .optimal, objective := none
      certificate := { primal := some #v[-1], dual := some bogusDual, ray := none }
      log := "" }
  let v := verifyOutcome noPresolve none trivialProblem sol
  wantsUnchecked .optimal v

/-- Non-terminal statuses pass straight through to `.unchecked status`,
    even when the certificate happens to be over budget — the budget
    check only runs when the status is terminal, not unconditionally. -/
private def tNonTerminalPreservesStatus (_ : Unit) : Outcome :=
  let sol : Solution 0 1 :=
    { status := .timeLimit, objective := none
      certificate := { primal := some #v[(1234567 : Rat) / 89], dual := none, ray := none }
      log := "" }
  let v := verifyOutcome noPresolve (some 1) trivialProblem sol
  wantsUnchecked .timeLimit v

def allTests : Array TestCase := #[
  .ofPure "optimal: feasibility + min proof carried"    tOptimal,
  .ofPure "infeasible: Farkas proof carried"            tInfeasible,
  .ofPure "unbounded: ray proof carried"                tUnbounded,
  .ofPure "maximize: IsOptimal _ .maximize transport"   tMaximize,
  .ofPure "budget too small short-circuits"             tBudgetExceeded,
  .ofPure "budget=5 short-circuits"                     tBudget5Exceeded,
  .ofPure "default budget accepts the same LP"          tDefaultBudgetPasses,
  .ofPure "budget=none disables the check"              tBudgetNoneDisables,
  .ofPure "verifyOutcome: optimal missing primal/dual"  tMissingCertOptimal,
  .ofPure "verifyOutcome: infeasible missing dual"      tMissingCertInfeasible,
  .ofPure "verifyOutcome: unbounded missing ray"        tMissingCertUnbounded,
  .ofPure "verifyOutcome: failed checkOptimal"          tFailedCheckOptimal,
  .ofPure "verifyOutcome: non-terminal preserves status" tNonTerminalPreservesStatus
]

def main : IO UInt32 := runAll "solveVerified" allTests
