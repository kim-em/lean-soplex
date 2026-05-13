/-
  End-to-end tests that pit `solveFloat` against `solveExact` on
  ill-conditioned LPs. The point is to demonstrate that the two solvers
  produce materially different objectives on inputs where double
  precision loses information, even though both report `.optimal` —
  exact mode's iterative refinement reaches an answer the pure-float
  pivot cannot.

  See PLAN.md §"Test corpus" item: "An ill-conditioned LP where the
  float solve disagrees with the exact solve, confirming exact mode
  produces the expected verified answer."
-/

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
    (objOffset : Rat := 0) : Problem :=
  { numVars, numConstraints, c, a, rowBounds, colBounds, objOffset }

private def noPresolve : Options :=
  { ({} : Options) with presolve := false, verbose := false, precisionBoost := false }

/-- Lossy `Rat → Float` for objective-comparison purposes only.
    `(q.num : Float) / (q.den : Float)` is single-rounding; adequate for
    a `1e-10` divergence check. -/
private def ratToFloat (q : Rat) : Float :=
  let sign : Float := if q.num < 0 then -1.0 else 1.0
  sign * (Float.ofScientific q.num.natAbs false 0 / Float.ofScientific q.den false 0)

/-- Absolute value of a `Float`. -/
private def fAbs (x : Float) : Float := if x < 0 then -x else x

/-! ## (1) Ill-conditioned LP: float-mode vs exact-mode divergence.

  The constraints `7 x₁ = 1, 10⁷ x₁ − x₂ = 0` force `x₁ = 1/7` and
  `x₂ = 10⁷/7`. With `c = (0, 10⁷)` the mathematically-true objective
  is `c·x = 10¹⁴/7 ≈ 14285714285714.285714…`.

  Float mode does the multiplication in `double` and accumulates a few
  ULPs of error at this magnitude. ULP near `10¹³` is about `2⁻³⁹ ≈
  1.8e-12`, but two chained multiplications (`x₁ = 1/7` rounded once,
  `x₂ = 10⁷ · x₁` rounded again, `obj = 10⁷ · x₂` rounded a third
  time) compound into a milli-scale discrepancy. Exact mode's
  iterative-refinement loop drives the objective to a much closer
  rational, and the two `double` objectives end up disagreeing by
  about `2e-3` — well beyond the `1e-10` floor the issue asks for. -/
private def illConditionedLp : Problem :=
  mkProblem 2 2
    (c := #[0, (10:Rat)^7])
    (a := #[(0, 0, 7), (1, 0, (10:Rat)^7), (1, 1, -1)])
    (rowBounds := #[(some 1, some 1), (some 0, some 0)])
    (colBounds := #[(some 0, none), (some 0, none)])

/-- Both solvers report `.optimal`, but `objective`s disagree by more
    than `1e-10` and exact-mode's value is meaningfully closer to the
    rational truth `10¹⁴/7`.

    Three assertions, not one, so a regression where exact stops
    drifting from float at the float-only answer fails the test:

    * `|objE − objF| > 1e-10` — the documented divergence floor.
    * `errExact ≤ errFloat` — exact is at least as close to the truth.
    * `errExact < 1e-4` — exact is strictly close. A regression where
      exact stalls at float precision pushes `errExact ≈ errFloat ≈
      2e-3` and trips this bound. -/
private def tIllConditionedDiverges (_ : Unit) : Outcome :=
  let p := illConditionedLp
  match solveExact noPresolve p, solveFloat noPresolve p with
  | .error e, _ => .fail s!"solveExact failed: {repr e}"
  | _, .error e => .fail s!"solveFloat failed: {repr e}"
  | .ok se, .ok sf =>
    match se.status, sf.status, se.objective, sf.objective with
    | .optimal, .optimal, some objE, some objF =>
      let objEf   := ratToFloat objE
      let diff    := fAbs (objEf - objF)
      let truth   : Float := ratToFloat ((10:Rat)^14 / 7)
      let errExact := fAbs (objEf - truth)
      let errFloat := fAbs (objF - truth)
      let diverges    := diff > 1e-10
      let exactCloser := errExact ≤ errFloat
      let exactTight  := errExact < 1e-4
      expect (diverges && exactCloser && exactTight)
        (s!"divergence check failed: |Δobj|={diff}, " ++
         s!"errExact={errExact}, errFloat={errFloat}, " ++
         s!"objE={objEf}, objF={objF}, truth={truth}")
    | _, _, _, _ =>
      .fail s!"unexpected solver outcomes: exact={repr se}, float={repr sf}"

/-! ## Verified end-to-end on an LP whose optimum is float-representable.

  PLAN.md §"What this catches" notes that `solveVerified` only returns
  a real soundness proof when SoPlex's certificate passes the pure-Lean
  checker. On `illConditionedLp` above, the rational primal coordinates
  (`1/7`, `10⁷/7`) are not finite-binary, and the `feastol > 0`
  iterative-refinement loop in this Boost/GMP-only build halts before
  the certificate satisfies `Ax = b` exactly — so `solveVerified`
  returns `.unchecked .optimal` there.

  This test pairs the divergence demonstration above with a
  Klee–Minty-style integer-vertex companion LP where exact mode *does*
  hand back a verifiable certificate and `solveVerified` returns
  `Verified.optimal` carrying the soundness proof. Together the two
  tests pin both directions of the float-vs-exact comparison:
  exact-mode reaches answers float cannot (the divergence test) and
  the verified driver actually verifies them when SoPlex's refinement
  converges (this test). -/
private def kleeMintyN3 : Problem :=
  -- max  100 x₁ + 10 x₂ + x₃
  -- s.t. x₁ ≤ 1
  --      20 x₁ + x₂ ≤ 100
  --      200 x₁ + 20 x₂ + x₃ ≤ 10000
  --      0 ≤ xⱼ
  -- Sent as a minimization by negating the objective; optimum is at
  -- `(0, 0, 10000)` with canonical-form obj `-10000`.
  mkProblem 3 3
    (c := #[-100, -10, -1])
    (a := #[(0, 0, 1),
            (1, 0, 20), (1, 1, 1),
            (2, 0, 200), (2, 1, 20), (2, 2, 1)])
    (rowBounds := #[(none, some 1), (none, some 100), (none, some 10000)])
    (colBounds := #[(some 0, none), (some 0, none), (some 0, none)])

private def tIllConditionedVerified (_ : Unit) : Outcome :=
  match solveVerified noPresolve kleeMintyN3 with
  | .error e => .fail s!"solveVerified failed: {repr e}"
  | .ok r =>
    match r.verified with
    | .optimal x h =>
      -- The match binding `h` proves `IsFeasible ∧ IsOptimal`; we
      -- additionally pin the primal vertex so a wrong-vertex regression
      -- (which would still satisfy the proof shape) fails.
      let _ : IsFeasible r.normalized x ∧ IsOptimal r.normalized .minimize x := h
      expect (x = #[0, 0, 10000])
        s!"unexpected verified optimum: {repr x}"
    | .infeasible _  => .fail "expected .optimal, got .infeasible"
    | .unbounded ..  => .fail "expected .optimal, got .unbounded"
    | .unchecked s   => .fail s!"expected .optimal, got .unchecked {repr s}"

/-! ## Driver. -/

def allTests : Array TestCase := #[
  ⟨"ill-conditioned LP: float vs exact diverge by > 1e-10",
    tIllConditionedDiverges⟩,
  ⟨"verified end-to-end on Klee–Minty n=3",
    tIllConditionedVerified⟩
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
    IO.println s!"All {allTests.size} solveCompare tests passed."
    return 0
  else
    IO.eprintln s!"{failed} of {allTests.size} solveCompare tests FAILED."
    return 1
