/-
  User-facing verified-solve driver: data types and the pure
  Solution→Verified mapping.

  The `solveVerified` glue in `LeanSoplex.Basic` chains
  `validateOptions`, `validate`, and `solveExact`, then defers to
  `verifyOutcome` (below) for the certificate-by-certificate
  bookkeeping. Keeping that bookkeeping in this file (which has no
  FFI dependency) lets the soundness story sit entirely in the
  pure-Lean `LeanSoplexVerify` library: the FFI side only contributes
  the `Solution` value.

  See `PLAN.md` §"User-facing driver".
-/

import LeanSoplex.Verify.Prop
import LeanSoplex.Verify.Sound
import LeanSoplex.Verify.Budget

namespace LeanSoplex.Verify

open LeanSoplex

/-- A proof about a specific `Problem`. The problem index is **always
    the validated / normalised form**, never the user's raw input. -/
inductive Verified {m n : Nat} (p : Problem m n) (sense : ObjSense)
  /-- Optimal: a feasible point that achieves the optimum. -/
  | optimal     (x : Vector Rat n)
                (h : IsFeasible p x.toArray ∧ IsOptimal p sense x.toArray)
  /-- Provably infeasible. -/
  | infeasible  (h : IsInfeasible p)
  /-- Unbounded: a feasible base point and an improving recession ray. -/
  | unbounded   (x ray : Vector Rat n) (h : IsUnbounded p sense)
  /-- Solver couldn't decide, or its certificate failed to verify. -/
  | unchecked   (status : SolveStatus)

/-- Result of `solveVerified`: the normalised problem the checker
    actually ran against, plus the proof carried by `Verified`. -/
structure VerifiedSolve {m n : Nat} (sense : ObjSense) where
  normalized : Problem m n
  verified   : Verified normalized sense

/-! ## Sense-canonicalisation is feasibility-invariant.

  `canonicalize` only touches `c` and `objOffset`; `IsFeasible` does
  not. So `IsFeasible (canonicalize sense p) x ↔ IsFeasible p x` by
  `rfl` once `sense` is destructured. Used below to repackage
  `checkOptimal_sound`'s feasibility component (which is stated
  about the canonicalised LP) into the `IsFeasible normalized x`
  shape that `Verified.optimal` demands. -/
private theorem isFeasible_canonicalize_iff {m n : Nat}
    {sense : ObjSense} {p : Problem m n} {x : Array Rat} :
    IsFeasible (canonicalize sense p) x ↔ IsFeasible p x := by
  cases sense <;> exact Iff.rfl

/-- Pure mapping from a `Solution` (whatever produced it) to a
    `Verified` proof carrier. Every failure path returns
    `Verified.unchecked _`; the three positive constructors are only
    built from real soundness-lemma conclusions, never fabricated.

    Failure paths, in order:

    1. Budget overrun (`denomBudget = some n` and the certificate's
       rationals exceed `n` bits) → `.unchecked .budgetExceeded`,
       checked **before** any `check*` runs.
    2. Non-terminal solver status (`timeLimit`, `iterLimit`,
       `numericFailure`, `aborted`, `budgetExceeded`) → passed
       through as `.unchecked status`.
    3. Missing certificate field for a terminal status (e.g.
       `.optimal` but no `dual`) → `.unchecked status`.
    4. Failed `check*` → `.unchecked status`.

    The downstream `check*` runs against the canonicalised LP, which
    is `negateObjective normalized` for `.maximize`. -/
def verifyOutcome {m n : Nat} (opts : Options) (denomBudget : Option Nat)
    (normalized : Problem m n) (sol : Solution m n) :
    Verified normalized opts.sense :=
  let pCanon := canonicalize opts.sense normalized
  let overBudget : Bool :=
    denomBudget.isSome && !certificateWithinBudget denomBudget sol.certificate
  match sol.status with
  | .optimal =>
      if overBudget then .unchecked .budgetExceeded
      else
        match sol.certificate.primal, sol.certificate.dual with
        | some x, some d =>
            if hChk : checkOptimal pCanon x d = true then
              let ⟨hFeas, hOpt⟩ := checkOptimal_sound hChk
              .optimal x ⟨isFeasible_canonicalize_iff.mp hFeas, hOpt⟩
            else
              .unchecked .optimal
        | _, _ => .unchecked .optimal
  | .infeasible =>
      if overBudget then .unchecked .budgetExceeded
      else
        match sol.certificate.dual with
        | some d =>
            if hChk : checkInfeasible normalized d = true then
              .infeasible (checkInfeasible_sound hChk)
            else
              .unchecked .infeasible
        | none => .unchecked .infeasible
  | .unbounded =>
      if overBudget then .unchecked .budgetExceeded
      else
        match sol.certificate.primal, sol.certificate.ray with
        | some x, some r =>
            if hChk : checkUnbounded pCanon x r = true then
              .unbounded x r (checkUnbounded_sound hChk)
            else
              .unchecked .unbounded
        | _, _ => .unchecked .unbounded
  | s => .unchecked s

end LeanSoplex.Verify
