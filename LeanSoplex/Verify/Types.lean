/-
  Data types shared by the certificate checker (`LeanSoplex.Verify`) and
  the FFI binding (`LeanSoplex.Basic`).

  Lives inside the `Verify` namespace because the verifier is the
  standalone library; the FFI side imports these types and reuses them
  unchanged. Pure-Lean only — no dependency on the FFI.

  Most of the design rationale lives in `PLAN.md` §"API" and
  §"Verification layer"; this file only restates the types themselves.
-/

namespace LeanSoplex

/-- Objective sense. The verifier internally canonicalises everything
    to `.minimize`; `.maximize` is reduced by negating the objective. -/
inductive ObjSense | minimize | maximize
  deriving Repr, DecidableEq

/-- Which simplex variant to run. `.auto` lets SoPlex decide. -/
inductive Simplex  | primal | dual | auto
  deriving Repr, DecidableEq

/-- Solver / verifier configuration. See `PLAN.md` §"API". -/
structure Options where
  sense          : ObjSense    := .minimize
  /-- Wall-clock limit in seconds; `none` = unlimited. -/
  timeLimit      : Option Float := none
  /-- Simplex-iteration limit; `none` = unlimited. -/
  iterLimit      : Option Nat   := none
  simplex        : Simplex     := .auto
  verbose        : Bool        := false
  randomSeed     : UInt32      := 0
  /-- Fall back to precision boosting on ill-conditioned LPs. -/
  precisionBoost : Bool        := true
  /-- Enable SoPlex's presolve. `solveVerified` forces this `false`
      internally; see `PLAN.md` §"What this catches" §4. -/
  presolve       : Bool        := true
  deriving Repr

/-- LP problem in canonical sparse form.

    Sparse `a` entries are `(row, col, value)`, 0-indexed. `validate`
    normalises this representation: duplicate `(row, col)` entries are
    summed, zero values are dropped, entries are sorted by `(row, col)`.
    The verifier always runs against the post-`validate` form. -/
structure Problem where
  numVars        : Nat
  numConstraints : Nat
  /-- Objective coefficients (length = `numVars`). All zero ⇒ pure
      feasibility. -/
  c              : Array Rat
  /-- Optional constant added to the objective. -/
  objOffset      : Rat := 0
  /-- Sparse constraint matrix entries: `(row, col, value)`, 0-indexed.
      Normalised by `validate`. -/
  a              : Array (Nat × Nat × Rat)
  /-- Per-row bounds `(lo, hi)`; `none` = ±∞. Covers ≤, =, ≥, and
      ranged constraints uniformly. -/
  rowBounds      : Array (Option Rat × Option Rat)
  /-- Per-variable bounds `(lo, hi)`; `none` = ±∞. -/
  colBounds      : Array (Option Rat × Option Rat)
  deriving Repr

/-- Tag used by `ProblemError.indexOutOfRange` and `boundInverted`. -/
inductive IndexKind | row | col | sparseEntry
  deriving Repr, DecidableEq

/-- Why `validate` rejected a `Problem`. -/
inductive ProblemError
  /-- An array field had the wrong length for the declared `numVars` /
      `numConstraints`. -/
  | wrongLength      (field : String) (expected got : Nat)
  /-- A sparse-entry coordinate or bound array index pointed outside
      the declared dimensions. -/
  | indexOutOfRange  (kind : IndexKind) (index bound : Nat)
  /-- A bound pair had `lo > hi`. -/
  | boundInverted    (kind : IndexKind) (i : Nat) (lo hi : Rat)
  deriving Repr

/-- Why `validateOptions` rejected an `Options`. -/
inductive OptionError
  | nanTimeLimit
  | negativeTimeLimit (value : Float)
  | zeroIterLimit
  deriving Repr

/-- Canonical lower / upper split for dual multipliers.

    All four arrays are nonnegative and length-matched to the problem;
    a coordinate is zero whenever the matching bound is `none`. The
    *signed* dual would be `rowLower − rowUpper` (and similarly for
    columns), but storing the split is strictly more expressive for
    ranged constraints, where the dual objective genuinely depends on
    the decomposition. See `PLAN.md` §"Dual feasibility, concretely". -/
structure DualBundle where
  /-- Multipliers for `rowLoᵢ ≤ (Ax)ᵢ` (one per row). -/
  rowLower : Array Rat
  /-- Multipliers for `(Ax)ᵢ ≤ rowHiᵢ` (one per row). -/
  rowUpper : Array Rat
  /-- Multipliers for `colLoⱼ ≤ xⱼ` (one per column). -/
  colLower : Array Rat
  /-- Multipliers for `xⱼ ≤ colHiⱼ` (one per column). -/
  colUpper : Array Rat
  deriving Repr, Inhabited

/-- Outcome bucket reported by `solveExact` / `solveVerified`. -/
inductive SolveStatus
  | optimal
  | infeasible
  | unbounded
  | timeLimit
  | iterLimit
  /-- Refinement + boosting both failed. -/
  | numericFailure
  /-- Set by the *checker*, not by SoPlex: the certificate's
      numerator-plus-denominator bit length exceeded `denomBudget`. -/
  | budgetExceeded
  | aborted
  deriving Repr, DecidableEq, Inhabited

/-- Certificate of the solve outcome.

    Which fields are required depends on `status`:

    * `optimal`     — `primal` and `dual`
    * `infeasible`  — `dual` (a Farkas multiplier)
    * `unbounded`   — `primal` (a feasible base point) and `ray`
    * anything else — none required

    The verifier checks the appropriate combination and accepts /
    rejects accordingly. See `PLAN.md` §"The three certificates". -/
structure Certificate where
  primal : Option (Array Rat)
  dual   : Option DualBundle
  ray    : Option (Array Rat)
  deriving Repr, Inhabited

/-- Exact-mode result. `Solution.objective` is always in the
    *caller's original sense* (including `objOffset`), never the
    internal min-canonical value. -/
structure Solution where
  status      : SolveStatus
  /-- Exact for `status = optimal`; a hint otherwise. -/
  objective   : Option Rat
  certificate : Certificate
  /-- Captured solver log; `""` when `Options.verbose = false`. -/
  log         : String
  deriving Repr, Inhabited

/-- Float-mode result. Kept distinct from `Solution` to prevent
    accidental feeding into the verifier: these rationals are exact
    representations of IEEE-754 doubles, not exact-mode certificates. -/
structure FloatSolution where
  status      : SolveStatus
  /-- Primal solution as exact rationals representing the doubles
      SoPlex computed. NOT certificate-grade. -/
  primalAsRat : Option (Array Rat)
  objective   : Option Float
  /-- Captured solver log; `""` when `Options.verbose = false`. -/
  log         : String
  deriving Repr, Inhabited

/-- Errors surfaced by the FFI layer. User-input or known-solver-
    -limitation issues live here; impossible states `panic` instead.
    See `PLAN.md` §"`Except` vs `panic`". -/
inductive SolveError
  | invalidProblem (e : ProblemError)
  | invalidOptions (e : OptionError)
  /-- A known SoPlex limitation hit (e.g. requested feature not in
      the linked release). -/
  | unsupported    (feature : String)
  /-- SoPlex rejected an `Options` field at runtime. -/
  | parameter      (msg : String)
  /-- The linked SoPlex lacks a required accessor (e.g. an
      exact-mode getter introduced in a newer release). -/
  | missingApi     (feature : String)
  /-- File parse error from `readMps` / `readLp`. -/
  | parseError     (path : String) (msg : String)
  /-- FFI-level failure that didn't `panic`. -/
  | bridge         (msg : String)
  deriving Repr

end LeanSoplex
