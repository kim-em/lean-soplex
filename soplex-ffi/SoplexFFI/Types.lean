/-
  Data types shared by the certificate checker (`Soplex.Verify`) and
  the FFI binding (`Soplex.Basic`).

  Lives inside the `Verify` namespace because the verifier is the
  standalone library; the FFI side imports these types and reuses them
  unchanged. Pure-Lean only — no dependency on the FFI.

  This file states the shared API types; the verifier and FFI layers
  both import these definitions.
-/

namespace Soplex

/-- Largest natural value this package passes through SoPlex APIs that
    take C++ `int` parameters. -/
def ffiMaxInt : Nat := 2147483647

/-- Objective sense. The verifier internally canonicalises everything
    to `.minimize`; `.maximize` is reduced by negating the objective. -/
inductive ObjSense | minimize | maximize
  deriving Repr, DecidableEq

/-- Which simplex variant to run. `.auto` lets SoPlex decide. -/
inductive Simplex  | primal | dual | auto
  deriving Repr, DecidableEq

/-- Solver / verifier configuration. -/
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
      internally so certificates describe the original normalised LP. -/
  presolve       : Bool        := true
  deriving Repr

/-- LP problem in canonical sparse form.

    Sparse `a` entries are `(row, col, value)`, 0-indexed. `validate`
    normalises this representation: duplicate `(row, col)` entries are
    summed, zero values are dropped, entries are sorted by `(row, col)`.
    The verifier always runs against the post-`validate` form. -/
structure Problem (numConstraints numVars : Nat) where
  /-- Objective coefficients (length = `numVars`). All zero ⇒ pure
      feasibility. -/
  c              : Vector Rat numVars
  /-- Optional constant added to the objective. -/
  objOffset      : Rat := 0
  /-- Sparse constraint matrix entries: `(row, col, value)`, 0-indexed.
      Normalised by `validate`. -/
  a              : Array (Nat × Nat × Rat)
  /-- Per-row bounds `(lo, hi)`; `none` = ±∞. Covers ≤, =, ≥, and
      ranged constraints uniformly. -/
  rowBounds      : Vector (Option Rat × Option Rat) numConstraints
  /-- Per-variable bounds `(lo, hi)`; `none` = ±∞. -/
  colBounds      : Vector (Option Rat × Option Rat) numVars
  deriving Repr

/-- Tag used by `ProblemError.indexOutOfRange` and `boundInverted`. -/
inductive IndexKind | row | col | sparseEntry
  deriving Repr, DecidableEq

/-- Why `validate` rejected a `Problem`. -/
inductive ProblemError
  /-- An array field had the wrong length for the declared `numVars` /
      `numConstraints`. -/
  | wrongLength      (field : String) (expected got : Nat)
  /-- A field is too large for the FFI representation used by SoPlex. -/
  | tooLarge         (field : String) (max got : Nat)
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
  | iterLimitTooLarge (max got : Nat)
  deriving Repr

/-- Canonical lower / upper split for dual multipliers.

    All four vectors are nonnegative and length-matched to the problem
    (`m` rows, `n` cols); a coordinate is zero whenever the matching
    bound is `none`. The *signed* dual would be `rowLower − rowUpper`
    (and similarly for columns), but storing the split is strictly more
    expressive for ranged constraints, where the dual objective genuinely
    depends on the decomposition. -/
structure DualBundle (m n : Nat) where
  /-- Multipliers for `rowLoᵢ ≤ (Ax)ᵢ` (one per row). -/
  rowLower : Vector Rat m
  /-- Multipliers for `(Ax)ᵢ ≤ rowHiᵢ` (one per row). -/
  rowUpper : Vector Rat m
  /-- Multipliers for `colLoⱼ ≤ xⱼ` (one per column). -/
  colLower : Vector Rat n
  /-- Multipliers for `xⱼ ≤ colHiⱼ` (one per column). -/
  colUpper : Vector Rat n
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
    rejects accordingly.

    Parameterised by `(m n : Nat)` — the constraint and variable
    counts — so the primal / ray vectors and the dual bundle all
    carry their expected lengths in the type. -/
structure Certificate (m n : Nat) where
  primal : Option (Vector Rat n)
  dual   : Option (DualBundle m n)
  ray    : Option (Vector Rat n)
  deriving Repr, Inhabited

/-- Exact-mode result. `Solution.objective` is always in the
    *caller's original sense* (including `objOffset`), never the
    internal min-canonical value.

    Parameterised by `(numConstraints numVars : Nat)` so the
    embedded `Certificate` is dimension-aware at the type level.
    The dimensions come from the `Problem` the `Solution` was
    produced from. -/
structure Solution (numConstraints numVars : Nat) where
  status         : SolveStatus
  /-- Exact for `status = optimal`; a hint otherwise. -/
  objective      : Option Rat
  certificate    : Certificate numConstraints numVars
  /-- Captured solver log; `""` when `Options.verbose = false`. -/
  log            : String
  deriving Repr, Inhabited

/-- Float-mode result. Kept distinct from `Solution` to prevent
    accidental feeding into the verifier: these rationals are exact
    representations of IEEE-754 doubles, not exact-mode certificates.

    Parameterised by `(numVars : Nat)` — only the primal vector
    needs a length tag. -/
structure FloatSolution (numVars : Nat) where
  status      : SolveStatus
  /-- Primal solution as exact rationals representing the doubles
      SoPlex computed. NOT certificate-grade. -/
  primalAsRat : Option (Vector Rat numVars)
  objective   : Option Float
  /-- Captured solver log; `""` when `Options.verbose = false`. -/
  log         : String
  deriving Repr, Inhabited

/-- Errors surfaced by the FFI layer. Invalid Lean-side inputs are
    reported structurally; all unclassified C++ / SoPlex failures remain
    bridge errors. True bridge-invariant violations may still `panic`. -/
inductive SolveError
  | invalidProblem (e : ProblemError)
  | invalidOptions (e : OptionError)
  /-- File parse error from `readMps` / `readLp`. -/
  | parseError     (path : String) (msg : String)
  /-- FFI-level failure that didn't `panic`. -/
  | bridge         (msg : String)
  deriving Repr

/-! ## Objective canonicalisation. -/

/-- Flip the objective in place. Identity on everything else. -/
def negateObjective {m n : Nat} (p : Problem m n) : Problem m n :=
  { p with c := p.c.map Neg.neg, objOffset := -p.objOffset }

/-- Reduce to minimisation form. -/
def canonicalize {m n : Nat} (sense : ObjSense) (p : Problem m n) : Problem m n :=
  match sense with
  | .minimize => p
  | .maximize => negateObjective p

end Soplex
