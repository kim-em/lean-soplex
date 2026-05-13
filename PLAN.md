# lean-soplex — plan

Stub repo. Goal: Lean 4 FFI bindings for **SoPlex**, the LP solver from
the SCIP optimization suite, used in its **exact (iterative-refinement
+ precision-boosting) mode**, wrapped behind a **pure-Lean certificate
checker** so the bindings can be trusted independently of the solver.

This repo doesn't ship code yet. It exists as a forward-looking design
doc so that if/when [`kim-em/sos`](https://github.com/kim-em/sos) (or
another Lean project) needs a production-grade exact LP solver, this
is the place to drop one.

## What SoPlex is

SoPlex is a high-performance **revised primal/dual simplex** LP solver
developed at ZIB. It's part of the SCIP optimization suite and one of
the standard LP solvers in research MILP/MIP backends. The interesting
feature for our purposes is its **exact-rational mode**: it solves in
floating point at near-production speed and then iteratively refines
to an exact rational answer using controlled perturbations + GMP, with
provably exact basis decisions. Since SoPlex 7.0 the exact mode also
supports **precision boosting** as a fallback when iterative
refinement stalls on ill-conditioned LPs.

The exact mode is *not* the default. It requires specific parameter
settings (`feastol=0`, `opttol=0`, `solvemode=2`, `syncmode=1`,
typically `readmode=1` and `checkmode=2`); the bindings must set these
explicitly rather than relying on defaults.

References:
- Gleixner, Steffy, Wolter. *Iterative Refinement for Linear
  Programming* (INFORMS J. Computing, 2016).
- SoPlex exact-mode docs: https://soplex.zib.de/doc/html/EXACT.php
- Source: https://github.com/scipopt/soplex (active development).
- Project page: https://soplex.zib.de/
- Licence: SoPlex itself is Apache 2.0. The wrapper inherits Apache
  2.0, but the linked binary carries the obligations of its
  dependencies (GMP / GMPXX are LGPL; respect those when choosing
  static vs dynamic linking).

## Why we'd want it

Where [`lean-qsopt`](https://github.com/kim-em/lean-qsopt) gives us a
pure-rational simplex (slow but simple), SoPlex gives us **fast**
exact LP — near floating-point simplex speed on the float pass,
exact-rational refinement only at the end. Speed is instance- and
conditioning-dependent: on ill-conditioned LPs the refinement loop can
stall before precision boosting kicks in. "Often much faster than pure
rational simplex" is the honest framing.

Concrete situations where this matters:

- The half-Newton-polytope basis pruning for `kim-em/sos` issue #23
  has a bounded LP size (a few dozen monomials) that QSopt-Exact and
  the Tier-0 in-tree simplex both handle fine. SoPlex would only
  matter if the SOS pipeline starts solving LPs at larger scale (e.g.
  exact polyhedral preprocessing of Putinar constraints, exact
  rational basis recovery from float SDP solutions).
- A future Lean MILP backend, where the LP relaxation needs to be
  both exact and fast.

For the immediate `kim-em/sos` use case, the Tier-0 simplex suffices.
Explicit trigger criteria for switching this on:

1. A repeated LP workload above a few hundred variables/constraints.
2. QSopt-Exact wall-clock becomes a bottleneck on a real workload.
3. We need MPS/LP file I/O for repros, bug reports, or solver
   comparisons.
4. A MILP relaxation loop appears (any branch-and-cut style code).

## Template: follow `lean-csdp`

The build pattern is fully solved by
[`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp). Mirror that
structure:

```
soplex/                       # vendor as git submodule (scipopt/soplex)
ffi/lean_soplex.cpp           # C++ glue translating flat sparse LP data
ffi/lean_soplex_bridge.cpp    # C-ABI entry points Lean calls
LeanSoplex/Basic.lean         # opaque FFI declarations + Lean-side types
LeanSoplex/Verify.lean        # pure-Lean certificate checkers (see below)
Main.lean                     # worked examples (also used as smoke test)
lakefile.lean                 # build config; two lean_lib targets
                              # (LeanSoplex.Verify with no FFI dep, LeanSoplex with)
.github/workflows/ci.yml      # Linux + macOS + Windows CI — MANDATORY
scripts/install-toolchain.sh
README.md
LICENSE                       # Apache 2.0 for the wrapper
```

CI is non-negotiable. Certificate checkers, FFI object lifetimes, and
GMP linkage all break silently; the three-platform matrix plus the
test corpus (§"Test corpus") must be green on every push. Run an
ASan/UBSan build on Linux on top of the normal matrix.

`README.md` and `LICENSE` are **day-one deliverables**, not optional.
The README must cover: per-platform build steps (Linux / macOS /
Windows), a minimal working example end-to-end, a pointer to the
verification story (so users understand the trust model), and
GMP / Boost install notes. The LICENSE is `Apache-2.0`; if static
linking of dependencies is chosen, ship a `NOTICE` alongside it with
SoPlex / GMP / Boost attribution. The repo should not advertise
itself as a working binding without both files in place.

### FFI safety

SoPlex is C++. `extern "C"` linkage is necessary but not sufficient.
The bridge must:

- Mark every entry point `noexcept` and catch all C++ exceptions,
  translating them into structured `SolveError` values. No C++
  exception ever crosses the C ABI.
- Manage Lean object lifetimes correctly (`lean_object*`,
  `lean_obj_arg`, `lean_inc`/`lean_dec`). `Rat` decoding has two
  cases (small `Int` and boxed numerator/denominator) — get both
  right, or the checker will catch you later.
- Use RAII strictly inside each call. No Lean object retained across
  calls; no SoPlex object outlives its entry point.
- Be deterministic: no thread pools, no environment-dependent
  behavior, random seed always set.

## API

Pure, not in `IO`. SoPlex is an unverified oracle; the verification
layer below is what gives us correctness. Hiding the call behind `IO`
buys us nothing semantic and costs us the ability to call the solver
from tactics or `decide`-style code. Every FFI entry point — solver
and file I/O alike — returns `Except SolveError _`.

**Pure-FFI execution contract.** `solveExact`, `solveFloat`, and the
MPS/LP read/write entry points are `opaque` to the kernel. The kernel
never unfolds them; only the runtime evaluator (and `native_decide`)
can call into the bridge. **Soundness never depends on what the
solver returns** — only certificates that pass a pure-Lean checker
produce proofs of optimality / infeasibility / unboundedness. File
I/O has observable side effects on disk, but those are hidden behind
the same opaque-extern trick as the solver's CPU/memory use; from
Lean's perspective the result is a function of inputs.

**`Except` vs `panic`.** Anything attributable to user input or to a
recoverable SoPlex condition goes in `Except`: a malformed `Problem`
(caught by `validate`), malformed `Options` (caught by
`validateOptions`), an unsupported feature, a parameter rejected by
SoPlex, a missing certificate accessor in the linked SoPlex version,
a file parse error. Only true bridge-invariant violations —
allocation failure, a contract-broken Lean object, an unrecoverable
native crash — `panic`. The line is "user error or known solver
limitation ⇒ `Except`; impossible state ⇒ `panic`".

Caveat for resource limits: if `Options.timeLimit` or `iterLimit` is
set, the result depends on host speed. The non-determinism is
captured in `SolveStatus`, not in the monad — the user opted in by
setting the limit. Note that a `Verified.optimal` produced under a
time limit is **proof-producing but not reproducible**: another
machine might return `unchecked (timeLimit)` for the same inputs.

```lean
namespace LeanSoplex

inductive ObjSense | minimize | maximize
inductive Simplex  | primal | dual | auto

structure Options where
  sense          : ObjSense    := .minimize
  timeLimit      : Option Float := none    -- seconds; none = unlimited
  iterLimit      : Option Nat   := none
  simplex        : Simplex     := .auto
  verbose        : Bool        := false
  randomSeed     : UInt32      := 0
  precisionBoost : Bool        := true     -- fallback for ill-conditioned LPs
  /-- Enable SoPlex's presolve. Substantial speedup on most LPs, but
      certificates returned then describe the *presolved* problem and
      will not pass the Lean-side checker. `solveVerified` forces
      this to `false` internally; direct callers of `solveExact` can
      leave it on for raw exact-rational answers without proof. -/
  presolve       : Bool        := true

structure Problem where
  numVars        : Nat
  numConstraints : Nat
  /-- Objective coefficients (length = numVars). All zero ⇒ pure feasibility. -/
  c              : Array Rat
  /-- Optional constant added to the objective. -/
  objOffset      : Rat := 0
  /-- Sparse constraint matrix entries: (row, col, value), 0-indexed.
      Normalized by `validate`: duplicate `(row, col)` entries are
      summed, zero-valued entries are dropped, entries are sorted by
      `(row, col)`. -/
  a              : Array (Nat × Nat × Rat)
  /-- Per-row bounds (lo, hi); `none` = ±∞. Covers ≤, =, ≥, and ranged
      constraints uniformly. -/
  rowBounds      : Array (Option Rat × Option Rat)
  /-- Per-variable bounds (lo, hi); `none` = ±∞. -/
  colBounds      : Array (Option Rat × Option Rat)

inductive IndexKind | row | col | sparseEntry
  deriving Repr

inductive ProblemError
  | wrongLength      (field : String) (expected got : Nat)
  | indexOutOfRange  (kind : IndexKind) (index bound : Nat)
  | boundInverted    (kind : IndexKind) (i : Nat) (lo hi : Rat)
  deriving Repr

inductive OptionError
  | nanTimeLimit
  | negativeTimeLimit (value : Float)
  | zeroIterLimit
  deriving Repr

/-- Validate a `Problem` before it touches C++, returning a normalized
copy: duplicate sparse entries summed, zero-valued entries dropped,
sparse data sorted by `(row, col)`, arrays length-checked, indices
in-range, bounds non-inverted. This is a *pure-Lean* layer — failures
here are user errors. **The verification layer always runs against
this normalized form.** Callers either invoke `validate` themselves
and pass the result on, or use `solveVerified`, which internally
validates and returns a `(Σ pN, Verified pN sense)`. -/
def validate : Problem → Except ProblemError Problem := ...

/-- Validate `Options` (NaN / negative `timeLimit`, zero `iterLimit`,
unsupported `Simplex` combos, etc.) before they reach C++. Distinct
from `validate` because `Options` is a separate input space. -/
def validateOptions : Options → Except OptionError Options := ...

inductive SolveStatus
  | optimal
  | infeasible
  | unbounded
  | timeLimit
  | iterLimit
  | numericFailure        -- refinement + boosting both failed
  /-- Set by the *checker*, not by SoPlex: the certificate's
      numerator-plus-denominator bit length exceeded `denomBudget`. -/
  | budgetExceeded
  | aborted

/-- Canonical lower/upper split for dual multipliers. All four arrays
are nonnegative and length-matched to the problem; a coordinate is
zero whenever the matching bound is `none`. The *signed* dual would
be `rowLower − rowUpper` (and similarly for columns), but storing the
split is strictly more expressive for ranged constraints, where the
dual objective genuinely depends on the decomposition. The same shape
is used for both optimality and Farkas (infeasibility) certificates;
the checker tells them apart by which equations it verifies. -/
structure DualBundle where
  rowLower : Array Rat       -- multipliers for `rowLo ≤ Ax` side
  rowUpper : Array Rat       -- multipliers for `Ax ≤ rowHi` side
  colLower : Array Rat       -- multipliers for `colLo ≤ x` side
  colUpper : Array Rat       -- multipliers for `x ≤ colHi` side

structure Certificate where
  /-- Primal solution (length = numVars). Required for `optimal`; for
      `unbounded` it is the base point of the unbounded ray. -/
  primal : Option (Array Rat)
  /-- Dual multipliers in canonical lower/upper form. Required for
      `optimal` and `infeasible`. -/
  dual   : Option DualBundle
  /-- Improving ray (length = numVars). Required for `unbounded`. -/
  ray    : Option (Array Rat)

structure Solution where
  status      : SolveStatus
  /-- Objective value, always in the **caller's original sense**
      (including `objOffset`). Internal min-canonical values are
      never exposed. Exact for `status = optimal`; for any other
      status, this is whatever the solver last reported and carries
      no guarantee — treat it as a hint. -/
  objective   : Option Rat
  certificate : Certificate
  /-- Captured solver log; `""` when `Options.verbose = false`. -/
  log         : String

/-- Distinct from `Solution` to prevent accidental feeding into the
verifier: float-mode rationals are exact representations of doubles,
not exact-mode certificates. -/
structure FloatSolution where
  status     : SolveStatus
  /-- Primal solution as exact rationals representing the IEEE-754
      doubles SoPlex computed. NOT exact-mode certificates. -/
  primalAsRat : Option (Array Rat)
  objective   : Option Float
  /-- `""` when `Options.verbose = false`. -/
  log         : String

inductive SolveError
  | invalidProblem (e : ProblemError)
  | invalidOptions (e : OptionError)
  | unsupported    (feature : String)        -- known SoPlex limitation
  | parameter      (msg : String)            -- SoPlex rejected an Options field
  | missingApi     (feature : String)        -- linked SoPlex lacks an accessor
  | parseError     (path : String) (msg : String)
  | bridge         (msg : String)            -- FFI-level failure that didn't panic
  deriving Repr

/-- Exact LP solve: iterative refinement + GMP, with optional precision
boosting fallback. Returned primal and `Solution.objective` are exact
rationals for the LP SoPlex actually solved (which is the *presolved*
form when `Options.presolve = true`); the returned `Certificate` is
only expected to verify against the original `Problem` when
`Options.presolve = false`. -/
@[extern "lean_soplex_solve_exact"]
opaque solveExact (opts : Options) (p : Problem) : Except SolveError Solution

/-- Float-only solve. Useful as a preconditioner or feasibility check.
**Not** safe to feed into the verifier: the returned rationals are
exact representations of `Float`s, not exact-mode certificates. The
distinct return type makes this hard to do by accident. -/
@[extern "lean_soplex_solve_float"]
opaque solveFloat (opts : Options) (p : Problem) : Except SolveError FloatSolution

/-- MPS / LP file I/O. Pure-ish opaque FFI (file system effects are
hidden by the same trick as `solveExact`'s CPU use). Round-trips are
*mathematical*, not structural — the formats lose names, may reorder
rows, and have format-specific limitations on objective offsets and
ranged rows. -/
@[extern "lean_soplex_read_mps"]
opaque readMps  : System.FilePath → Except SolveError Problem
@[extern "lean_soplex_write_mps"]
opaque writeMps : System.FilePath → Problem → Except SolveError Unit
@[extern "lean_soplex_read_lp"]
opaque readLp   : System.FilePath → Except SolveError Problem
@[extern "lean_soplex_write_lp"]
opaque writeLp  : System.FilePath → Problem → Except SolveError Unit
```

## Verification layer

The point of writing bindings instead of shelling out to a binary is
that exact-mode SoPlex returns rational certificates we can **check
independently** in pure Lean. SoPlex becomes an untrusted oracle;
wrong output — for any reason, including bugs in our own bridge —
fails the check and surfaces as `unchecked`, not as silently wrong
math.

**Invariant.** `solveVerified` calls every `check*` on the *exact
original* `Problem` value supplied by the caller (after pure-Lean
normalization via `validate`). Certificates are never checked against
data round-tripped through C++. A bridge that corrupts both the
problem it sends to SoPlex *and* the certificate it returns is still
caught, because the certificate has to match the original Lean-side
problem to pass.

### Canonical form

The math is done in **minimization** form. Maximization is reduced
via a single helper:

```lean
/-- Flip `c` and `objOffset` in place. Identity on the rest. -/
def negateObjective (p : Problem) : Problem :=
  { p with c := p.c.map Neg.neg, objOffset := -p.objOffset }

def canonicalize (sense : ObjSense) (p : Problem) : Problem :=
  match sense with
  | .minimize => p
  | .maximize => negateObjective p

/-- Sense-aware optimality, defined via the min-canonical form. -/
def IsOptimal   (p : Problem) (sense : ObjSense) (x : Array Rat) : Prop :=
  IsOptimalMin (canonicalize sense p) x
def IsUnbounded (p : Problem) (sense : ObjSense) : Prop :=
  IsUnboundedMin (canonicalize sense p)
```

`IsFeasible`/`IsInfeasible` don't depend on the objective and need no
sense parameter. Because `IsOptimal` and `IsUnbounded` are *defined*
in terms of the min-canonical predicates, there is no proof
doubling: every theorem is stated and proved once for `Min`, and the
sense-aware versions unfold to it.

The verified-driver reports `Solution.objective` in the **caller's
original sense** (including `objOffset`); internal min-canonical
values are never exposed.

Multipliers are stored as four **nonnegative** arrays in canonical
lower/upper split (the `DualBundle` from the API section). For a row
with both bounds finite (ranged constraint), this carries strictly
more information than one signed scalar would: the dual objective
genuinely depends on the decomposition, not only on the signed
difference. Each multiplier coordinate is required to be zero when
the matching bound is `none`.

### The three certificates

Each terminal status comes with finite rational evidence. Sufficient
conditions, for minimization:

- **Optimal**: primal `x*` and a `DualBundle` `(yL, yU, zL, zU)`.
  Check (1) `x*` is primal-feasible; (2) the bundle is dual-feasible
  (stationarity `Aᵀ(yL − yU) + (zL − zU) = c`, nonnegativity, and
  zero-where-absent); (3) `c·x* + objOffset = dualObj(yL, yU, zL, zU)`.
  LP weak duality then gives optimality.

- **Infeasible**: a `DualBundle` `(yL, yU, zL, zU)` satisfying the
  *homogeneous* version. Check (1) nonnegativity + zero-where-absent;
  (2) `Aᵀ(yL − yU) + (zL − zU) = 0`;
  (3) `Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ) + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ) > 0`.
  This is the four-vector Farkas certificate. It correctly handles
  infeasibility coming from column bounds alone (e.g. `x ≤ −1` with
  `0 ≤ x`) and from any row + bound combination — a row-only Farkas
  vector cannot.

  *Worked example to pin the sign convention.* The LP
  `min 0 · x   s.t.  0 ≤ x ≤ −1` (no rows, one column with both
  bounds active and inverted feasible region). Choose
  `zL = [1], zU = [1]`. Homogeneous stationarity:
  `zL − zU = 1 − 1 = 0`. ✓. Bound combination:
  `zL · cₗ − zU · cᵤ = 1·0 − 1·(−1) = 1 > 0`. ✓. Infeasible.

- **Unbounded**: a primal-feasible `x` *and* a ray `r` such that
  `x + λr` is feasible for all `λ ≥ 0` and `c·r < 0`. The recession
  cone conditions, per row and per column:

  - if `rowLoᵢ` is finite then `(Ar)ᵢ ≥ 0`;
  - if `rowHiᵢ` is finite then `(Ar)ᵢ ≤ 0`;
  - if `colLoⱼ` is finite then `rⱼ ≥ 0`;
  - if `colHiⱼ` is finite then `rⱼ ≤ 0`.

  Equality rows (both row bounds finite and equal) and boxed columns
  (both column bounds finite) collapse to `= 0`, ranged rows likewise
  to `= 0`, one-sided to the relevant inequality. Then `x + λr` is
  feasible for all `λ ≥ 0` and `c · (x + λr) → −∞`.

  The bridge must extract both `x` and `r` from SoPlex. If only the
  ray is available (some solver states return one without the
  other), `solveVerified` returns `Verified.unchecked` rather than
  fabricating a base point.

### Dual feasibility, concretely

For `min c·x + objOffset`, dual feasibility of `(yL, yU, zL, zU)` is:

```
Aᵀ(yL − yU) + (zL − zU) = c
yL, yU, zL, zU ≥ 0  (componentwise)
yLᵢ = 0   if rₗᵢ = none      (no lower bound to multiply)
yUᵢ = 0   if rᵤᵢ = none      (no upper bound to multiply)
zLⱼ = 0   if cₗⱼ = none
zUⱼ = 0   if cᵤⱼ = none
```

Dual objective:

```
dualObj = Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ) + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ) + objOffset
```

All decidable on `Rat`.

### Lean shape

```lean
namespace LeanSoplex.Verify

/-- Mathematical predicates over `Rat`. Stated in minimization form;
maximization is canonicalized away by the driver. -/
def IsFeasible   (p : Problem) (x : Array Rat) : Prop := ...
def IsOptimalMin (p : Problem) (x : Array Rat) : Prop := ...
def IsInfeasible (p : Problem) : Prop := ¬ ∃ x, IsFeasible p x
def IsUnboundedMin (p : Problem) : Prop := ...

def isPrimalFeasible  (p : Problem) (x : Array Rat)  : Bool := ...
def isDualFeasible    (p : Problem) (d : DualBundle) : Bool := ...
def isFarkasFeasible  (p : Problem) (d : DualBundle) : Bool := ...
def primalObj         (p : Problem) (x : Array Rat)  : Rat  := ...
def dualObj           (p : Problem) (d : DualBundle) : Rat  := ...
def boundCombinationPos (p : Problem) (d : DualBundle) : Bool := ...

def checkOptimal (p : Problem) (x : Array Rat) (d : DualBundle) : Bool :=
  isPrimalFeasible p x
  && isDualFeasible p d
  && primalObj p x == dualObj p d

def checkInfeasible (p : Problem) (d : DualBundle) : Bool :=
  isFarkasFeasible p d
  && boundCombinationPos p d

def checkUnbounded (p : Problem) (x ray : Array Rat) : Bool := ...
```

**Totality.** All `is*`/`check*` Booleans are total. On dimension
mismatch (wrong array lengths, sparse indices out of range, unequal
`DualBundle` array sizes) they return `false`, never panic. Callers
that have not already run `validate` get a benign `false` rather
than undefined behavior. Soundness lemmas
(`checkOptimal_sound : checkOptimal p x d = true → IsFeasible p x ∧ IsOptimalMin p x`,
analogously for `Infeasible`/`Unbounded`) bridge the `Bool` world to
the `Prop` world.

The one non-trivial proof obligation is **weak duality on `Rat`**:

```lean
theorem weak_duality
    (hx : isPrimalFeasible p x = true)
    (hd : isDualFeasible    p d = true) :
    dualObj p d ≤ primalObj p x
```

Proof shape:

```
Σⱼ cⱼ · xⱼ + objOffset
  =  Σⱼ (Aᵀ(yL − yU) + (zL − zU))ⱼ · xⱼ + objOffset      -- stationarity
  =  Σᵢ (yLᵢ − yUᵢ) · (Ax)ᵢ + Σⱼ (zLⱼ − zUⱼ) · xⱼ + objOffset
                                                          -- swap finite sums
  ≥  Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ) + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ) + objOffset
                                                          -- nonneg × bounds
  =  dualObj p d
```

Each piece of the third step uses one of
`yLᵢ ≥ 0 ∧ (Ax)ᵢ ≥ rₗᵢ ⇒ yLᵢ · (Ax)ᵢ ≥ yLᵢ · rₗᵢ` and the three
symmetric variants for the upper-row, lower-column, and upper-column
sides.

Elementary `Rat` arithmetic — but implementing it in core Lean does
need a small bespoke toolkit around `Array.foldl`, sparse-matrix
evaluation, and dot products. Budget for that; don't expect the
literal proof script to be three lines. The checker module is
**standalone** — no dependency beyond core Lean, so `lean-soplex` is
consumable from any Lean project.

`checkOptimal_sound`, `checkInfeasible_sound`, and
`checkUnbounded_sound` then follow from `weak_duality` plus the
certificate-specific equalities / strict inequalities.

### User-facing driver

```lean
/-- A proof about a specific `Problem`. The problem this is indexed
by is **always the validated/normalized form**, never the user's
raw input (which `validate` may have permuted, summed, or zero-pruned). -/
inductive Verified (p : Problem) (sense : ObjSense)
  | optimal     (x : Array Rat)
                (h : IsFeasible p x ∧ IsOptimal p sense x)
  | infeasible  (h : IsInfeasible p)
  | unbounded   (x ray : Array Rat) (h : IsUnbounded p sense)
  /-- Solver couldn't decide, or its certificate failed to verify. -/
  | unchecked   (status : SolveStatus)

/-- Result of `solveVerified`: the normalized problem the checker
actually ran against, plus the proof carried by `Verified`. The
two-piece return is necessary because callers passed in `p` but the
witness is about `validate p` — and those can be unequal as Lean
values even when mathematically equivalent. -/
structure VerifiedSolve (sense : ObjSense) where
  normalized : Problem
  verified   : Verified normalized sense

/-- Drive `validate`, `solveExact`, then the checker.

* Calls `validateOptions` and `validate` first; either failure
  surfaces as `Except.error`.
* Forces `Options.presolve := false` internally — the checker has
  to run against the original (normalized) problem, not the
  presolved version.
* `denomBudget` is a ceiling on the bit length of every rational
  coordinate in the certificate (sum of `numerator.natAbs.bitLen`
  and `denominator.bitLen` after reduction). A certificate exceeding
  the budget reports `Verified.unchecked .budgetExceeded`; `none`
  means unbounded.
* Returns `(normalized, verified)`: downstream code that wants the
  proof in terms of its own `Problem` value must reason about
  `validate p`, not `p`. -/
def solveVerified (opts : Options) (p : Problem)
    (denomBudget : Option Nat := some 10000) :
    Except SolveError (VerifiedSolve opts.sense) := ...
```

Downstream code pattern-matches on `verified` and pulls out a real
proof, not just data. The `normalized` field is the `Problem` that
proof is about — equal-up-to-normalization to the user's input.

### What this catches

A non-verifying certificate fires for any of:

1. A SoPlex bug — wrong basis, refinement step gone wrong, exact-mode
   parameters not set correctly.
2. A bridge bug — mis-decoded `Rat`s (small-int vs boxed case
   confused), dropped sparse entries, sign confusion in the SoPlex →
   canonical-form translation.
3. Convention mismatch — our nonneg lower/upper rule disagrees with
   the bridge's translation of `getDualRational` /
   `getRedCostRational` / `getDualFarkasRational` for some
   row-sense × column-status combo.
4. **Presolve leakage** — if SoPlex's presolve transforms the LP
   before solving, returned certificates describe the presolved LP,
   not the original, and won't pass the checker. `solveVerified`
   forces `Options.presolve := false`; users calling `solveExact`
   directly with presolve on get a fast exact-rational answer but
   should expect `Verified.unchecked` if they then feed it to the
   verifier. Bringing presolve into the verified path requires
   reconstructing the original-problem certificate from SoPlex's
   presolve transcript — tracked at
   https://github.com/kim-em/lean-soplex/issues/1.

### What it does *not* check

- The user's intent. `Verified.optimal` proves things about the
  `Problem` value passed in, not about whatever LP the user meant to
  construct. Standard caveat for all proof-producing tools.
- MILP. The LP layer is a building block for verified MILP, but
  branching and cutting-plane certificates are a separate story.
- Cost of checking. Certificates with astronomical denominators can
  be slow to verify. In practice exact-mode SoPlex produces tame
  ones; the checker can optionally accept a denominator budget and
  fall back to `unchecked` past it.

### SoPlex API ↔ canonical form translation

SoPlex's rational accessors (`getPrimalRational`,
`getPrimalRayRational`, `getDualRational`, `getRedCostRational`,
`getDualFarkasRational`) do **not** return data in our canonical
lower/upper split. The bridge has to translate, taking into account
row sense, bound status, objective sense, scaling/presolve state, and
SoPlex's own sign conventions. This translation is itself
**untrusted** — the verification layer catches translation bugs as
non-verifying certificates. Required artifacts:

1. Pin a SoPlex release (capture the exact tag in this doc).
2. For that release, document the meaning and sign of each accessor
   on every combination of: free / equality / one-sided / ranged
   rows; free / fixed / one-sided / boxed columns; min / max sense.
3. Golden tests per row-sense × column-status combination, in CI.

The translation is documented in `docs/accessors.md` for the
pinned `v8.0.2` release; the goldens live in `AccessorGoldens.lean`
(`lake exe accessor-goldens`) and run on every CI platform.

### Decisions (recorded for future implementers)

- **Presolve.** `solveVerified` forces it off; `solveExact` defaults
  it on. Restoring presolve on the verified path is tracked as a
  separate issue and deferred until profiling justifies the bridge
  complexity.
- **Denominator budget.** Exposed as a parameter on `solveVerified`
  (not in `Options`), default `some 10000` bits per coordinate
  (measured as `numerator.natAbs.bitLen + denominator.bitLen` after
  reduction). ≈ 3000 decimal digits combined — comfortably above
  anything real SoPlex produces, but a real ceiling. Exceeding it
  yields `Verified.unchecked .budgetExceeded`.
- **Module separation.** Two Lake `lean_lib` targets in one repo:
  `LeanSoplex.Verify` (pure-Lean checker, no FFI dep) and
  `LeanSoplex` (the FFI binding, depends on the checker). Consumers
  that only want the checker depend on the verify target alone. The
  physical separation makes "no SoPlex dependency" a build
  invariant.
- **SoPlex release.** Track the latest stable tag at the time of
  pinning. Bump on a planned schedule, not opportunistically — each
  bump may shift accessor sign conventions and require golden-test
  updates. Capture the exact tag in this doc the moment the
  submodule lands. **Currently pinned: `v8.0.2`** (April 2026,
  `SOPLEX_VERSION = 802`, internal version 9.0.0).
- **GMP linkage.** Dynamic, system-provided. Static SoPlex into the
  Lean shared library, but GMP stays a runtime dependency. Cleanest
  LGPL story and matches the `lean-csdp` precedent.
- **`Verified` indexing.** Sense-aware (`Verified p sense`), with
  `IsOptimal`/`IsUnbounded` *defined* via the min-canonical
  predicates — no proof doubling. Indexed by the **normalized**
  (post-`validate`) problem, never the user's raw input.
  `solveVerified` returns `VerifiedSolve sense`, a pair of the
  normalized problem and the witness about it, so callers can see
  exactly which problem was checked.
- **Validation type.** `validate : Problem → Except ProblemError
  Problem` returns the same type. Convention, not a newtype barrier.
  Revisit if multiple entry points start constructing `Problem`
  values without going through `validate` first.
- **Objective convention.** `Solution.objective` and the witnesses
  in `Verified` are always in the **caller's original sense**
  (including `objOffset`). Internal min-canonical values never leak
  to the API.

## System dependencies

SoPlex needs GMP **with `libgmpxx`** (the C++ wrappers, not just
`libgmp`) for exact mode. Boost is required by recent SoPlex versions
for multi-precision support inside precision boosting.

| Platform | Packages |
|----------|---|
| Linux    | `libgmp-dev libgmpxx-dev libboost-dev` |
| macOS    | `gmp boost` (Homebrew; `gmp` includes gmpxx) |
| Windows  | MSYS2 `mingw-w64-x86_64-gmp mingw-w64-x86_64-boost` |

Build flags (to pin once tested in CI): `GMP=on`, `BOOST=on`, plus
the exact-mode flags per the chosen SoPlex release. Prefer static
linking of SoPlex into the Lean shared library; respect GMP's LGPL
when deciding static vs dynamic for GMP itself.

Vendoring: git submodule `scipopt/soplex` pinned to a tagged release.
Build via SoPlex's bundled CMake invoked from the lakefile. The exact
release tag and the exact CMake flag set go in this document once
chosen.

## Test corpus

CI must run, at minimum:

- An optimal LP with a known rational answer (tiny, hand-computed).
- An infeasible LP whose infeasibility comes from the rows alone,
  checking the Farkas certificate verifies.
- An infeasible LP whose infeasibility comes from **column bounds
  alone** (e.g. `x ≤ −1` with `0 ≤ x`) — the four-vector Farkas form
  is required.
- An infeasible LP whose infeasibility needs both rows *and* bounds.
- An unbounded LP, checking the `(x, ray)` pair verifies.
- A ranged-row LP (both `lo` and `hi` finite, `lo < hi`) — exercises
  the four-vector dual storage in the optimal case.
- An LP with duplicate sparse entries, equality rows, and one-sided
  bounds — exercises `validate`'s normalization.
- An LP with large numerator/denominator rationals (multi-digit GMP).
- An ill-conditioned LP where the float solve disagrees with the
  exact solve, confirming exact mode produces the expected verified
  answer.
- A denominator-budget regression: a tiny LP whose certificate
  legitimately fits well under the default budget, and an
  artificially-constructed certificate (or budget set absurdly low)
  that should trip `.budgetExceeded`.
- A maximization-sense LP, exercising the max → min canonicalization
  end-to-end.
- For each accessor / row-sense / column-status combination, a
  one-row LP that pins down the SoPlex → canonical-form translation
  (golden tests for the bridge).
- Round-trip `writeMps` ∘ `readMps` (and same for LP format) on the
  corpus, asserting **mathematical equivalence** (objective and
  constraint sets coincide after normalization) rather than
  structural equality of the `Problem` value.

Each problem runs `validate`, then `solveExact`, then the
verification layer. CI fails if any step reports an unexpected
status, or if a certificate fails to verify.

## Implementation order

A fresh implementer should work through these in order. Several of
the choices in earlier steps appear in later signatures; flipping
them later means redoing public types.

1. **Pin the SoPlex tag and exact CMake flags.** Capture both in this
   doc. Bridge signatures and golden tests depend on the accessor
   semantics of a specific release.
2. **Define the normalized-`Problem` semantics.** Implement
   `validate`, `validateOptions`, and the totality conventions for
   the checker (false-on-mismatch, sparse-matrix interpretation).
   No SoPlex yet.
3. **Implement the pure checker.** `LeanSoplex.Verify` as a
   standalone Lake library: predicates, `is*`/`check*` Booleans,
   `weak_duality`, the three `check*_sound` lemmas, the
   sense-canonicalization wrappers, the denominator-budget check.
   Drive it from hand-rolled tiny certificates with no SoPlex
   involvement. All CI for the verify library should be green
   before any FFI work.
4. **Write the bridge skeleton + SoPlex API translation.** Stand up
   the FFI plumbing, decode `Rat`s, translate `getPrimalRational`
   etc. into the canonical `DualBundle` form for the pinned SoPlex
   release. Test purely via golden one-row LPs per
   row-sense × column-status combo — no `solveVerified` yet.
5. **Wire up `solveExact` and `solveFloat`.** Both with `Options`,
   structured errors, and the presolve-on default. Test via the
   non-verified part of the corpus.
6. **Wire up `solveVerified` last.** Compose
   `validateOptions` + `validate` + presolve-off `solveExact` +
   `check*` + budget enforcement. Add the maximization-canonicalization
   wrapper. Run the full test corpus.
7. **File I/O entry points** (`readMps`/`writeMps`/`readLp`/`writeLp`)
   can land in parallel with steps 4–6; they share the bridge
   infrastructure but not the certificate path.
8. **README + LICENSE** alongside the first user-visible commit.
