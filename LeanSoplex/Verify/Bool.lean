/-
  Boolean (decidable) certificate checkers.

  All `is*` and `check*` functions are *total*: any kind of structural
  mismatch (wrong array lengths, out-of-range sparse indices, unequal
  `DualBundle` array sizes) returns `false` rather than panicking.
  Callers that have not run `validate` get a benign `false` instead
  of undefined behaviour.

  Soundness lemmas live in `LeanSoplex.Verify.Sound`; they lift these
  `Bool` checks to the `Prop` predicates in `LeanSoplex.Verify.Prop`.
-/

import LeanSoplex.Verify.Types

namespace LeanSoplex.Verify

open LeanSoplex

/-! ## Problem shape sanity check.

  Every public `is*` / `check*` function below calls `problemShapeOk`
  first. Without this guard, a malformed `Problem` (e.g. wrong
  `rowBounds` length, out-of-range sparse entries) would reach `[i]!`
  accesses that panic. PLAN.md §"Totality" mandates that the checker
  return `false` on any structural mismatch rather than panic, so
  callers that bypass `validate` get a benign rejection. -/

/-- Structural well-formedness for a `Problem`: declared array lengths
    match `numVars` / `numConstraints`, and every sparse entry's
    `(row, col)` is in range. Implemented as a conjunction of size
    checks and an `Array.all` over the sparse entries so the
    soundness layer can extract each conjunct via `decide_eq_true_iff`
    and `Array.all_eq_true`. -/
def problemShapeOk (p : Problem) : Bool :=
  decide (p.c.size = p.numVars)
  && decide (p.colBounds.size = p.numVars)
  && decide (p.rowBounds.size = p.numConstraints)
  && p.a.all (fun entry =>
       decide (entry.1 < p.numConstraints) && decide (entry.2.1 < p.numVars))

/-! ## Sparse matrix arithmetic.

  Stated via `Array.foldl` rather than a `for` loop with an early-exit
  range. Both forms are semantically equivalent on well-shaped `p`, but
  the `foldl` form is what `Array.foldl_induction` (core Lean) operates
  on, so reasoning in `LeanSoplex.Verify.Arith` is direct.
-/

/-- Apply a single sparse entry `(r, c, v)` to the accumulator: add
    `v * x[c]!` into slot `r` of `out`, defensively skipping the entry
    if either index is out of range. Both `out` and `x` keep their
    sizes. -/
@[inline] def applyAx (x : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) : Array Rat :=
  let (r, c, v) := entry
  if h : r < out.size ∧ c < x.size then
    out.set r (out[r]! + v * x[c]!) h.1
  else out

/-- Apply a single sparse entry `(r, c, v)` to the transposed
    accumulator: add `v * y[r]!` into slot `c` of `out`. -/
@[inline] def applyATy (y : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) : Array Rat :=
  let (r, c, v) := entry
  if h : c < out.size ∧ r < y.size then
    out.set c (out[c]! + v * y[r]!) h.1
  else out

/-- Compute `Ax` as an `Array Rat` of length `p.numConstraints`. -/
def evalAx (p : Problem) (x : Array Rat) : Array Rat :=
  p.a.foldl (applyAx x) (Array.replicate p.numConstraints 0)

/-- Compute `Aᵀy` as an `Array Rat` of length `p.numVars`. -/
def evalATy (p : Problem) (y : Array Rat) : Array Rat :=
  p.a.foldl (applyATy y) (Array.replicate p.numVars 0)

/-- Dot product of two same-length `Array Rat`. Returns `0` on length
    mismatch (falls into the "false" branch of any caller).
    Implemented via `Array.zipWith` + `Array.foldl` so the soundness
    layer's `dot_set` / linearity lemmas can use `Array.foldl_induction`
    directly. -/
def dot (a b : Array Rat) : Rat :=
  if a.size = b.size then
    (Array.zipWith (fun x y => x * y) a b).foldl (· + ·) 0
  else 0

/-! ## Bound checks. -/

/-- `x ≥ lo` where `lo = none` is `−∞` (so the check is vacuous). -/
@[inline] def geLB (x : Rat) (lo : Option Rat) : Bool :=
  match lo with | none => true | some l => l ≤ x

/-- `x ≤ hi` where `hi = none` is `+∞` (so the check is vacuous). -/
@[inline] def leUB (x : Rat) (hi : Option Rat) : Bool :=
  match hi with | none => true | some h => x ≤ h

/-! ## Primal feasibility. -/

/-- Decide whether `x` is primal-feasible for the (normalised) `p`. -/
def isPrimalFeasible (p : Problem) (x : Array Rat) : Bool :=
  problemShapeOk p
  && decide (x.size = p.numVars)
  && (Array.range p.numVars).all (fun j =>
       let (lo, hi) := p.colBounds[j]!
       geLB x[j]! lo && leUB x[j]! hi)
  && let ax := evalAx p x
     (Array.range p.numConstraints).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       geLB ax[i]! lo && leUB ax[i]! hi)

/-! ## Dual feasibility. -/

/-- Each `DualBundle` array must have the right length, every entry
    must be nonnegative, and any coordinate matching an absent bound
    must be zero. -/
def dualNonnegAndZeroWhereAbsent (p : Problem) (d : DualBundle) : Bool :=
  problemShapeOk p
  && decide (d.rowLower.size = p.numConstraints)
  && decide (d.rowUpper.size = p.numConstraints)
  && decide (d.colLower.size = p.numVars)
  && decide (d.colUpper.size = p.numVars)
  && (Array.range p.numConstraints).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       decide (0 ≤ d.rowLower[i]!)
       && decide (0 ≤ d.rowUpper[i]!)
       && (!lo.isNone || decide (d.rowLower[i]! = 0))
       && (!hi.isNone || decide (d.rowUpper[i]! = 0)))
  && (Array.range p.numVars).all (fun j =>
       let (lo, hi) := p.colBounds[j]!
       decide (0 ≤ d.colLower[j]!)
       && decide (0 ≤ d.colUpper[j]!)
       && (!lo.isNone || decide (d.colLower[j]! = 0))
       && (!hi.isNone || decide (d.colUpper[j]! = 0)))

/-- Componentwise subtraction of two same-length `Array Rat`. Returns
    `#[]` on length mismatch — that disagrees with `c` in size, which
    causes the equality check in `isDualFeasible` to fail benignly.
    Implemented via `Array.zipWith` so the soundness layer can use
    `getElem_zipWith` directly. -/
def arraySub (a b : Array Rat) : Array Rat :=
  if a.size = b.size then Array.zipWith (· - ·) a b else #[]

/-- Equality of two `Array Rat`s. Implemented as a size precheck plus
    a pairwise comparison over `Array.zip` so the soundness layer can
    extract size and per-index equality via `Array.all_eq_true`. -/
def arrayEq (a b : Array Rat) : Bool :=
  decide (a.size = b.size) && (a.zip b).all (fun ⟨x, y⟩ => x == y)

/-- Stationarity check: `Aᵀ(yL − yU) + (zL − zU) = c`. -/
def isStationary (p : Problem) (d : DualBundle) : Bool :=
  let aty := evalATy p (arraySub d.rowLower d.rowUpper)
  let zdiff := arraySub d.colLower d.colUpper
  arrayEq (Array.zipWith (· + ·) aty zdiff) p.c

/-- Dual feasibility for the optimality certificate. -/
def isDualFeasible (p : Problem) (d : DualBundle) : Bool :=
  dualNonnegAndZeroWhereAbsent p d && isStationary p d

/-- Farkas (homogeneous) dual feasibility: same shape, but with
    stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` instead of `= c`. -/
def isFarkasFeasible (p : Problem) (d : DualBundle) : Bool :=
  let aty := evalATy p (arraySub d.rowLower d.rowUpper)
  let zdiff := arraySub d.colLower d.colUpper
  dualNonnegAndZeroWhereAbsent p d
  && (Array.zipWith (· + ·) aty zdiff).all (· == 0)

/-! ## Objective values. -/

/-- Primal objective `c · x + objOffset`. Returns `objOffset` on
    length mismatch. -/
def primalObj (p : Problem) (x : Array Rat) : Rat :=
  dot p.c x + p.objOffset

/-- Contribution of a single optional lower bound: `mult * lo` or `0`. -/
@[inline] private def loContrib (lo : Option Rat) (mult : Rat) : Rat :=
  lo.elim 0 (mult * ·)

/-- Contribution of a single optional upper bound: `mult * hi` or `0`. -/
@[inline] private def hiContrib (hi : Option Rat) (mult : Rat) : Rat :=
  hi.elim 0 (mult * ·)

/-- The bound combination underlying `dualObj` and `boundCombinationPos`:
    `Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ) + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ)`. Returns
    `0` on any structural mismatch. The `+ objOffset` for `dualObj`
    and the strict-positive check for `boundCombinationPos` are
    layered on top. -/
def dualBoundCombination (p : Problem) (d : DualBundle) : Rat :=
  if problemShapeOk p
     && decide (d.rowLower.size = p.numConstraints)
     && decide (d.rowUpper.size = p.numConstraints)
     && decide (d.colLower.size = p.numVars)
     && decide (d.colUpper.size = p.numVars) then
    let rowPart := (Array.range p.numConstraints).foldl (fun (acc : Rat) i =>
      let (lo, hi) := p.rowBounds[i]!
      acc + loContrib lo d.rowLower[i]! - hiContrib hi d.rowUpper[i]!) 0
    let colPart := (Array.range p.numVars).foldl (fun (acc : Rat) j =>
      let (lo, hi) := p.colBounds[j]!
      acc + loContrib lo d.colLower[j]! - hiContrib hi d.colUpper[j]!) 0
    rowPart + colPart
  else 0

/-- Dual objective in the canonical lower/upper split form:

      Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ)
    + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ)
    + objOffset

    A coordinate contributes zero whenever the matching bound is `none`
    (regardless of the multiplier — see `dualNonnegAndZeroWhereAbsent`).

    Returns `objOffset` on any structural mismatch — `dualBoundCombination`
    short-circuits to `0` on a malformed problem, so the only term that
    survives is the offset. `checkOptimal` always requires
    `isDualFeasible` to hold before consulting this value, so the
    mismatch case is unreachable for accepted certificates. -/
def dualObj (p : Problem) (d : DualBundle) : Rat :=
  dualBoundCombination p d + p.objOffset

/-- The Farkas strict-positivity step: the bound combination must be
    strictly positive (with the same convention as `dualObj`, but
    without the `objOffset`). Returns `false` on any structural
    mismatch (in which case `dualBoundCombination` returns `0`, which
    is not strictly positive). -/
def boundCombinationPos (p : Problem) (d : DualBundle) : Bool :=
  decide (0 < dualBoundCombination p d)

/-! ## Top-level checks for each certificate kind. -/

/-- Optimal certificate: primal feasibility, dual feasibility, and
    strong duality `c·x* + objOffset = dualObj`. -/
def checkOptimal (p : Problem) (x : Array Rat) (d : DualBundle) : Bool :=
  isPrimalFeasible p x
  && isDualFeasible p d
  && primalObj p x == dualObj p d

/-- Infeasibility (Farkas) certificate: homogeneous dual feasibility
    plus strict-positive bound combination. -/
def checkInfeasible (p : Problem) (d : DualBundle) : Bool :=
  isFarkasFeasible p d
  && boundCombinationPos p d

/-- Recession-cone check for an unbounded ray. Each row / column with
    a finite bound on a given side produces the corresponding sign
    constraint on the corresponding `(Ar)ᵢ` / `rⱼ`. Equality rows /
    boxed columns collapse to `= 0`. -/
def isRecessionRay (p : Problem) (r : Array Rat) : Bool :=
  problemShapeOk p
  && decide (r.size = p.numVars)
  && (Array.range p.numVars).all (fun j =>
       let (lo, hi) := p.colBounds[j]!
       (!lo.isSome || decide (0 ≤ r[j]!))
       && (!hi.isSome || decide (r[j]! ≤ 0)))
  && let ar := evalAx p r
     (Array.range p.numConstraints).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       (!lo.isSome || decide (0 ≤ ar[i]!))
       && (!hi.isSome || decide (ar[i]! ≤ 0)))

/-- Unbounded certificate: a feasible base point and an improving
    recession ray. -/
def checkUnbounded (p : Problem) (x ray : Array Rat) : Bool :=
  isPrimalFeasible p x
  && isRecessionRay p ray
  && dot p.c ray < 0

end LeanSoplex.Verify
