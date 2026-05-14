/-
  Boolean (decidable) certificate checkers.

  All `is*` and `check*` functions are *total*: any kind of structural
  mismatch (wrong array lengths, out-of-range sparse indices, unequal
  `DualBundle` array sizes) returns `false` rather than panicking.
  Callers that have not run `validate` get a benign `false` instead
  of undefined behaviour.

  Soundness lemmas live in `Soplex.Verify.Sound`; they lift these
  `Bool` checks to the `Prop` predicates in `Soplex.Verify.Prop`.
-/

import Soplex.Verify.Types

namespace Soplex.Verify

open Soplex

/-! ## Problem shape sanity check.

  Every public `is*` / `check*` function below calls `problemShapeOk`
  first. Without this guard, a malformed `Problem` (e.g. wrong
  `rowBounds` length, out-of-range sparse entries) would reach `[i]!`
  accesses that panic. The checker returns `false` on structural
  mismatch so callers that bypass `validate` get a benign rejection. -/

/-- Structural well-formedness for a `Problem`: every sparse entry's
    `(row, col)` is in range. Length checks for `c`, `colBounds`, and
    `rowBounds` used to live here too, but with `Problem`'s `Vector`
    fields those sizes are guaranteed by the type. Implemented as
    `Array.all` over the sparse entries so the soundness layer can
    extract per-entry facts via `Array.all_eq_true`. -/
def problemShapeOk {m n : Nat} (p : Problem m n) : Bool :=
  p.a.all (fun entry =>
    decide (entry.1 < m) && decide (entry.2.1 < n))

/-! ## Sparse matrix arithmetic.

  Stated via `Array.foldl` rather than a `for` loop with an early-exit
  range. Both forms are semantically equivalent on well-shaped `p`, but
  the `foldl` form is what `Array.foldl_induction` (core Lean) operates
  on, so reasoning in `Soplex.Verify.Arith` is direct.
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

/-- Compute `Ax` as an `Array Rat` of length `m`. -/
def evalAx {m n : Nat} (p : Problem m n) (x : Array Rat) : Array Rat :=
  p.a.foldl (applyAx x) (Array.replicate m 0)

/-- Compute `Aᵀy` as an `Array Rat` of length `n`. -/
def evalATy {m n : Nat} (p : Problem m n) (y : Array Rat) : Array Rat :=
  p.a.foldl (applyATy y) (Array.replicate n 0)

/-! ### Output-size lemmas for `evalAx` / `evalATy`.

  Stated here so `vEvalAx` / `vEvalATy` below can package the size
  facts into the type. The proofs go via `Array.foldl_induction`,
  which is the canonical core-Lean structural induction over the
  sparse-entry foldl. -/

/-- `applyAx` preserves the output array's size. -/
theorem applyAx_size (x : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) :
    (applyAx x out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : r < out.size ∧ c < x.size
       then out.set r (out[r]! + v * x[c]!) h.1 else out).size = out.size
  by_cases h : r < out.size ∧ c < x.size
  · simp [h, Array.size_set]
  · simp [h]

/-- `applyATy` preserves the output array's size. -/
theorem applyATy_size (y : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) :
    (applyATy y out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : c < out.size ∧ r < y.size
       then out.set c (out[c]! + v * y[r]!) h.1 else out).size = out.size
  by_cases h : c < out.size ∧ r < y.size
  · simp [h, Array.size_set]
  · simp [h]

theorem evalAx_size {m n : Nat} (p : Problem m n) (x : Array Rat) :
    (evalAx p x).size = m := by
  unfold evalAx
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = m) ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyAx_size]; exact hAcc

theorem evalATy_size {m n : Nat} (p : Problem m n) (y : Array Rat) :
    (evalATy p y).size = n := by
  unfold evalATy
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = n) ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyATy_size]; exact hAcc

/-- `Aᵀy` packaged as a `Vector Rat n`. The output-size obligation is
    discharged by `evalATy_size`, so callers never have to re-derive
    it. The input `y` is kept `Array`-shaped because in practice it
    arrives as `vSub d.rowLower d.rowUpper` whose Vector size differs
    structurally from `p`'s dimensions even when numerically equal. -/
@[inline] def vEvalATy {m n : Nat} (p : Problem m n) (y : Array Rat) :
    Vector Rat n :=
  ⟨evalATy p y, evalATy_size p y⟩

/-- `Ax` packaged as a `Vector Rat m`. Dual to `vEvalATy`. -/
@[inline] def vEvalAx {m n : Nat} (p : Problem m n) (x : Array Rat) :
    Vector Rat m :=
  ⟨evalAx p x, evalAx_size p x⟩

@[simp] theorem vEvalAx_toArray {m n : Nat} (p : Problem m n) (x : Array Rat) :
    (vEvalAx p x).toArray = evalAx p x := rfl

@[simp] theorem vEvalATy_toArray {m n : Nat} (p : Problem m n) (y : Array Rat) :
    (vEvalATy p y).toArray = evalATy p y := rfl

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
def isPrimalFeasible {m n : Nat} (p : Problem m n) (x : Vector Rat n) : Bool :=
  problemShapeOk p
  && (Array.range n).all (fun j =>
       let (lo, hi) := p.colBounds[j]!
       geLB x[j]! lo && leUB x[j]! hi)
  && let ax := evalAx p x.toArray
     (Array.range m).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       geLB ax[i]! lo && leUB ax[i]! hi)

/-! ## Dual feasibility. -/

/-- Each `DualBundle` vector matches the problem's dimensions in its
    type; here we additionally check that every entry is nonnegative,
    and any coordinate matching an absent bound is zero. The `m = …`
    `n = …` size guards remain explicit because `d.rowLower.size = m`
    is definitional but `m = m` is not. -/
def dualNonnegAndZeroWhereAbsent {m n : Nat}
    (p : Problem m n) (d : DualBundle m n) : Bool :=
  problemShapeOk p
  && (Array.range m).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       decide (0 ≤ d.rowLower[i]!)
       && decide (0 ≤ d.rowUpper[i]!)
       && (!lo.isNone || decide (d.rowLower[i]! = 0))
       && (!hi.isNone || decide (d.rowUpper[i]! = 0)))
  && (Array.range n).all (fun j =>
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

/-- Vector-typed componentwise subtraction. Same as `arraySub` but the
    type signature rules out the length-mismatch case at the boundary
    instead of pushing it to a runtime `if`. -/
@[inline] def vSub {n : Nat} (a b : Vector Rat n) : Vector Rat n :=
  Vector.zipWith (· - ·) a b

/-- Vector-typed dot product. Same as `dot` but the type rules out the
    length-mismatch case, so there is no `if a.size = b.size` guard
    and no zero-on-mismatch fallback. -/
@[inline] def vDot {n : Nat} (a b : Vector Rat n) : Rat :=
  (Vector.zipWith (· * ·) a b).toArray.foldl (· + ·) 0

/-- Equality of two `Array Rat`s. Implemented as a size precheck plus
    a pairwise comparison over `Array.zip` so the soundness layer can
    extract size and per-index equality via `Array.all_eq_true`. -/
def arrayEq (a b : Array Rat) : Bool :=
  decide (a.size = b.size) && (a.zip b).all (fun ⟨x, y⟩ => x == y)

/-- Stationarity check: `Aᵀ(yL − yU) + (zL − zU) = c`. All three
    operands live in `Vector Rat n` so the componentwise sum has a
    fixed length matching `p.c`; the per-index equality is folded
    into a single `decide` predicate. -/
def isStationary {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  let aty   : Vector Rat n := vEvalATy p (vSub d.rowLower d.rowUpper).toArray
  let zdiff : Vector Rat n := vSub d.colLower d.colUpper
  decide (Vector.zipWith (· + ·) aty zdiff = p.c)

/-- Dual feasibility for the optimality certificate. -/
def isDualFeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  dualNonnegAndZeroWhereAbsent p d && isStationary p d

/-- Farkas (homogeneous) dual feasibility: same shape, but with
    stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` instead of `= c`. -/
def isFarkasFeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  let aty   : Vector Rat n := vEvalATy p (vSub d.rowLower d.rowUpper).toArray
  let zdiff : Vector Rat n := vSub d.colLower d.colUpper
  dualNonnegAndZeroWhereAbsent p d
  && (Vector.zipWith (· + ·) aty zdiff).all (· == 0)

/-! ## Objective values. -/

/-- Primal objective `c · x + objOffset`. Returns `objOffset` on
    length mismatch. -/
def primalObj {m n : Nat} (p : Problem m n) (x : Array Rat) : Rat :=
  dot p.c.toArray x + p.objOffset

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
def dualBoundCombination {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Rat :=
  if problemShapeOk p then
    let rowPart := (Array.range m).foldl (fun (acc : Rat) i =>
      let (lo, hi) := p.rowBounds[i]!
      acc + loContrib lo d.rowLower[i]! - hiContrib hi d.rowUpper[i]!) 0
    let colPart := (Array.range n).foldl (fun (acc : Rat) j =>
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
def dualObj {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Rat :=
  dualBoundCombination p d + p.objOffset

/-- The Farkas strict-positivity step: the bound combination must be
    strictly positive (with the same convention as `dualObj`, but
    without the `objOffset`). Returns `false` on any structural
    mismatch (in which case `dualBoundCombination` returns `0`, which
    is not strictly positive). -/
def boundCombinationPos {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  decide (0 < dualBoundCombination p d)

/-! ## Top-level checks for each certificate kind. -/

/-- Optimal certificate: primal feasibility, dual feasibility, and
    strong duality `c·x* + objOffset = dualObj`. -/
def checkOptimal {m n : Nat}
    (p : Problem m n) (x : Vector Rat n) (d : DualBundle m n) : Bool :=
  isPrimalFeasible p x
  && isDualFeasible p d
  && primalObj p x.toArray == dualObj p d

/-- Infeasibility (Farkas) certificate: homogeneous dual feasibility
    plus strict-positive bound combination. -/
def checkInfeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  isFarkasFeasible p d
  && boundCombinationPos p d

/-- Recession-cone check for an unbounded ray. Each row / column with
    a finite bound on a given side produces the corresponding sign
    constraint on the corresponding `(Ar)ᵢ` / `rⱼ`. Equality rows /
    boxed columns collapse to `= 0`. -/
def isRecessionRay {m n : Nat} (p : Problem m n) (r : Vector Rat n) : Bool :=
  problemShapeOk p
  && (Array.range n).all (fun j =>
       let (lo, hi) := p.colBounds[j]!
       (!lo.isSome || decide (0 ≤ r[j]!))
       && (!hi.isSome || decide (r[j]! ≤ 0)))
  && let ar := evalAx p r.toArray
     (Array.range m).all (fun i =>
       let (lo, hi) := p.rowBounds[i]!
       (!lo.isSome || decide (0 ≤ ar[i]!))
       && (!hi.isSome || decide (ar[i]! ≤ 0)))

/-- Unbounded certificate: a feasible base point and an improving
    recession ray. -/
def checkUnbounded {m n : Nat} (p : Problem m n) (x ray : Vector Rat n) : Bool :=
  isPrimalFeasible p x
  && isRecessionRay p ray
  && dot p.c.toArray ray.toArray < 0

end Soplex.Verify
