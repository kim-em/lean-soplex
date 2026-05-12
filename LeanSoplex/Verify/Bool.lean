/-
  Boolean (decidable) certificate checkers.

  All `is*` and `check*` functions are *total*: any kind of structural
  mismatch (wrong array lengths, out-of-range sparse indices, unequal
  `DualBundle` array sizes) returns `false` rather than panicking.
  Callers that have not run `validate` get a benign `false` instead
  of undefined behaviour.

  Soundness lemmas live in `LeanSoplex.Verify.Sound`; they bridge from
  these `Bool` checks to the `Prop` predicates in
  `LeanSoplex.Verify.Prop`.
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
    `(row, col)` is in range. -/
def problemShapeOk (p : Problem) : Bool := Id.run do
  if p.c.size ≠ p.numVars then return false
  if p.colBounds.size ≠ p.numVars then return false
  if p.rowBounds.size ≠ p.numConstraints then return false
  for k in [0:p.a.size] do
    let (r, c, _) := p.a[k]!
    if r ≥ p.numConstraints || c ≥ p.numVars then return false
  return true

/-! ## Sparse matrix arithmetic. -/

/-- Compute `Ax` as an `Array Rat` of length `p.numConstraints`. -/
def evalAx (p : Problem) (x : Array Rat) : Array Rat := Id.run do
  let mut out : Array Rat := Array.replicate p.numConstraints 0
  for k in [0:p.a.size] do
    let (r, c, v) := p.a[k]!
    if h : r < out.size ∧ c < x.size then
      out := out.set r (out[r]! + v * x[c]!) (by exact h.1)
  return out

/-- Compute `Aᵀy` as an `Array Rat` of length `p.numVars`. -/
def evalATy (p : Problem) (y : Array Rat) : Array Rat := Id.run do
  let mut out : Array Rat := Array.replicate p.numVars 0
  for k in [0:p.a.size] do
    let (r, c, v) := p.a[k]!
    if h : c < out.size ∧ r < y.size then
      out := out.set c (out[c]! + v * y[r]!) (by exact h.1)
  return out

/-- Dot product of two same-length `Array Rat`. Returns `0` on length
    mismatch (falls into the "false" branch of any caller). -/
def dot (a b : Array Rat) : Rat := Id.run do
  if a.size ≠ b.size then return 0
  let mut acc : Rat := 0
  for i in [0:a.size] do
    acc := acc + a[i]! * b[i]!
  return acc

/-! ## Bound checks. -/

/-- `x ≥ lo` where `lo = none` is `−∞` (so the check is vacuous). -/
@[inline] def geLB (x : Rat) (lo : Option Rat) : Bool :=
  match lo with | none => true | some l => l ≤ x

/-- `x ≤ hi` where `hi = none` is `+∞` (so the check is vacuous). -/
@[inline] def leUB (x : Rat) (hi : Option Rat) : Bool :=
  match hi with | none => true | some h => x ≤ h

/-! ## Primal feasibility. -/

/-- Decide whether `x` is primal-feasible for the (normalised) `p`. -/
def isPrimalFeasible (p : Problem) (x : Array Rat) : Bool := Id.run do
  if !problemShapeOk p then return false
  if x.size ≠ p.numVars then return false
  -- Column bounds.
  for j in [0:p.numVars] do
    let (lo, hi) := p.colBounds[j]!
    unless geLB x[j]! lo && leUB x[j]! hi do return false
  -- Row bounds.
  let ax := evalAx p x
  for i in [0:p.numConstraints] do
    let (lo, hi) := p.rowBounds[i]!
    unless geLB ax[i]! lo && leUB ax[i]! hi do return false
  return true

/-! ## Dual feasibility. -/

/-- Each `DualBundle` array must have the right length, every entry
    must be nonnegative, and any coordinate matching an absent bound
    must be zero. -/
def dualNonnegAndZeroWhereAbsent (p : Problem) (d : DualBundle) : Bool := Id.run do
  if !problemShapeOk p then return false
  if d.rowLower.size ≠ p.numConstraints then return false
  if d.rowUpper.size ≠ p.numConstraints then return false
  if d.colLower.size ≠ p.numVars        then return false
  if d.colUpper.size ≠ p.numVars        then return false
  for i in [0:p.numConstraints] do
    let (lo, hi) := p.rowBounds[i]!
    if d.rowLower[i]! < 0 then return false
    if d.rowUpper[i]! < 0 then return false
    if lo.isNone && d.rowLower[i]! ≠ 0 then return false
    if hi.isNone && d.rowUpper[i]! ≠ 0 then return false
  for j in [0:p.numVars] do
    let (lo, hi) := p.colBounds[j]!
    if d.colLower[j]! < 0 then return false
    if d.colUpper[j]! < 0 then return false
    if lo.isNone && d.colLower[j]! ≠ 0 then return false
    if hi.isNone && d.colUpper[j]! ≠ 0 then return false
  return true

/-- Componentwise subtraction of two same-length `Array Rat`. Returns
    `#[]` on length mismatch — that disagrees with `c` in size, which
    causes the equality check in `isDualFeasible` to fail benignly. -/
def arraySub (a b : Array Rat) : Array Rat := Id.run do
  if a.size ≠ b.size then return #[]
  let mut out : Array Rat := Array.mkEmpty a.size
  for i in [0:a.size] do
    out := out.push (a[i]! - b[i]!)
  return out

/-- Equality of two same-length `Array Rat`. -/
def arrayEq (a b : Array Rat) : Bool := Id.run do
  if a.size ≠ b.size then return false
  for i in [0:a.size] do
    if a[i]! ≠ b[i]! then return false
  return true

/-- Stationarity check: `Aᵀ(yL − yU) + (zL − zU) = c`. -/
def isStationary (p : Problem) (d : DualBundle) : Bool :=
  let aty := evalATy p (arraySub d.rowLower d.rowUpper)
  let zdiff := arraySub d.colLower d.colUpper
  if aty.size ≠ zdiff.size then false
  else
    arrayEq (Id.run do
      let mut out : Array Rat := Array.mkEmpty aty.size
      for i in [0:aty.size] do
        out := out.push (aty[i]! + zdiff[i]!)
      return out) p.c

/-- Dual feasibility for the optimality certificate. -/
def isDualFeasible (p : Problem) (d : DualBundle) : Bool :=
  dualNonnegAndZeroWhereAbsent p d && isStationary p d

/-- Farkas (homogeneous) dual feasibility: same shape, but with
    stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` instead of `= c`. -/
def isFarkasFeasible (p : Problem) (d : DualBundle) : Bool := Id.run do
  if !dualNonnegAndZeroWhereAbsent p d then return false
  let aty := evalATy p (arraySub d.rowLower d.rowUpper)
  let zdiff := arraySub d.colLower d.colUpper
  if aty.size ≠ zdiff.size then return false
  for i in [0:aty.size] do
    if aty[i]! + zdiff[i]! ≠ 0 then return false
  return true

/-! ## Objective values. -/

/-- Primal objective `c · x + objOffset`. Returns `objOffset` on
    length mismatch. -/
def primalObj (p : Problem) (x : Array Rat) : Rat :=
  dot p.c x + p.objOffset

/-- Dual objective in the canonical lower/upper split form:

      Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ)
    + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ)
    + objOffset

    A coordinate contributes zero whenever the matching bound is `none`
    (regardless of the multiplier — see `dualNonnegAndZeroWhereAbsent`).

    Returns `0` on any structural mismatch (problem-shape or dual-bundle
    size) so the function is total; `checkOptimal` always gates on
    `isDualFeasible` before consulting this value. -/
def dualObj (p : Problem) (d : DualBundle) : Rat := Id.run do
  if !problemShapeOk p then return 0
  if d.rowLower.size ≠ p.numConstraints then return 0
  if d.rowUpper.size ≠ p.numConstraints then return 0
  if d.colLower.size ≠ p.numVars then return 0
  if d.colUpper.size ≠ p.numVars then return 0
  let mut acc : Rat := 0
  -- Rows.
  for i in [0:p.numConstraints] do
    let (lo, hi) := p.rowBounds[i]!
    match lo with
    | some l => acc := acc + d.rowLower[i]! * l
    | none   => pure ()
    match hi with
    | some h => acc := acc - d.rowUpper[i]! * h
    | none   => pure ()
  -- Columns.
  for j in [0:p.numVars] do
    let (lo, hi) := p.colBounds[j]!
    match lo with
    | some l => acc := acc + d.colLower[j]! * l
    | none   => pure ()
    match hi with
    | some h => acc := acc - d.colUpper[j]! * h
    | none   => pure ()
  acc + p.objOffset

/-- The Farkas strict-positivity step: the bound combination must be
    strictly positive (with the same convention as `dualObj`, but
    without the `objOffset`). Returns `false` on any structural
    mismatch. -/
def boundCombinationPos (p : Problem) (d : DualBundle) : Bool :=
  if !problemShapeOk p then false
  else if d.rowLower.size ≠ p.numConstraints then false
  else if d.rowUpper.size ≠ p.numConstraints then false
  else if d.colLower.size ≠ p.numVars then false
  else if d.colUpper.size ≠ p.numVars then false
  else
  (Id.run do
    let mut acc : Rat := 0
    for i in [0:p.numConstraints] do
      let (lo, hi) := p.rowBounds[i]!
      match lo with
      | some l => acc := acc + d.rowLower[i]! * l
      | none   => pure ()
      match hi with
      | some h => acc := acc - d.rowUpper[i]! * h
      | none   => pure ()
    for j in [0:p.numVars] do
      let (lo, hi) := p.colBounds[j]!
      match lo with
      | some l => acc := acc + d.colLower[j]! * l
      | none   => pure ()
      match hi with
      | some h => acc := acc - d.colUpper[j]! * h
      | none   => pure ()
    return acc) > 0

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
def isRecessionRay (p : Problem) (r : Array Rat) : Bool := Id.run do
  if !problemShapeOk p then return false
  if r.size ≠ p.numVars then return false
  for j in [0:p.numVars] do
    let (lo, hi) := p.colBounds[j]!
    if lo.isSome && r[j]! < 0 then return false
    if hi.isSome && r[j]! > 0 then return false
  let ar := evalAx p r
  for i in [0:p.numConstraints] do
    let (lo, hi) := p.rowBounds[i]!
    if lo.isSome && ar[i]! < 0 then return false
    if hi.isSome && ar[i]! > 0 then return false
  return true

/-- Unbounded certificate: a feasible base point and an improving
    recession ray. -/
def checkUnbounded (p : Problem) (x ray : Array Rat) : Bool :=
  isPrimalFeasible p x
  && isRecessionRay p ray
  && dot p.c ray < 0

end LeanSoplex.Verify
