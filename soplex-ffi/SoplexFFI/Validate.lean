/-
  Pure-Lean validators for `Problem` and `Options`.

  `validate` normalizes and rejects every `Problem` value before it
  reaches the FFI or the certificate checker. It guarantees:

  * Every array field has the declared length.
  * Every sparse entry's `(row, col)` is in range.
  * Every bound pair has `lo ≤ hi`.
  * Sparse entries are sorted by `(row, col)`.
  * Duplicate `(row, col)` entries are summed.
  * Zero-valued sparse entries are dropped.

  This is the pure Lean boundary before data reaches either C++ or
  the verifier.
-/

import SoplexFFI.Types

namespace Soplex

/-! ## `validateOptions`. -/

/-- Reject obviously-invalid `Options` before they reach C++. -/
def validateOptions (o : Options) : Except OptionError Options := do
  -- NaN time-limit: distinct from a negative value so the error
  -- message can be useful.
  match o.timeLimit with
  | none     => pure ()
  | some t   =>
    if t.isNaN then
      throw .nanTimeLimit
    if t < 0.0 then
      throw (.negativeTimeLimit t)
  match o.iterLimit with
  | none   => pure ()
  | some n =>
    if n = 0 then
      throw .zeroIterLimit
    if n > ffiMaxInt then
      throw (.iterLimitTooLarge ffiMaxInt n)
  pure o

/-! ## `validate`. -/

/-- Compare `(row, col)` pairs lexicographically. -/
@[inline] private def entryLt (x y : Nat × Nat × Rat) : Bool :=
  let (r₁, c₁, _) := x
  let (r₂, c₂, _) := y
  r₁ < r₂ || (r₁ = r₂ && c₁ < c₂)

/-- Sum consecutive equal-key entries in a sorted sparse list, drop
    zero results, and return the normalised array. Assumes input is
    already sorted by `entryLt`. -/
private def collapseSorted (a : Array (Nat × Nat × Rat)) :
    Array (Nat × Nat × Rat) := Id.run do
  if a.isEmpty then return #[]
  let mut out : Array (Nat × Nat × Rat) := Array.mkEmpty a.size
  let mut curR : Nat := (a[0]!).1
  let mut curC : Nat := ((a[0]!).2).1
  let mut curV : Rat := ((a[0]!).2).2
  for i in [1:a.size] do
    let (r, c, v) := a[i]!
    if r = curR && c = curC then
      curV := curV + v
    else
      if curV ≠ 0 then
        out := out.push (curR, curC, curV)
      curR := r
      curC := c
      curV := v
  if curV ≠ 0 then
    out := out.push (curR, curC, curV)
  return out

/-- Normalise the sparse matrix: sort, sum duplicates, drop zeros. -/
private def normaliseSparse (a : Array (Nat × Nat × Rat)) :
    Array (Nat × Nat × Rat) :=
  collapseSorted (a.qsort entryLt)

/-- Validate and normalise a `Problem`.

    On success the returned `Problem` is structurally identical to the
    input *except* that `a` has been sorted, deduplicated, and pruned of
    zero entries. Field-level checks live here so the FFI and the
    checker can both assume well-formed inputs without re-validating. -/
def validate {numConstraints numVars : Nat} (p : Problem numConstraints numVars) :
    Except ProblemError (Problem numConstraints numVars) := do
  -- Length checks for `c`, `colBounds`, `rowBounds` are no longer
  -- needed: `Problem`'s `Vector` fields make wrong-length values
  -- unconstructible. `ProblemError.wrongLength` is retained in the
  -- error type for source compatibility but never thrown.
  -- Bound inversions for columns.
  for i in [0:p.colBounds.toArray.size] do
    match p.colBounds.toArray[i]! with
    | (some lo, some hi) =>
      if lo > hi then throw (.boundInverted .col i lo hi)
    | _ => pure ()
  -- Bound inversions for rows.
  for i in [0:p.rowBounds.toArray.size] do
    match p.rowBounds.toArray[i]! with
    | (some lo, some hi) =>
      if lo > hi then throw (.boundInverted .row i lo hi)
    | _ => pure ()
  -- Sparse-entry range checks.
  for k in [0:p.a.size] do
    let (r, c, _) := p.a[k]!
    if r ≥ numConstraints then
      throw (.indexOutOfRange .row r numConstraints)
    if c ≥ numVars then
      throw (.indexOutOfRange .col c numVars)
  let a' := normaliseSparse p.a
  pure { p with a := a' }

end Soplex
