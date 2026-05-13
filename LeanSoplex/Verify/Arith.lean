/-
  Bespoke `Rat` / `Array` arithmetic + Bool→Prop bridges used by the
  soundness proofs in `LeanSoplex.Verify.Sound`.

  PLAN.md §"Lean shape" makes the verifier standalone — no Mathlib —
  so this file contains the small set of derived lemmas that core
  Lean 4 does not ship under the names mathlib provides, plus the
  one-direction bridges that turn each `Bool` check from
  `LeanSoplex.Verify.Bool` into a usable `Prop` fact.

  Scope of this module: Rat helpers, array size/index lemmas, sparse
  bilinear identities, and the Bool→Prop bridges consumed by the
  soundness layer.
-/

import LeanSoplex.Verify.Bool
import LeanSoplex.Verify.Prop

namespace LeanSoplex.Verify

open LeanSoplex

/-! ## Derived `Rat` arithmetic.

  Lean 4 core (4.29.1) already provides `mul_nonneg`,
  `mul_le_mul_of_nonneg_left/right`, `add_nonneg`,
  `add_le_add_left/right` (as iffs), `add_lt_add_left/right`,
  `le_of_lt`, `le_trans`, `le_iff_sub_nonneg`, `neg_le_neg(_iff)`,
  `mul_lt_mul_of_pos_left/right`, the cancellation lemmas, and
  division lemmas. The handful below close the small gaps. Kept
  `private` and namespaced to avoid polluting the public verifier
  surface. -/

namespace RatAux

/-- Combine `add_le_add_left` and `add_le_add_right`. -/
protected theorem add_le_add {a b c d : Rat} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h₁) (Rat.add_le_add_left.mpr h₂)

/-- `0 ≤ a − b ↔ b ≤ a`. Reorientation of `Rat.le_iff_sub_nonneg`. -/
protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a :=
  (Rat.le_iff_sub_nonneg b a).symm

/-- Monotonicity of subtraction. -/
protected theorem sub_le_sub {a b c d : Rat} (h₁ : a ≤ b) (h₂ : d ≤ c) :
    a - c ≤ b - d := by
  have : a + (-c) ≤ b + (-d) := RatAux.add_le_add h₁ (Rat.neg_le_neg h₂)
  simpa [Rat.sub_eq_add_neg] using this

end RatAux

/-! ## `arrayEq` bridge.

  `arrayEq` is the Bool-level equality check used by `isStationary`.
  This bridge extracts a per-index Prop equality from the Bool true
  hypothesis, which subsequent stationarity / Farkas reasoning
  consumes. -/

/-- If `arrayEq a b = true` then `a` and `b` have the same size and
    agree at every index. The "size" half is a separate clause so
    callers can use it to discharge subsequent bounds-checks without
    needing the per-index value. -/
theorem arrayEq_true_imp_size
    {a b : Array Rat} (h : arrayEq a b = true) : a.size = b.size := by
  unfold arrayEq at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem arrayEq_true_imp_eq
    {a b : Array Rat} (h : arrayEq a b = true)
    (i : Nat) (hi : i < a.size) :
    a[i] = b[i]'(by have := arrayEq_true_imp_size h; omega) := by
  have hSize := arrayEq_true_imp_size h
  unfold arrayEq at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, hAll⟩ := h
  rw [Array.all_eq_true] at hAll
  have hZipSize : (a.zip b).size = a.size := by
    simp [Array.size_zip, hSize]
  have hi' : i < (a.zip b).size := by simpa [hZipSize]
  have := hAll i hi'
  simp [Array.getElem_zip] at this
  exact this

/-! ## `problemShapeOk` bridge. -/

/-- Bundled Prop-level shape predicate. `problemShapeOk p = true ↔`
    this, but only the forward direction is needed for soundness
    (we extract shape facts from a Bool hypothesis we already have).
    `validate` callers can also extract these facts from successful
    validation, but the bridge is more useful for direct extraction. -/
structure ProblemShapeOk (p : Problem) : Prop where
  c_size : p.c.size = p.numVars
  colBounds_size : p.colBounds.size = p.numVars
  rowBounds_size : p.rowBounds.size = p.numConstraints
  sparse_in_range : ∀ k (hk : k < p.a.size),
    (p.a[k]).1 < p.numConstraints ∧ (p.a[k]).2.1 < p.numVars

theorem problemShapeOk_imp
    {p : Problem} (h : problemShapeOk p = true) :
    ProblemShapeOk p := by
  unfold problemShapeOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hC, hCol⟩, hRow⟩, hAll⟩ := h
  refine
    { c_size := of_decide_eq_true hC
      colBounds_size := of_decide_eq_true hCol
      rowBounds_size := of_decide_eq_true hRow
      sparse_in_range := ?_ }
  intro k hk
  rw [Array.all_eq_true] at hAll
  have := hAll k hk
  rw [Bool.and_eq_true] at this
  exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩

/-! ## Bridges for Bool checks.

  Each lemma is a single-direction `Bool = true → Prop fact`. The
  Prop targets live in `LeanSoplex.Verify.Prop`; the soundness proofs
  in `LeanSoplex.Verify.Sound` consume these bridges. -/

theorem boundCombinationPos_imp {m n : Nat} {p : Problem} {d : DualBundle m n}
    (h : boundCombinationPos p d = true) :
    0 < dualBoundCombination p d := by
  unfold boundCombinationPos at h
  exact of_decide_eq_true h

/-- `(!o.isNone || decide P) = true ↔ (o = none → P)`. The Bool
    pattern used in `dualNonnegAndZeroWhereAbsent` for the
    zero-where-absent clauses. -/
private theorem or_not_isNone_decide_eq_true {α} {o : Option α} {P : Prop}
    [Decidable P] (h : (!o.isNone || decide P) = true) :
    o = none → P := by
  intro hNone
  rw [Bool.or_eq_true] at h
  rcases h with hSome | hP
  · simp [hNone] at hSome
  · exact of_decide_eq_true hP

theorem dualNonnegAndZeroWhereAbsent_imp
    {m n : Nat} {p : Problem} {d : DualBundle m n}
    (h : dualNonnegAndZeroWhereAbsent p d = true) :
    DualNonnegZeroWhereAbsent p d := by
  unfold dualNonnegAndZeroWhereAbsent at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, hM⟩, hN⟩, hRow⟩, hCol⟩ := h
  rw [Array.all_eq_true] at hRow hCol
  refine
    { numConstraints_eq := of_decide_eq_true hM
      numVars_eq       := of_decide_eq_true hN
      row_nonneg := ?_
      col_nonneg := ?_
      row_zero_absent := ?_
      col_zero_absent := ?_ }
  · intro i hi
    have hRange : i < (Array.range p.numConstraints).size := by
      simpa [Array.size_range] using hi
    have hi' := hRow i hRange
    rw [Array.getElem_range] at hi'
    simp only [Bool.and_eq_true] at hi'
    exact ⟨of_decide_eq_true hi'.1.1.1, of_decide_eq_true hi'.1.1.2⟩
  · intro j hj
    have hRange : j < (Array.range p.numVars).size := by
      simpa [Array.size_range] using hj
    have hj' := hCol j hRange
    rw [Array.getElem_range] at hj'
    simp only [Bool.and_eq_true] at hj'
    exact ⟨of_decide_eq_true hj'.1.1.1, of_decide_eq_true hj'.1.1.2⟩
  · intro i hi
    have hRange : i < (Array.range p.numConstraints).size := by
      simpa [Array.size_range] using hi
    have hi' := hRow i hRange
    rw [Array.getElem_range] at hi'
    simp only [Bool.and_eq_true] at hi'
    exact ⟨or_not_isNone_decide_eq_true hi'.1.2,
           or_not_isNone_decide_eq_true hi'.2⟩
  · intro j hj
    have hRange : j < (Array.range p.numVars).size := by
      simpa [Array.size_range] using hj
    have hj' := hCol j hRange
    rw [Array.getElem_range] at hj'
    simp only [Bool.and_eq_true] at hj'
    exact ⟨or_not_isNone_decide_eq_true hj'.1.2,
           or_not_isNone_decide_eq_true hj'.2⟩

/-! ## Size lemmas for `evalAx` / `evalATy` / `arraySub`.

  These are the foundational size facts the soundness layer uses to
  discharge index-in-range obligations when bridging Bool↔Prop. -/

/-- `applyAx` preserves the output array's size. -/
theorem applyAx_size (x : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) :
    (LeanSoplex.Verify.applyAx x out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : r < out.size ∧ c < x.size
       then out.set r (out[r]! + v * x[c]!) h.1 else out).size = out.size
  by_cases h : r < out.size ∧ c < x.size
  · simp [h, Array.size_set]
  · simp [h]

/-- `applyATy` preserves the output array's size. -/
theorem applyATy_size (y : Array Rat) (out : Array Rat)
    (entry : Nat × Nat × Rat) :
    (LeanSoplex.Verify.applyATy y out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : c < out.size ∧ r < y.size
       then out.set c (out[c]! + v * y[r]!) h.1 else out).size = out.size
  by_cases h : c < out.size ∧ r < y.size
  · simp [h, Array.size_set]
  · simp [h]

theorem evalAx_size (p : Problem) (x : Array Rat) :
    (evalAx p x).size = p.numConstraints := by
  unfold evalAx
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = p.numConstraints)
    ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyAx_size]
    exact hAcc

theorem evalATy_size (p : Problem) (y : Array Rat) :
    (evalATy p y).size = p.numVars := by
  unfold evalATy
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = p.numVars)
    ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyATy_size]
    exact hAcc

theorem arraySub_size_of_eq (a b : Array Rat) (h : a.size = b.size) :
    (arraySub a b).size = a.size := by
  unfold arraySub
  rw [if_pos h, Array.size_zipWith, h, Nat.min_self]

/-- `arraySub a b` at index `i` is `a[i]! - b[i]!`, given sizes match
    and `i` is in range. -/
theorem arraySub_get!_of_eq
    (a b : Array Rat) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (arraySub a b)[i]! = a[i]! - b[i]! := by
  have hib : i < b.size := h ▸ hi
  have hZip : i < (Array.zipWith (fun x y => x - y) a b).size := by
    rw [Array.size_zipWith]
    exact Nat.lt_min.mpr ⟨hi, hib⟩
  unfold arraySub
  rw [if_pos h]
  rw [getElem!_pos (Array.zipWith (fun x y => x - y) a b) i hZip]
  rw [Array.getElem_zipWith]
  rw [← getElem!_pos a i hi, ← getElem!_pos b i hib]

/-! ## Vector-lifted analogues of `arraySub` / `dot` / `evalAx` / `evalATy`.

  The proof obligations that the Array versions need (size match,
  in-range index, output-size lemma) come for free when the inputs
  and outputs are `Vector Rat n`: sizes are part of the type. These
  bridges connect the two views so callers can use the type-safe
  Vector form without rewriting every soundness lemma. -/

/-- `(vSub a b).toArray` agrees with `arraySub` on the underlying
    arrays. -/
theorem vSub_toArray {n : Nat} (a b : Vector Rat n) :
    (vSub a b).toArray = arraySub a.toArray b.toArray := by
  unfold vSub arraySub
  rw [Vector.toArray_zipWith]
  rw [if_pos (by rw [a.size_toArray, b.size_toArray])]

/-- `vDot` agrees with `dot` on the underlying arrays — the Vector
    form has no size-mismatch fallback, but on equally-sized inputs
    they compute the same sum. -/
theorem vDot_eq_dot {n : Nat} (a b : Vector Rat n) :
    vDot a b = dot a.toArray b.toArray := by
  unfold vDot dot
  rw [if_pos (by rw [a.size_toArray, b.size_toArray])]
  rw [Vector.toArray_zipWith]

/-- `Aᵀy` as a `Vector Rat p.numVars`. Wraps `evalATy` together with
    its `_size` lemma so callers never re-derive the output size. -/
def vEvalATy (p : Problem) {k : Nat} (y : Vector Rat k) : Vector Rat p.numVars :=
  ⟨evalATy p y.toArray, evalATy_size p y.toArray⟩

/-- `Ax` as a `Vector Rat p.numConstraints`, dual to `vEvalATy`. -/
def vEvalAx (p : Problem) {k : Nat} (x : Vector Rat k) : Vector Rat p.numConstraints :=
  ⟨evalAx p x.toArray, evalAx_size p x.toArray⟩

@[simp] theorem vEvalAx_toArray (p : Problem) {k : Nat} (x : Vector Rat k) :
    (vEvalAx p x).toArray = evalAx p x.toArray := rfl

@[simp] theorem vEvalATy_toArray (p : Problem) {k : Nat} (y : Vector Rat k) :
    (vEvalATy p y).toArray = evalATy p y.toArray := rfl

/-! ## Sparse bilinear identity.

  Core Lean does not expose the Mathlib-style finite-sum API used for
  dot-product update lemmas, so we use small Nat-indexed prefix sums
  and connect them to the executable `Array.foldl` definitions. -/

private def dotPrefix (a b : Array Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => dotPrefix a b n + a[n]! * b[n]!

private def sparsePrefix (entries : Array (Nat × Nat × Rat))
    (y x : Array Rat) : Nat → Rat
  | 0 => 0
  | n + 1 =>
      let e := entries[n]!
      sparsePrefix entries y x n + e.2.2 * y[e.1]! * x[e.2.1]!

private def sparseBilinear (p : Problem) (y x : Array Rat) : Rat :=
  p.a.foldl (fun acc e => acc + e.2.2 * y[e.1]! * x[e.2.1]!) 0

private theorem dot_eq_dotPrefix
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b = dotPrefix a b a.size := by
  unfold dot
  rw [if_pos h]
  have hZipSize :
      (Array.zipWith (fun x y => x * y) a b).size = a.size := by
    rw [Array.size_zipWith, h, Nat.min_self]
  have hFold :
      (Array.zipWith (fun x y => x * y) a b).foldl (fun x y => x + y) 0 =
        dotPrefix a b (Array.zipWith (fun x y => x * y) a b).size := by
    refine Array.foldl_induction
      (as := Array.zipWith (fun x y => x * y) a b)
      (motive := fun i acc => acc = dotPrefix a b i) ?_ ?_
    · rfl
    · intro i acc hAcc
      rw [hAcc]
      have hiZip : i.val < (Array.zipWith (fun x y => x * y) a b).size := i.isLt
      have hia : i.val < a.size := by
        simpa [hZipSize] using hiZip
      have hib : i.val < b.size := by
        rw [← h]
        exact hia
      change dotPrefix a b i.val +
          (Array.zipWith (fun x y => x * y) a b)[i.val] =
        dotPrefix a b (i.val + 1)
      rw [show (Array.zipWith (fun x y => x * y) a b)[i.val] =
          a[i.val] * b[i.val] from Array.getElem_zipWith (hi := hiZip)]
      rw [← getElem!_pos a i.val hia, ← getElem!_pos b i.val hib]
      rfl
  rw [hFold, hZipSize]

private theorem dotPrefix_set_within
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) (n : Nat) (hn : n ≤ a.size) :
    dotPrefix y (a.set r v hr) n =
      dotPrefix y a n + if r < n then y[r]! * (v - a[r]!) else 0 := by
  induction n with
  | zero =>
      simp [dotPrefix, Rat.add_zero]
  | succ n ih =>
      by_cases hrn : r = n
      · subst r
        have hnLt : n < a.size := hr
        have hnSet : n < (a.set n v hr).size := by
          rw [Array.size_set]
          exact hr
        have hnY : n < y.size := by rw [hSize]; exact hnLt
        rw [dotPrefix, ih (by omega)]
        rw [getElem!_pos (a.set n v hr) n hnSet]
        rw [Array.getElem_set]
        rw [if_pos rfl]
        have hnn : ¬ n < n := by omega
        have hnns : n < n + 1 := by omega
        simp [hnn, hnns]
        rw [show dotPrefix y a (n + 1) = dotPrefix y a n + y[n]! * a[n]! by rfl]
        rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
        change dotPrefix y a n + 0 + y[n] * v =
          (dotPrefix y a n + y[n] * a[n]) + y[n] * (v - a[n])
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
          Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
      · by_cases hrLtN : r < n
        · have hnLt : n < a.size := by omega
          have hnSet : n < (a.set r v hr).size := by
            rw [Array.size_set]
            exact hnLt
          have hnY : n < y.size := by rw [hSize]; exact hnLt
          rw [dotPrefix, ih (by omega)]
          rw [getElem!_pos (a.set r v hr) n hnSet]
          rw [Array.getElem_set]
          simp [hrn, hrLtN, Nat.lt_succ_of_lt hrLtN]
          rw [dotPrefix]
          rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
          grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
        · have hrNotLtSucc : ¬ r < n + 1 := by omega
          have hnLt : n < a.size := by omega
          have hnSet : n < (a.set r v hr).size := by
            rw [Array.size_set]
            exact hnLt
          have hnY : n < y.size := by rw [hSize]; exact hnLt
          rw [dotPrefix, ih (by omega)]
          rw [getElem!_pos (a.set r v hr) n hnSet]
          rw [Array.getElem_set]
          simp [hrLtN, hrNotLtSucc]
          rw [dotPrefix]
          rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
          simp [hrn, Rat.add_zero]

private theorem dotPrefix_set
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) :
    dotPrefix y (a.set r v hr) a.size =
      dotPrefix y a a.size + y[r]! * (v - a[r]!) := by
  rw [dotPrefix_set_within y a r v hr hSize a.size (Nat.le_refl _)]
  simp [hr]

private theorem dot_set
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) :
    dot y (a.set r v hr) =
      dot y a + y[r]! * (v - a[r]!) := by
  have hSetSize : y.size = (a.set r v hr).size := by
    rw [Array.size_set]
    exact hSize
  rw [dot_eq_dotPrefix y (a.set r v hr) hSetSize]
  rw [dot_eq_dotPrefix y a hSize]
  rw [hSize]
  exact dotPrefix_set y a r v hr hSize

private theorem dotPrefix_comm_within
    (a b : Array Rat) :
    ∀ n, n ≤ a.size → n ≤ b.size → dotPrefix a b n = dotPrefix b a n
  | 0, _, _ => rfl
  | n + 1, hna, hnb => by
      have hna' : n ≤ a.size := by omega
      have hnb' : n ≤ b.size := by omega
      have hia : n < a.size := by omega
      have hib : n < b.size := by omega
      rw [dotPrefix, dotPrefix, dotPrefix_comm_within a b n hna' hnb']
      rw [getElem!_pos a n hia, getElem!_pos b n hib]
      grind [Rat.mul_comm]

private theorem dot_comm
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b = dot b a := by
  rw [dot_eq_dotPrefix a b h, dot_eq_dotPrefix b a h.symm]
  rw [show b.size = a.size from h.symm]
  exact dotPrefix_comm_within a b a.size (Nat.le_refl _) (by rw [← h]; exact Nat.le_refl _)

private theorem dot_set_left
    (a x : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : a.size = x.size) :
    dot (a.set r v hr) x =
      dot a x + x[r]! * (v - a[r]!) := by
  have hSetSize : (a.set r v hr).size = x.size := by
    rw [Array.size_set]
    exact hSize
  rw [dot_comm (a.set r v hr) x hSetSize]
  rw [dot_set x a r v hr hSize.symm]
  rw [dot_comm a x hSize]

private theorem dot_replicate_right_zero (y : Array Rat) (n : Nat)
    (h : y.size = n) :
    dot y (Array.replicate n 0) = 0 := by
  unfold dot
  rw [if_pos (by simp [h])]
  refine Array.foldl_induction
    (as := Array.zipWith (fun x y => x * y) y (Array.replicate n (0 : Rat)))
    (motive := fun _ acc => acc = 0) ?_ ?_
  · rfl
  · intro i acc hAcc
    rw [hAcc]
    have hiZip : i.val < (Array.zipWith (fun x y => x * y) y
        (Array.replicate n (0 : Rat))).size := i.isLt
    have hiRep : i.val < (Array.replicate n (0 : Rat)).size := by
      have hZipSize : (Array.zipWith (fun x y => x * y) y
          (Array.replicate n (0 : Rat))).size = n := by
        rw [Array.size_zipWith, h, Array.size_replicate, Nat.min_self]
      have : i.val < n := by
        exact Nat.lt_of_lt_of_le hiZip (Nat.le_of_eq hZipSize)
      simpa using this
    have hiY : i.val < y.size := by rw [h]; simpa using hiRep
    change 0 + (Array.zipWith (fun x y => x * y) y
        (Array.replicate n (0 : Rat)))[i.val] = 0
    rw [show (Array.zipWith (fun x y => x * y) y
        (Array.replicate n (0 : Rat)))[i.val] =
        y[i.val] * (Array.replicate n (0 : Rat))[i.val] from
        Array.getElem_zipWith (hi := hiZip)]
    rw [Array.getElem_replicate (h := hiRep)]
    rw [Rat.mul_zero, Rat.zero_add]

private theorem dot_replicate_left_zero (x : Array Rat) (n : Nat)
    (h : x.size = n) :
    dot (Array.replicate n 0) x = 0 := by
  rw [dot_comm (Array.replicate n (0 : Rat)) x (by simp [h])]
  exact dot_replicate_right_zero x n h

private theorem dotPrefix_eq_range_fold
    (a b : Array Rat) :
    ∀ n, n ≤ a.size → n ≤ b.size →
      dotPrefix a b n =
        (Array.range n).foldl (fun acc i => acc + a[i]! * b[i]!) 0
  | 0, _, _ => rfl
  | n + 1, hna, hnb => by
      have hna' : n ≤ a.size := by omega
      have hnb' : n ≤ b.size := by omega
      have hia : n < a.size := by omega
      have hib : n < b.size := by omega
      rw [dotPrefix, dotPrefix_eq_range_fold a b n hna' hnb']
      have hRange :
          Array.range (n + 1) = (Array.range n).push n := by
        exact Array.range_succ
      rw [hRange, Array.foldl_push]

theorem dot_eq_range_fold
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b =
      (Array.range a.size).foldl (fun acc i => acc + a[i]! * b[i]!) 0 := by
  rw [dot_eq_dotPrefix a b h]
  exact dotPrefix_eq_range_fold a b a.size (Nat.le_refl _) (by rw [h]; exact Nat.le_refl _)

/-! ## Pointwise affine rays.

  These helpers support the unboundedness proof: `addSmul x λ r` is
  the executable point `x + λ • r`, with linearity facts for dot
  products, objectives, and `evalAx`. -/

def Array.addSmul (x : Array Rat) (lam : Rat) (r : Array Rat) : Array Rat :=
  if x.size = r.size then Array.zipWith (fun xj rj => xj + lam * rj) x r else #[]

theorem Array.addSmul_size_of_eq
    (x r : Array Rat) (lam : Rat) (h : x.size = r.size) :
    (Array.addSmul x lam r).size = x.size := by
  unfold Array.addSmul
  rw [if_pos h, Array.size_zipWith, h, Nat.min_self]

theorem Array.addSmul_get!_of_eq
    (x r : Array Rat) (lam : Rat) (h : x.size = r.size)
    (i : Nat) (hi : i < x.size) :
    (Array.addSmul x lam r)[i]! = x[i]! + lam * r[i]! := by
  have hir : i < r.size := h ▸ hi
  have hZip : i < (Array.zipWith (fun xj rj => xj + lam * rj) x r).size := by
    rw [Array.size_zipWith]
    exact Nat.lt_min.mpr ⟨hi, hir⟩
  unfold Array.addSmul
  rw [if_pos h]
  rw [getElem!_pos (Array.zipWith (fun xj rj => xj + lam * rj) x r) i hZip]
  rw [Array.getElem_zipWith]
  rw [← getElem!_pos x i hi, ← getElem!_pos r i hir]

private theorem range_fold_congr
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i = g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 =
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  apply Rat.le_antisymm
  · induction n with
    | zero =>
        simp [Array.range]
    | succ n ih =>
        simp [Array.range_succ]
        exact RatAux.add_le_add
          (by simpa using ih (by intro i hi; exact h i (by omega)))
          (by rw [h n (by omega)]; exact Rat.le_refl)
  · induction n with
    | zero =>
        simp [Array.range]
    | succ n ih =>
        simp [Array.range_succ]
        exact RatAux.add_le_add
          (by simpa using ih (by intro i hi; rw [h i (by omega)]))
          (by rw [h n (by omega)]; exact Rat.le_refl)

private theorem range_fold_add
    (n : Nat) (f g : Nat → Rat) :
    (Array.range n).foldl (fun acc i => acc + (f i + g i)) 0 =
      (Array.range n).foldl (fun acc i => acc + f i) 0 +
        (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero =>
      simp [Array.range, Rat.zero_add]
  | succ n ih =>
      simp [Array.range_succ]
      have ih' :
          Array.foldl (fun acc i => acc + (f i + g i)) 0 (Array.range n) 0 n =
            Array.foldl (fun acc i => acc + f i) 0 (Array.range n) 0 n +
              Array.foldl (fun acc i => acc + g i) 0 (Array.range n) 0 n := by
        simpa using ih
      rw [ih']
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem range_fold_smul
    (n : Nat) (lam : Rat) (f : Nat → Rat) :
    (Array.range n).foldl (fun acc i => acc + lam * f i) 0 =
      lam * (Array.range n).foldl (fun acc i => acc + f i) 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      have ih' :
          Array.foldl (fun acc i => acc + lam * f i) 0 (Array.range n) 0 n =
            lam * Array.foldl (fun acc i => acc + f i) 0 (Array.range n) 0 n := by
        simpa using ih
      rw [ih']
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem dot_addSmul_right
    (c x r : Array Rat) (lam : Rat)
    (hcx : c.size = x.size) (hxr : x.size = r.size) :
    dot c (Array.addSmul x lam r) = dot c x + lam * dot c r := by
  have hySize : (Array.addSmul x lam r).size = x.size :=
    Array.addSmul_size_of_eq x r lam hxr
  rw [dot_eq_range_fold c (Array.addSmul x lam r) (by rw [hySize]; exact hcx)]
  rw [dot_eq_range_fold c x hcx]
  rw [dot_eq_range_fold c r (by rw [← hxr]; exact hcx)]
  rw [hcx]
  calc
    (Array.range x.size).foldl
        (fun acc i => acc + c[i]! * (Array.addSmul x lam r)[i]!) 0
        =
      (Array.range x.size).foldl
        (fun acc i => acc + (c[i]! * x[i]! + c[i]! * (lam * r[i]!))) 0 := by
          apply range_fold_congr
          intro i hi
          rw [Array.addSmul_get!_of_eq x r lam hxr i hi]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
    _ =
      (Array.range x.size).foldl (fun acc i => acc + c[i]! * x[i]!) 0 +
        (Array.range x.size).foldl (fun acc i => acc + c[i]! * (lam * r[i]!)) 0 := by
          exact range_fold_add x.size
            (fun i => c[i]! * x[i]!)
            (fun i => c[i]! * (lam * r[i]!))
    _ =
      (Array.range x.size).foldl (fun acc i => acc + c[i]! * x[i]!) 0 +
        lam * (Array.range x.size).foldl (fun acc i => acc + c[i]! * r[i]!) 0 := by
          have hScale :
              (Array.range x.size).foldl
                  (fun acc i => acc + c[i]! * (lam * r[i]!)) 0 =
                (Array.range x.size).foldl
                  (fun acc i => acc + lam * (c[i]! * r[i]!)) 0 := by
            apply range_fold_congr
            intro i hi
            grind [Rat.mul_assoc, Rat.mul_comm]
          rw [hScale]
          rw [range_fold_smul x.size lam (fun i => c[i]! * r[i]!)]

private def unitVector (n i : Nat) : Array Rat :=
  Array.ofFn (fun j : Fin n => if j.val = i then 1 else 0)

private theorem unitVector_size (n i : Nat) :
    (unitVector n i).size = n := by
  unfold unitVector
  simp

private theorem unitVector_get! (n i j : Nat) (hj : j < n) :
    (unitVector n i)[j]! = if j = i then 1 else 0 := by
  unfold unitVector
  rw [getElem!_pos _ j (by simpa using hj)]
  rw [Array.getElem_ofFn]

private theorem range_fold_unit_zero_before
    (n i : Nat) (a : Array Rat) (hn : n ≤ i) :
    (Array.range n).foldl
      (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!) 0 = 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      have hni : n ≠ i := by omega
      have ih' :
          Array.foldl (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!)
            0 (Array.range n) 0 n = 0 := by
        simpa using ih (by omega)
      rw [ih']
      simp [hni, Rat.zero_add]

private theorem range_fold_unit_get
    (n i : Nat) (a : Array Rat) (hi : i < n) :
    (Array.range n).foldl
      (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!) 0 = a[i]! := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      simp [Array.range_succ]
      by_cases hin : i = n
      · subst i
        have hzero :
            Array.foldl (fun acc j => acc + (if j = n then (1 : Rat) else 0) * a[j]!)
              0 (Array.range n) 0 n = 0 := by
          simpa using range_fold_unit_zero_before n n a (Nat.le_refl _)
        rw [hzero]
        simp [Rat.zero_add]
      · have hiPrev : i < n := by omega
        have ih' :
            Array.foldl (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!)
              0 (Array.range n) 0 n = a[i]! := by
          simpa using ih hiPrev
        rw [ih']
        have hni : n ≠ i := by omega
        simp [hni, Rat.add_zero]

private theorem dot_unitVector_left
    (a : Array Rat) (n i : Nat) (ha : a.size = n) (hi : i < n) :
    dot (unitVector n i) a = a[i]! := by
  rw [dot_eq_range_fold (unitVector n i) a (by rw [unitVector_size, ha])]
  rw [unitVector_size]
  apply Eq.trans ?_ (range_fold_unit_get n i a hi)
  apply range_fold_congr
  intro j hj
  rw [unitVector_get! n i j hj]

theorem primalObj_addSmul
    (p : Problem) (x r : Array Rat) (lam : Rat)
    (hcx : p.c.size = x.size) (hxr : x.size = r.size) :
    primalObj p (Array.addSmul x lam r) =
      primalObj p x + lam * dot p.c r := by
  unfold primalObj
  rw [dot_addSmul_right p.c x r lam hcx hxr]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem dot_replicate_left_zero'
    (x : Array Rat) (n : Nat) (h : x.size = n) :
    dot (Array.replicate n 0) x = 0 :=
  dot_replicate_left_zero x n h

theorem dot_replicate_right_zero'
    (y : Array Rat) (n : Nat) (h : y.size = n) :
    dot y (Array.replicate n 0) = 0 :=
  dot_replicate_right_zero y n h

private theorem sparseBilinear_eq_sparsePrefix
    (p : Problem) (y x : Array Rat) :
    sparseBilinear p y x = sparsePrefix p.a y x p.a.size := by
  unfold sparseBilinear
  refine Array.foldl_induction
    (as := p.a)
    (motive := fun i acc => acc = sparsePrefix p.a y x i) ?_ ?_
  · rfl
  · intro i acc hAcc
    rw [hAcc]
    rw [sparsePrefix]
    rw [getElem!_pos p.a i.val i.isLt]
    rfl

private theorem dot_evalAx_eq_sparseBilinear
    (p : Problem) (y x : Array Rat)
    (hShape : ProblemShapeOk p)
    (hY : y.size = p.numConstraints)
    (hX : x.size = p.numVars) :
    dot y (evalAx p x) = sparseBilinear p y x := by
  unfold evalAx
  rw [sparseBilinear_eq_sparsePrefix]
  have hFold := Array.foldl_induction
    (as := p.a)
    (init := Array.replicate p.numConstraints 0)
    (f := applyAx x)
    (motive := fun i out =>
      out.size = p.numConstraints ∧ dot y out = sparsePrefix p.a y x i)
    (by
      constructor
      · simp
      · rw [dot_replicate_right_zero y p.numConstraints hY]
        rfl)
    (by
      intro i out hAcc
      obtain ⟨hOutSize, hDot⟩ := hAcc
      cases hEntryEq : p.a[i.val] with
      | mk r cv =>
      cases cv with
    | mk c v =>
    have hEntry := hShape.sparse_in_range i.val i.isLt
    simp [hEntryEq] at hEntry
    have hrOut : r < out.size := by rw [hOutSize]; exact hEntry.1
    have hcX : c < x.size := by rw [hX]; exact hEntry.2
    constructor
    · rw [applyAx_size, hOutSize]
    · unfold applyAx
      simp [hrOut, hcX]
      rw [dot_set y out r (out[r] + v * x[c]) hrOut (by rw [hOutSize]; exact hY)]
      rw [hDot]
      rw [sparsePrefix, getElem!_pos p.a i.val i.isLt]
      rw [hEntryEq]
      rw [← getElem!_pos x c hcX]
      rw [← getElem!_pos out r hrOut]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm])
  exact hFold.2

private theorem dot_evalATy_eq_sparseBilinear
    (p : Problem) (y x : Array Rat)
    (hShape : ProblemShapeOk p)
    (hY : y.size = p.numConstraints)
    (hX : x.size = p.numVars) :
    dot (evalATy p y) x = sparseBilinear p y x := by
  unfold evalATy
  rw [sparseBilinear_eq_sparsePrefix]
  have hFold := Array.foldl_induction
    (as := p.a)
    (init := Array.replicate p.numVars 0)
    (f := applyATy y)
    (motive := fun i out =>
      out.size = p.numVars ∧ dot out x = sparsePrefix p.a y x i)
    (by
      constructor
      · simp
      · rw [dot_replicate_left_zero x p.numVars hX]
        rfl)
    (by
      intro i out hAcc
      obtain ⟨hOutSize, hDot⟩ := hAcc
      cases hEntryEq : p.a[i.val] with
      | mk r cv =>
      cases cv with
    | mk c v =>
    have hEntry := hShape.sparse_in_range i.val i.isLt
    simp [hEntryEq] at hEntry
    have hcOut : c < out.size := by rw [hOutSize]; exact hEntry.2
    have hrY : r < y.size := by rw [hY]; exact hEntry.1
    constructor
    · rw [applyATy_size, hOutSize]
    · unfold applyATy
      simp [hcOut, hrY]
      rw [dot_set_left out x c (out[c] + v * y[r]) hcOut (by rw [hOutSize, ← hX])]
      rw [hDot]
      rw [sparsePrefix, getElem!_pos p.a i.val i.isLt]
      rw [hEntryEq]
      rw [← getElem!_pos out c hcOut]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm])
  exact hFold.2

theorem dot_y_evalAx_eq_dot_evalATy_x
    (p : Problem) (y x : Array Rat)
    (hShape : ProblemShapeOk p)
    (hY : y.size = p.numConstraints)
    (hX : x.size = p.numVars) :
    dot y (evalAx p x) = dot (evalATy p y) x := by
  rw [dot_evalAx_eq_sparseBilinear p y x hShape hY hX,
      dot_evalATy_eq_sparseBilinear p y x hShape hY hX]

theorem evalAx_addSmul_get!
    (p : Problem) (x r : Array Rat) (lam : Rat)
    (hShape : ProblemShapeOk p)
    (hx : x.size = p.numVars) (hr : r.size = p.numVars)
    (i : Nat) (hi : i < p.numConstraints) :
    (evalAx p (Array.addSmul x lam r))[i]! =
      (evalAx p x)[i]! + lam * (evalAx p r)[i]! := by
  let e := unitVector p.numConstraints i
  have heSize : e.size = p.numConstraints := unitVector_size p.numConstraints i
  have hySize : (Array.addSmul x lam r).size = p.numVars := by
    have h := Array.addSmul_size_of_eq x r lam (by rw [hx, hr])
    rw [hx] at h
    exact h
  have hLeft :
      dot e (evalAx p (Array.addSmul x lam r)) =
        (evalAx p (Array.addSmul x lam r))[i]! := by
    exact dot_unitVector_left (evalAx p (Array.addSmul x lam r))
      p.numConstraints i (evalAx_size ..) hi
  have hX :
      dot e (evalAx p x) = (evalAx p x)[i]! := by
    exact dot_unitVector_left (evalAx p x) p.numConstraints i (evalAx_size ..) hi
  have hR :
      dot e (evalAx p r) = (evalAx p r)[i]! := by
    exact dot_unitVector_left (evalAx p r) p.numConstraints i (evalAx_size ..) hi
  rw [← hLeft, dot_y_evalAx_eq_dot_evalATy_x p e (Array.addSmul x lam r)
        hShape heSize hySize]
  rw [dot_addSmul_right (evalATy p e) x r lam (by rw [evalATy_size, hx]) (by rw [hx, hr])]
  rw [← dot_y_evalAx_eq_dot_evalATy_x p e x hShape heSize hx]
  rw [← dot_y_evalAx_eq_dot_evalATy_x p e r hShape heSize hr]
  rw [hX, hR]

/-! ## `isStationary` bridge.

  Translates the Bool-level array equality into the componentwise
  `StationarityAgainst p d p.c` Prop. The proof unpacks `arrayEq` to
  get a per-index equality, then uses `getElem_zipWith` and
  `arraySub_get!_of_eq` to rewrite both sides into `[i]!` form. -/
theorem isStationary_imp
    {m n : Nat} {p : Problem} {d : DualBundle m n}
    (hShape : ProblemShapeOk p)
    (hDual : DualNonnegZeroWhereAbsent p d)
    (h : isStationary p d = true) :
    StationarityAgainst p d p.c := by
  unfold isStationary at h
  -- Translate Vector ops back to their Array forms so the existing
  -- size lemmas apply unchanged.
  simp only [vSub_toArray] at h
  -- Sizes of the inner foldl / zipWith.
  have hRowEq : d.rowLower.toArray.size = d.rowUpper.toArray.size :=
    hDual.rowLower_size.trans hDual.rowUpper_size.symm
  have hColEq : d.colLower.toArray.size = d.colUpper.toArray.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hRowSub : (arraySub d.rowLower.toArray d.rowUpper.toArray).size = p.numConstraints := by
    rw [arraySub_size_of_eq _ _ hRowEq]; exact hDual.rowLower_size
  have hAty : (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size = p.numVars :=
    evalATy_size ..
  have hZdiff : (arraySub d.colLower.toArray d.colUpper.toArray).size = p.numVars := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  have hZipSize : (Array.zipWith (fun x y => x + y)
      (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))
      (arraySub d.colLower.toArray d.colUpper.toArray)).size = p.numVars := by
    rw [Array.size_zipWith, hAty, hZdiff, Nat.min_self]
  intro j hj
  have hjZip : j < (Array.zipWith (fun x y => x + y)
      (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))
      (arraySub d.colLower.toArray d.colUpper.toArray)).size := by rw [hZipSize]; exact hj
  have hEqj := arrayEq_true_imp_eq h j hjZip
  rw [Array.getElem_zipWith] at hEqj
  -- Convert getElem to [_]! at each position.
  have hjAty : j < (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size := by
    rw [hAty]; exact hj
  have hjZdiff : j < (arraySub d.colLower.toArray d.colUpper.toArray).size := by
    rw [hZdiff]; exact hj
  have hjC : j < p.c.size := by rw [hShape.c_size]; exact hj
  rw [← getElem!_pos _ j hjAty, ← getElem!_pos _ j hjZdiff,
      ← getElem!_pos _ j hjC] at hEqj
  -- Substitute arraySub at index j.
  rw [arraySub_get!_of_eq _ _ hColEq j (by rw [hDual.colLower_size]; exact hj)]
    at hEqj
  exact hEqj

/-- `(!o.isSome || decide P) = true ↔ (o = some _ → P)`. The Bool
    pattern used in `isRecessionRay` for the per-bound sign clauses. -/
private theorem or_not_isSome_decide_eq_true {α} {o : Option α} {P : Prop}
    [Decidable P] (h : (!o.isSome || decide P) = true) :
    o.isSome = true → P := by
  intro hSome
  rw [Bool.or_eq_true] at h
  rcases h with hNotSome | hP
  · simp [hSome] at hNotSome
  · exact of_decide_eq_true hP

/-- The `geLB` Bool check unpacked as a Prop: if `geLB x lo = true`
    then `lo = some l → l ≤ x`. -/
private theorem geLB_imp {x : Rat} {lo : Option Rat} (h : geLB x lo = true) :
    ∀ l, lo = some l → l ≤ x := by
  intro l hSome
  unfold geLB at h
  rw [hSome] at h
  exact of_decide_eq_true h

/-- The `leUB` Bool check unpacked as a Prop. -/
private theorem leUB_imp {x : Rat} {hi : Option Rat} (h : leUB x hi = true) :
    ∀ h', hi = some h' → x ≤ h' := by
  intro h' hSome
  unfold leUB at h
  rw [hSome] at h
  exact of_decide_eq_true h

theorem isPrimalFeasible_imp
    {p : Problem} {x : Array Rat}
    (h : isPrimalFeasible p x = true) :
    ProblemShapeOk p ∧ IsFeasible p x := by
  unfold isPrimalFeasible at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hShape, hxSize⟩, hCol⟩, hRow⟩ := h
  have hShape' := problemShapeOk_imp hShape
  have hxSize' : x.size = p.numVars := of_decide_eq_true hxSize
  rw [Array.all_eq_true] at hCol hRow
  refine ⟨hShape', ?_, ?_⟩
  · -- ColBoundsSatisfied
    refine ⟨hxSize', ?_⟩
    intro j
    have hRange : j.val < (Array.range p.numVars).size := by
      simp [Array.size_range, j.isLt]
    have hj' := hCol j.val hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hj'
    exact ⟨geLB_imp hj'.1, leUB_imp hj'.2⟩
  · -- RowBoundsSatisfied
    intro i
    have hRange : i.val < (Array.range p.numConstraints).size := by
      simp [Array.size_range, i.isLt]
    have hi' := hRow i.val hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hi'
    exact ⟨geLB_imp hi'.1, leUB_imp hi'.2⟩

theorem isRecessionRay_imp
    {p : Problem} {r : Array Rat}
    (h : isRecessionRay p r = true) :
    IsRecessionRay p r := by
  unfold isRecessionRay at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hSize⟩, hCol⟩, hRow⟩ := h
  rw [Array.all_eq_true] at hCol hRow
  refine
    { size := of_decide_eq_true hSize
      col_lo_nonneg := ?_
      col_hi_nonpos := ?_
      row_lo_nonneg := ?_
      row_hi_nonpos := ?_ }
  · intro j hj hLo
    have hRange : j < (Array.range p.numVars).size := by
      simpa [Array.size_range] using hj
    have hj' := hCol j hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hj'
    exact or_not_isSome_decide_eq_true hj'.1 hLo
  · intro j hj hHi
    have hRange : j < (Array.range p.numVars).size := by
      simpa [Array.size_range] using hj
    have hj' := hCol j hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hj'
    exact or_not_isSome_decide_eq_true hj'.2 hHi
  · intro i hi hLo
    have hRange : i < (Array.range p.numConstraints).size := by
      simpa [Array.size_range] using hi
    have hi' := hRow i hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hi'
    exact or_not_isSome_decide_eq_true hi'.1 hLo
  · intro i hi hHi
    have hRange : i < (Array.range p.numConstraints).size := by
      simpa [Array.size_range] using hi
    have hi' := hRow i hRange
    rw [Array.getElem_range, Bool.and_eq_true] at hi'
    exact or_not_isSome_decide_eq_true hi'.2 hHi

/-- `isFarkasFeasible p d = true` implies the homogeneous componentwise
    stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` plus the
    `DualNonnegZeroWhereAbsent` structure. Combined here so the
    soundness layer can consume `IsFarkasDualFeasible p d` in one
    step. -/
theorem isFarkasFeasible_imp
    {m n : Nat} {p : Problem} {d : DualBundle m n}
    (h : isFarkasFeasible p d = true) :
    IsFarkasDualFeasible p d := by
  unfold isFarkasFeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hNonneg, hZero⟩ := h
  simp only [vSub_toArray] at hZero
  have hDual := dualNonnegAndZeroWhereAbsent_imp hNonneg
  -- Sizes.
  have hRowEq : d.rowLower.toArray.size = d.rowUpper.toArray.size :=
    hDual.rowLower_size.trans hDual.rowUpper_size.symm
  have hColEq : d.colLower.toArray.size = d.colUpper.toArray.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hAty : (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size = p.numVars :=
    evalATy_size ..
  have hZdiff : (arraySub d.colLower.toArray d.colUpper.toArray).size = p.numVars := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  have hZipSize : (Array.zipWith (fun x y => x + y)
      (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))
      (arraySub d.colLower.toArray d.colUpper.toArray)).size = p.numVars := by
    rw [Array.size_zipWith, hAty, hZdiff, Nat.min_self]
  rw [Array.all_eq_true] at hZero
  refine
    { nonneg_zero_absent := hDual
      stationarity_zero := ?_ }
  intro j hj
  have hjZip : j < (Array.zipWith (fun x y => x + y)
      (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))
      (arraySub d.colLower.toArray d.colUpper.toArray)).size := by rw [hZipSize]; exact hj
  have hjZ := hZero j hjZip
  rw [Array.getElem_zipWith] at hjZ
  -- hjZ : decide (aty[j] + zdiff[j] = 0) = true (via `· == 0` lifted to decide)
  simp only [beq_iff_eq] at hjZ
  -- Convert getElems to [j]! form.
  have hjAty : j < (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size := by
    rw [hAty]; exact hj
  have hjZdiff : j < (arraySub d.colLower.toArray d.colUpper.toArray).size := by
    rw [hZdiff]; exact hj
  rw [← getElem!_pos _ j hjAty, ← getElem!_pos _ j hjZdiff] at hjZ
  rw [arraySub_get!_of_eq _ _ hColEq j (by rw [hDual.colLower_size]; exact hj)]
    at hjZ
  exact hjZ

end LeanSoplex.Verify
