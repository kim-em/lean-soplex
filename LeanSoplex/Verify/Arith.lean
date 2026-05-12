/-
  Bespoke `Rat` / `Array` arithmetic + Bool→Prop bridges used by the
  soundness proofs in `LeanSoplex.Verify.Sound`.

  PLAN.md §"Lean shape" makes the verifier standalone — no Mathlib —
  so this file contains the small set of derived lemmas that core
  Lean 4 does not ship under the names mathlib provides, plus the
  one-direction bridges that turn each `Bool` check from
  `LeanSoplex.Verify.Bool` into a usable `Prop` fact.

  Scope of this module today: Rat helpers, the `arrayEq` bridge,
  and the `problemShapeOk` bridge. The sparse-bilinear identity
  `dot y (evalAx p x) = dot (evalATy p y) x` and the rest of the
  per-check bridges live alongside `weak_duality` (PR-B); they are
  not used until the math layer needs them.
-/

import LeanSoplex.Verify.Bool

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

end LeanSoplex.Verify
