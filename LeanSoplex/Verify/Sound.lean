/-
  Soundness theorems bridging the `Bool` checkers in
  `LeanSoplex.Verify.Bool` to the `Prop` predicates in
  `LeanSoplex.Verify.Prop`.

  The central technical lemma is `bound_combination_le_dot_q`: for any
  primal-feasible `x`, any dual nonneg/zero-where-absent `d`, and any
  `q` satisfying `Aᵀ(yL − yU) + (zL − zU) = q`, the dual bound
  combination lower-bounds `dot q x`. Specialised:

  * `weak_duality` at `q := p.c.toArray` discharges `checkOptimal_sound`.
  * `q := Array.replicate n 0` discharges `checkInfeasible_sound`.

  `checkUnbounded_sound` does not use the bound-combination lemma; it
  builds `y := x + λ · ray` and uses `IsRecessionRay`'s sign
  discipline plus `evalAx_addSmul` / `primalObj_addSmul` linearity.

  These proofs are the Prop-level soundness layer for accepted
  certificates.
-/

import LeanSoplex.Verify.Arith

namespace LeanSoplex.Verify

open LeanSoplex

private theorem problemShapeOk_of_prop {m n : Nat} {p : Problem m n}
    (h : ProblemShapeOk p) : problemShapeOk p = true := by
  unfold problemShapeOk
  rw [Array.all_eq_true]
  intro k hk
  have hrange := h.sparse_in_range k hk
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true hrange.1, decide_eq_true hrange.2⟩

private theorem dualNonnegAndZeroWhereAbsent_imp_shape
    {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : dualNonnegAndZeroWhereAbsent p d = true) :
    ProblemShapeOk p := by
  unfold dualNonnegAndZeroWhereAbsent at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact problemShapeOk_imp h.1.1

private theorem isDualFeasible_imp
    {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : isDualFeasible p d = true) :
    ProblemShapeOk p ∧ IsDualFeasible p d := by
  unfold isDualFeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hNonneg, hStatBool⟩ := h
  have hShape := dualNonnegAndZeroWhereAbsent_imp_shape hNonneg
  have hDual := dualNonnegAndZeroWhereAbsent_imp hNonneg
  refine ⟨hShape, ?_⟩
  exact { nonneg_zero_absent := hDual
          stationarity := isStationary_imp hShape hDual hStatBool }

private theorem range_fold_mono
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i ≤ g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 ≤
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      exact RatAux.add_le_add
        (by simpa using ih (by intro i hi; exact h i (by omega)))
        (h n (by omega))

private theorem range_fold_congr
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i = g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 =
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  apply Rat.le_antisymm
  · exact range_fold_mono n f g (by
      intro i hi
      rw [h i hi]
      exact Rat.le_refl)
  · exact range_fold_mono n g f (by
      intro i hi
      rw [h i hi]
      exact Rat.le_refl)

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

private theorem range_fold_mono_sub
    (n : Nat) (f g h : Nat → Rat)
    (hle : ∀ i, i < n → f i - g i ≤ h i) :
    (Array.range n).foldl (fun acc i => acc + f i - g i) 0 ≤
      (Array.range n).foldl (fun acc i => acc + h i) 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      have hprev :
          Array.foldl (fun acc i => acc + f i - g i) 0 (Array.range n) 0 n ≤
            Array.foldl (fun acc i => acc + h i) 0 (Array.range n) 0 n := by
        simpa using ih (by intro i hi; exact hle i (by omega))
      have hadd := RatAux.add_le_add hprev (hle n (by omega))
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem lower_contrib_le {lo : Option Rat} {mult value : Rat}
    (hNonneg : 0 ≤ mult)
    (hBound : ∀ l, lo = some l → l ≤ value)
    (hZero : lo = none → mult = 0) :
    (lo.elim 0 (mult * ·)) ≤ mult * value := by
  cases lo with
  | none =>
      simp [hZero rfl]
  | some l =>
      exact Rat.mul_le_mul_of_nonneg_left (hBound l rfl) hNonneg

private theorem neg_upper_contrib_le {hi : Option Rat} {mult value : Rat}
    (hNonneg : 0 ≤ mult)
    (hBound : ∀ u, hi = some u → value ≤ u)
    (hZero : hi = none → mult = 0) :
    -(hi.elim 0 (mult * ·)) ≤ -(mult * value) := by
  cases hi with
  | none =>
      simp [hZero rfl]
  | some u =>
      exact Rat.neg_le_neg (Rat.mul_le_mul_of_nonneg_left (hBound u rfl) hNonneg)

private theorem bound_term_le
    {lo hi : Option Rat} {loMult hiMult value : Rat}
    (hLoNonneg : 0 ≤ loMult) (hHiNonneg : 0 ≤ hiMult)
    (hLoBound : ∀ l, lo = some l → l ≤ value)
    (hHiBound : ∀ u, hi = some u → value ≤ u)
    (hLoZero : lo = none → loMult = 0)
    (hHiZero : hi = none → hiMult = 0) :
    lo.elim 0 (loMult * ·) - hi.elim 0 (hiMult * ·) ≤
      (loMult - hiMult) * value := by
  have hLo := lower_contrib_le (lo := lo) hLoNonneg hLoBound hLoZero
  have hHi := neg_upper_contrib_le (hi := hi) hHiNonneg hHiBound hHiZero
  have h := RatAux.add_le_add hLo hHi
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]

private theorem dot_of_stationarity
    {m n : Nat} {p : Problem m n} {d : DualBundle m n} {x q : Array Rat}
    (hXSize : x.size = n)
    (hDual : DualNonnegZeroWhereAbsent p d)
    (hStat : StationarityAgainst p d q)
    (hQ : q.size = n) :
    dot q x =
      dot (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)) x +
        dot (arraySub d.colLower.toArray d.colUpper.toArray) x := by
  have hColEq : d.colLower.toArray.size = d.colUpper.toArray.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hAty : (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size = n :=
    evalATy_size ..
  have hZdiff : (arraySub d.colLower.toArray d.colUpper.toArray).size = n := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  rw [dot_eq_range_fold q x (by rw [hQ, hXSize])]
  rw [dot_eq_range_fold (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)) x
    (by rw [hAty, hXSize])]
  rw [dot_eq_range_fold (arraySub d.colLower.toArray d.colUpper.toArray) x
    (by rw [hZdiff, hXSize])]
  rw [hQ, hAty, hZdiff]
  rw [← range_fold_add n
    (fun j => (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))[j]! * x[j]!)
    (fun j => (arraySub d.colLower.toArray d.colUpper.toArray)[j]! * x[j]!)]
  apply range_fold_congr
  intro j hj
  have hjQ : j < q.size := by rw [hQ]; exact hj
  have hjA : j < (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)).size := by
    rw [hAty]; exact hj
  have hjZ : j < (arraySub d.colLower.toArray d.colUpper.toArray).size := by
    rw [hZdiff]; exact hj
  have hStatj := hStat j hj
  have hSub := arraySub_get!_of_eq d.colLower.toArray d.colUpper.toArray hColEq j
    (by rw [hDual.colLower_size]; exact hj)
  rw [hSub]
  rw [← hStatj]
  grind [Rat.mul_add]

private theorem bound_combination_le_dot_q
    {m n : Nat} {p : Problem m n} {d : DualBundle m n} {x q : Array Rat}
    (hShape : ProblemShapeOk p)
    (hX : IsFeasible p x)
    (hDual : DualNonnegZeroWhereAbsent p d)
    (hStat : StationarityAgainst p d q)
    (hQ : q.size = n) :
    dualBoundCombination p d ≤ dot q x := by
  have hXSize : x.size = n := hX.1.1
  have hAxSize : (evalAx p x).size = m := evalAx_size ..
  have hRowEq : d.rowLower.toArray.size = d.rowUpper.toArray.size :=
    hDual.rowLower_size.trans hDual.rowUpper_size.symm
  have hColEq : d.colLower.toArray.size = d.colUpper.toArray.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hRowSub : (arraySub d.rowLower.toArray d.rowUpper.toArray).size = m := by
    rw [arraySub_size_of_eq _ _ hRowEq]; exact hDual.rowLower_size
  have hColSub : (arraySub d.colLower.toArray d.colUpper.toArray).size = n := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  have hRowLe :
      (Array.range m).foldl (fun (acc : Rat) i =>
        let (lo, hi) := p.rowBounds[i]!
        acc + lo.elim 0 (d.rowLower[i]! * ·) -
          hi.elim 0 (d.rowUpper[i]! * ·)) 0 ≤
        dot (arraySub d.rowLower.toArray d.rowUpper.toArray) (evalAx p x) := by
    rw [dot_eq_range_fold (arraySub d.rowLower.toArray d.rowUpper.toArray) (evalAx p x)
      (by rw [hRowSub, hAxSize])]
    rw [hRowSub]
    exact range_fold_mono_sub m
      (fun i => (p.rowBounds[i]!).1.elim 0 (d.rowLower[i]! * ·))
      (fun i => (p.rowBounds[i]!).2.elim 0 (d.rowUpper[i]! * ·))
      (fun i => (arraySub d.rowLower.toArray d.rowUpper.toArray)[i]! * (evalAx p x)[i]!)
      (by
        intro i hi
        have hNon := hDual.row_nonneg i hi
        have hZero := hDual.row_zero_absent i hi
        have hBounds := hX.2 ⟨i, hi⟩
        have hSub := arraySub_get!_of_eq d.rowLower.toArray d.rowUpper.toArray hRowEq i
          (by rw [hDual.rowLower_size]; exact hi)
        calc
          (match p.rowBounds[i]! with
            | (lo, hi) =>
              (lo.elim 0 fun x => d.rowLower[i]! * x) -
                hi.elim 0 fun x => d.rowUpper[i]! * x)
              ≤ (d.rowLower[i]! - d.rowUpper[i]!) * (evalAx p x)[i]! := by
                exact bound_term_le hNon.1 hNon.2 hBounds.1 hBounds.2 hZero.1 hZero.2
          _ = (arraySub d.rowLower.toArray d.rowUpper.toArray)[i]! * (evalAx p x)[i]! := by
                rw [hSub]; simp)
  have hColLe :
      (Array.range n).foldl (fun (acc : Rat) j =>
        let (lo, hi) := p.colBounds[j]!
        acc + lo.elim 0 (d.colLower[j]! * ·) -
          hi.elim 0 (d.colUpper[j]! * ·)) 0 ≤
        dot (arraySub d.colLower.toArray d.colUpper.toArray) x := by
    rw [dot_eq_range_fold (arraySub d.colLower.toArray d.colUpper.toArray) x
      (by rw [hColSub, hXSize])]
    rw [hColSub]
    exact range_fold_mono_sub n
      (fun j => (p.colBounds[j]!).1.elim 0 (d.colLower[j]! * ·))
      (fun j => (p.colBounds[j]!).2.elim 0 (d.colUpper[j]! * ·))
      (fun j => (arraySub d.colLower.toArray d.colUpper.toArray)[j]! * x[j]!)
      (by
        intro j hj
        have hNon := hDual.col_nonneg j hj
        have hZero := hDual.col_zero_absent j hj
        have hBounds := hX.1.2 ⟨j, hj⟩
        have hSub := arraySub_get!_of_eq d.colLower.toArray d.colUpper.toArray hColEq j
          (by rw [hDual.colLower_size]; exact hj)
        calc
          (match p.colBounds[j]! with
            | (lo, hi) =>
              (lo.elim 0 fun x => d.colLower[j]! * x) -
                hi.elim 0 fun x => d.colUpper[j]! * x)
              ≤ (d.colLower[j]! - d.colUpper[j]!) * x[j]! := by
                exact bound_term_le hNon.1 hNon.2 hBounds.1 hBounds.2 hZero.1 hZero.2
          _ = (arraySub d.colLower.toArray d.colUpper.toArray)[j]! * x[j]! := by
                rw [hSub]; simp)
  have hBoundLe :
      dualBoundCombination p d ≤
        dot (arraySub d.rowLower.toArray d.rowUpper.toArray) (evalAx p x) +
          dot (arraySub d.colLower.toArray d.colUpper.toArray) x := by
    unfold dualBoundCombination
    simp [problemShapeOk_of_prop hShape]
    have hAdd := RatAux.add_le_add hRowLe hColLe
    simpa [Rat.sub_eq_add_neg] using hAdd
  have hBilin :
      dot (arraySub d.rowLower.toArray d.rowUpper.toArray) (evalAx p x) =
        dot (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray)) x :=
    dot_y_evalAx_eq_dot_evalATy_x p (arraySub d.rowLower.toArray d.rowUpper.toArray) x
      hShape hRowSub hXSize
  have hDot := dot_of_stationarity hXSize hDual hStat hQ
  rw [hBilin] at hBoundLe
  rw [hDot]
  exact hBoundLe

/-- Weak duality on `Rat`: any primal-feasible `x` and any dual-feasible
    `d` satisfy `dualObj d ≤ primalObj x`.

    Proof shape (per `PLAN.md` §"Verification layer"):

    1. Stationarity `Aᵀ(yL − yU) + (zL − zU) = c` lets us rewrite
       `c·x` as `Σⱼ (Aᵀ(yL − yU) + (zL − zU))ⱼ · xⱼ`.
    2. Swap finite sums to get
       `Σᵢ (yLᵢ − yUᵢ) · (Ax)ᵢ + Σⱼ (zLⱼ − zUⱼ) · xⱼ`.
    3. Use componentwise bound inequalities
       (`yLᵢ ≥ 0 ∧ (Ax)ᵢ ≥ rₗᵢ ⇒ yLᵢ · (Ax)ᵢ ≥ yLᵢ · rₗᵢ`, three
       symmetric variants) to lower-bound each term by its dual-obj
       contribution.
    4. The remaining shifted sum is exactly `dualObj p d`. -/
theorem weak_duality {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    (hx : isPrimalFeasible p x = true)
    (hd : isDualFeasible    p d = true) :
    dualObj p d ≤ primalObj p x.toArray := by
  obtain ⟨hShape, hFeas⟩ := isPrimalFeasible_imp hx
  obtain ⟨_, hDualFeas⟩ := isDualFeasible_imp hd
  have hBound := bound_combination_le_dot_q hShape hFeas
    hDualFeas.nonneg_zero_absent hDualFeas.stationarity hShape.c_size
  unfold dualObj primalObj
  exact Rat.add_le_add_right.mpr hBound

/-- Optimality certificate is sound: a Boolean-accepted certificate
    really witnesses feasibility and min-optimality. -/
theorem checkOptimal_sound {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    (h : checkOptimal p x d = true) :
    IsFeasible p x.toArray ∧ IsOptimalMin p x.toArray := by
  unfold checkOptimal at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hPrimal, hDualBool⟩, hEqBool⟩ := h
  obtain ⟨hShape, hFeasX⟩ := isPrimalFeasible_imp hPrimal
  obtain ⟨_, hDual⟩ := isDualFeasible_imp hDualBool
  have hEq : primalObj p x.toArray = dualObj p d := by
    simpa [beq_iff_eq] using hEqBool
  refine ⟨hFeasX, hFeasX, ?_⟩
  intro y hFeasY
  have hBound := bound_combination_le_dot_q hShape hFeasY
    hDual.nonneg_zero_absent hDual.stationarity hShape.c_size
  have hWeakY : dualObj p d ≤ primalObj p y := by
    unfold dualObj primalObj
    exact Rat.add_le_add_right.mpr hBound
  rw [hEq]
  exact hWeakY

/-- Infeasibility (Farkas) certificate is sound. -/
theorem checkInfeasible_sound {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : checkInfeasible p d = true) :
    IsInfeasible p := by
  unfold checkInfeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hFarkasBool, hPosBool⟩ := h
  unfold isFarkasFeasible at hFarkasBool
  rw [Bool.and_eq_true] at hFarkasBool
  obtain ⟨hNonnegBool, hZeroBool⟩ := hFarkasBool
  have hShape := dualNonnegAndZeroWhereAbsent_imp_shape hNonnegBool
  have hFarkas := isFarkasFeasible_imp (by
    unfold isFarkasFeasible
    rw [Bool.and_eq_true]
    exact ⟨hNonnegBool, hZeroBool⟩)
  have hPos := boundCombinationPos_imp hPosBool
  intro hExists
  obtain ⟨x, hFeasX⟩ := hExists
  have hStatZero : StationarityAgainst p d (Array.replicate n 0) := by
    intro j hj
    simpa [getElem!_pos (Array.replicate n (0 : Rat)) j (by simpa using hj),
      Array.getElem_replicate] using hFarkas.stationarity_zero j hj
  have hLe := bound_combination_le_dot_q hShape hFeasX
    hFarkas.nonneg_zero_absent hStatZero (by simp)
  have hXSize : x.size = n := hFeasX.1.1
  rw [dot_replicate_left_zero' x n hXSize] at hLe
  have : False := by grind
  exact this.elim

private theorem feasible_addSmul_of_recession
    {m n : Nat} {p : Problem m n} {x ray : Vector Rat n} {lam : Rat}
    (hShape : ProblemShapeOk p)
    (hFeas : IsFeasible p x.toArray)
    (hRay : IsRecessionRay p ray.toArray)
    (hLam : 0 ≤ lam) :
    IsFeasible p (Array.addSmul x.toArray lam ray.toArray) := by
  constructor
  · constructor
    · have hSize := Array.addSmul_size_of_eq x.toArray ray.toArray lam
        (by rw [hFeas.1.1, hRay.size])
      rw [hFeas.1.1] at hSize
      exact hSize
    · intro j
      have hjx : j.val < x.toArray.size := by rw [hFeas.1.1]; exact j.isLt
      have hjr : j.val < ray.toArray.size := by rw [hRay.size]; exact j.isLt
      have hjy : j.val < (Array.addSmul x.toArray lam ray.toArray).size := by
        rw [Array.addSmul_size_of_eq x.toArray ray.toArray lam (by rw [hFeas.1.1, hRay.size])]
        exact hjx
      have hy :
          (Array.addSmul x.toArray lam ray.toArray)[j.val]! =
            x.toArray[j.val]! + lam * ray.toArray[j.val]! :=
        Array.addSmul_get!_of_eq x.toArray ray.toArray lam
          (by rw [hFeas.1.1, hRay.size]) j.val hjx
      have hxBounds := hFeas.1.2 j
      constructor
      · intro l hLo
        change p.colBounds[j.val]!.fst = some l at hLo
        have hrNonneg : 0 ≤ ray.toArray[j.val]! :=
          hRay.col_lo_nonneg j.val j.isLt (by rw [hLo]; rfl)
        have hStep : 0 ≤ lam * ray.toArray[j.val]! := Rat.mul_nonneg hLam hrNonneg
        rw [hy]
        have hxLo := hxBounds.1 l hLo
        grind
      · intro u hHi
        change p.colBounds[j.val]!.snd = some u at hHi
        have hrNonpos : ray.toArray[j.val]! ≤ 0 :=
          hRay.col_hi_nonpos j.val j.isLt (by rw [hHi]; rfl)
        have hStep : lam * ray.toArray[j.val]! ≤ 0 := by
          have := Rat.mul_le_mul_of_nonneg_left hrNonpos hLam
          simpa using this
        rw [hy]
        have hxHi := hxBounds.2 u hHi
        grind
  · intro i
    have hAx :
        (evalAx p (Array.addSmul x.toArray lam ray.toArray))[i.val]! =
          (evalAx p x.toArray)[i.val]! + lam * (evalAx p ray.toArray)[i.val]! :=
      evalAx_addSmul_get! p x.toArray ray.toArray lam hShape hFeas.1.1 hRay.size i.val i.isLt
    have hxBounds := hFeas.2 i
    constructor
    · intro l hLo
      change p.rowBounds[i.val]!.fst = some l at hLo
      have hrNonneg : 0 ≤ (evalAx p ray.toArray)[i.val]! :=
        hRay.row_lo_nonneg i.val i.isLt (by rw [hLo]; rfl)
      have hStep : 0 ≤ lam * (evalAx p ray.toArray)[i.val]! := Rat.mul_nonneg hLam hrNonneg
      rw [hAx]
      have hxLo := hxBounds.1 l hLo
      grind
    · intro u hHi
      change p.rowBounds[i.val]!.snd = some u at hHi
      have hrNonpos : (evalAx p ray.toArray)[i.val]! ≤ 0 :=
        hRay.row_hi_nonpos i.val i.isLt (by rw [hHi]; rfl)
      have hStep : lam * (evalAx p ray.toArray)[i.val]! ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_left hrNonpos hLam
        simpa using this
      rw [hAx]
      have hxHi := hxBounds.2 u hHi
      grind

/-- Unbounded certificate is sound. -/
theorem checkUnbounded_sound {m n : Nat} {p : Problem m n} {x ray : Vector Rat n}
    (h : checkUnbounded p x ray = true) :
    IsUnboundedMin p := by
  unfold checkUnbounded at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hPrimal, hRayBool⟩, hNegBool⟩ := h
  obtain ⟨hShape, hFeasX⟩ := isPrimalFeasible_imp hPrimal
  have hRay := isRecessionRay_imp hRayBool
  have hNeg : dot p.c.toArray ray.toArray < 0 := by
    simpa using hNegBool
  refine ⟨⟨x.toArray, hFeasX⟩, ?_⟩
  intro M
  by_cases hAlready : primalObj p x.toArray < M
  · exact ⟨x.toArray, hFeasX, hAlready⟩
  · let denom := -dot p.c.toArray ray.toArray
    let lam := (primalObj p x.toArray - M) / denom + 1
    have hDenomPos : 0 < denom := by
      unfold denom
      grind
    have hBaseGe : M ≤ primalObj p x.toArray := by
      grind
    have hDiffNonneg : 0 ≤ primalObj p x.toArray - M := by
      exact RatAux.sub_nonneg.mpr hBaseGe
    have hFracNonneg : 0 ≤ (primalObj p x.toArray - M) / denom := by
      have hInv : 0 ≤ denom⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hDenomPos)
      simpa [Rat.div] using Rat.mul_nonneg hDiffNonneg hInv
    have hLamNonneg : 0 ≤ lam := by
      unfold lam
      grind
    have hLamPos : 0 < lam := by
      unfold lam
      grind
    refine ⟨Array.addSmul x.toArray lam ray.toArray,
      feasible_addSmul_of_recession hShape hFeasX hRay hLamNonneg, ?_⟩
    have hObj :
        primalObj p (Array.addSmul x.toArray lam ray.toArray) =
          primalObj p x.toArray + lam * dot p.c.toArray ray.toArray := by
      exact primalObj_addSmul p x.toArray ray.toArray lam (by rw [hShape.c_size, hFeasX.1.1])
        (by rw [hFeasX.1.1, hRay.size])
    rw [hObj]
    unfold lam denom
    have hDrop :
        primalObj p x.toArray +
            (((primalObj p x.toArray - M) / (-dot p.c.toArray ray.toArray) + 1) *
              dot p.c.toArray ray.toArray) =
          M + dot p.c.toArray ray.toArray := by
      have hDenomNe : -dot p.c.toArray ray.toArray ≠ 0 := by grind
      have hcancel :
          (primalObj p x.toArray - M) / (-dot p.c.toArray ray.toArray) *
              (-dot p.c.toArray ray.toArray) =
            primalObj p x.toArray - M := Rat.div_mul_cancel hDenomNe
      have hpart :
          (primalObj p x.toArray - M) / (-dot p.c.toArray ray.toArray) *
              dot p.c.toArray ray.toArray =
            -(primalObj p x.toArray - M) := by
        grind [Rat.mul_neg, Rat.neg_neg]
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
        Rat.sub_eq_add_neg]
    rw [hDrop]
    grind

end LeanSoplex.Verify
