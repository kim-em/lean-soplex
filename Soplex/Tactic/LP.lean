import Lean
import Init.Data.Vector.Lemmas
import Soplex.Basic

open Lean Meta Elab Tactic
open Soplex Soplex.Verify

namespace Soplex.Tactic.LP

@[simp] theorem vector_get_mk {α : Type u} {n : Nat} {xs : Array α}
    {h : xs.size = n} (i : Fin n) :
    (Vector.mk xs h).get i = xs[i.val]'(by rw [h]; exact i.isLt) := by
  rfl

theorem rat_le_of_sub_nonpos {a b : Rat} (h : a - b ≤ 0) : a ≤ b := by
  have hAdd := (Rat.add_le_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_le {a b : Rat} (h : a ≤ b) : a - b ≤ 0 := by
  have hAdd := (Rat.add_le_add_right (a := a) (b := b) (c := -b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_eq {a b : Rat} (h : a = b) : a - b ≤ 0 := by
  subst h
  simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel]

theorem rat_lt_of_sub_neg {a b : Rat} (h : a - b < 0) : a < b := by
  have hAdd := (Rat.add_lt_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_le_of_nonneg_sub {a b : Rat} (h : 0 ≤ b - a) : a ≤ b := by
  exact Soplex.Verify.RatAux.sub_nonneg.mp h

theorem rat_lt_of_pos_sub {a b : Rat} (h : 0 < b - a) : a < b := by
  have hle : a ≤ b := rat_le_of_nonneg_sub (Rat.le_of_lt h)
  exact Rat.lt_of_le_of_ne hle (by
    intro hEq
    subst hEq
    simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel] at h)

theorem lower_bound_of_checkOptimal
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y) :
    primalObj p x.toArray ≤ primalObj p y :=
  (checkOptimal_sound hCheck).2.2 y hFeas

theorem nonneg_obj_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {obj : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptNonneg : 0 ≤ primalObj p x.toArray)
    (hObj : primalObj p y = obj) :
    0 ≤ obj := by
  rw [← hObj]
  exact Rat.le_trans hOptNonneg (lower_bound_of_checkOptimal hCheck hFeas)

theorem pos_obj_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {obj : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptPos : 0 < primalObj p x.toArray)
    (hObj : primalObj p y = obj) :
    0 < obj := by
  rw [← hObj]
  exact Std.lt_of_lt_of_le hOptPos (lower_bound_of_checkOptimal hCheck hFeas)

theorem le_goal_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {lhs rhs : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptNonneg : 0 ≤ primalObj p x.toArray)
    (hObj : primalObj p y = rhs - lhs) :
    lhs ≤ rhs :=
  rat_le_of_nonneg_sub (nonneg_obj_of_min_certificate hCheck hFeas hOptNonneg hObj)

theorem lt_goal_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {lhs rhs : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptPos : 0 < primalObj p x.toArray)
    (hObj : primalObj p y = rhs - lhs) :
    lhs < rhs :=
  rat_lt_of_pos_sub (pos_obj_of_min_certificate hCheck hFeas hOptPos hObj)

theorem false_of_checkInfeasible
    {m n : Nat} {p : Problem m n} {y : Array Rat} {d : DualBundle m n}
    (hCheck : checkInfeasible p d = true)
    (hFeas : IsFeasible p y) :
    False :=
  checkInfeasible_sound hCheck ⟨y, hFeas⟩

theorem any_of_checkInfeasible
    {m n : Nat} {p : Problem m n} {y : Array Rat} {d : DualBundle m n} {α : Prop}
    (hCheck : checkInfeasible p d = true)
    (hFeas : IsFeasible p y) :
    α :=
  (false_of_checkInfeasible hCheck hFeas).elim

private def coeffAdd (a b : Array Rat) : Array Rat :=
  Array.addSmul a 1 b

private def coeffNeg (a : Array Rat) : Array Rat :=
  Array.addSmul (Array.replicate a.size 0) (-1) a

private def coeffSmul (k : Rat) (a : Array Rat) : Array Rat :=
  Array.addSmul (Array.replicate a.size 0) k a

private def unitVector (n i : Nat) : Array Rat :=
  Array.ofFn (fun j : Fin n => if j.val = i then 1 else 0)

private def linEval (coeffs values : Array Rat) (const : Rat) : Rat :=
  dot coeffs values + const

private theorem unitVector_size (n i : Nat) :
    (unitVector n i).size = n := by
  unfold unitVector
  simp

private theorem unitVector_get! (n i j : Nat) (hj : j < n) :
    (unitVector n i)[j]! = if j = i then 1 else 0 := by
  unfold unitVector
  rw [getElem!_pos _ j (by simpa using hj)]
  rw [Array.getElem_ofFn]

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

private theorem dot_addSmul_left
    (a b values : Array Rat) (lam : Rat)
    (ha : a.size = values.size) (hb : b.size = values.size) :
    dot (Array.addSmul a lam b) values = dot a values + lam * dot b values := by
  have hab : a.size = b.size := ha.trans hb.symm
  rw [dot_eq_range_fold (Array.addSmul a lam b) values
    (by rw [Array.addSmul_size_of_eq a b lam hab, ha])]
  rw [dot_eq_range_fold a values ha]
  rw [dot_eq_range_fold b values hb]
  rw [Array.addSmul_size_of_eq a b lam hab]
  rw [← hab]
  calc
    (Array.range a.size).foldl
        (fun acc i => acc + (Array.addSmul a lam b)[i]! * values[i]!) 0
        =
      (Array.range a.size).foldl
        (fun acc i => acc + (a[i]! * values[i]! + lam * (b[i]! * values[i]!))) 0 := by
          apply range_fold_congr
          intro i hi
          rw [Array.addSmul_get!_of_eq a b lam hab i hi]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
    _ =
      (Array.range a.size).foldl (fun acc i => acc + a[i]! * values[i]!) 0 +
        (Array.range a.size).foldl (fun acc i => acc + lam * (b[i]! * values[i]!)) 0 := by
          exact range_fold_add a.size
            (fun i => a[i]! * values[i]!)
            (fun i => lam * (b[i]! * values[i]!))
    _ =
      (Array.range a.size).foldl (fun acc i => acc + a[i]! * values[i]!) 0 +
        lam * (Array.range a.size).foldl (fun acc i => acc + b[i]! * values[i]!) 0 := by
          rw [range_fold_smul]

private theorem linEval_const (values : Array Rat) (n : Nat) (c : Rat)
    (hValues : values.size = n) :
    c = linEval (Array.replicate n 0) values c := by
  unfold linEval
  rw [dot_replicate_left_zero' values n hValues]
  simp [Rat.zero_add]

private theorem linEval_var (values : Array Rat) (n i : Nat)
    (hValues : values.size = n) (hi : i < n) :
    values[i]! = linEval (unitVector n i) values 0 := by
  unfold linEval
  rw [dot_unitVector_left values n i hValues hi]
  simp [Rat.add_zero]

private theorem linEval_add_eq {e₁ e₂ : Rat} {c₁ c₂ values : Array Rat} {k₁ k₂ : Rat}
    (h₁ : e₁ = linEval c₁ values k₁)
    (h₂ : e₂ = linEval c₂ values k₂)
    (h₁s : c₁.size = values.size)
    (h₂s : c₂.size = values.size) :
    e₁ + e₂ = linEval (coeffAdd c₁ c₂) values (k₁ + k₂) := by
  rw [h₁, h₂]
  unfold linEval coeffAdd
  rw [dot_addSmul_left c₁ c₂ values 1 h₁s h₂s]
  simp [Rat.one_mul, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem linEval_neg_eq {e : Rat} {c values : Array Rat} {k : Rat}
    (h : e = linEval c values k)
    (hs : c.size = values.size) :
    -e = linEval (coeffNeg c) values (-k) := by
  rw [h]
  unfold linEval coeffNeg
  have hZero : (Array.replicate c.size 0).size = c.size := by simp
  rw [dot_addSmul_left (Array.replicate c.size 0) c values (-1) (by simp [hs]) hs]
  rw [dot_replicate_left_zero' values c.size (by rw [hs])]
  grind [Rat.mul_assoc, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem linEval_sub_eq {e₁ e₂ : Rat} {c₁ c₂ values : Array Rat} {k₁ k₂ : Rat}
    (h₁ : e₁ = linEval c₁ values k₁)
    (h₂ : e₂ = linEval c₂ values k₂)
    (h₁s : c₁.size = values.size)
    (h₂s : c₂.size = values.size) :
    e₁ - e₂ = linEval (coeffAdd c₁ (coeffNeg c₂)) values (k₁ - k₂) := by
  rw [Rat.sub_eq_add_neg]
  have hNeg := linEval_neg_eq h₂ h₂s
  have hAdd := linEval_add_eq h₁ hNeg h₁s (by
    unfold coeffNeg
    rw [Array.addSmul_size_of_eq]
    · simp [h₂s]
    · simp)
  simpa [Rat.sub_eq_add_neg] using hAdd

private theorem linEval_smul_eq {e : Rat} {c values : Array Rat} {k a : Rat}
    (h : e = linEval c values k)
    (hs : c.size = values.size) :
    a * e = linEval (coeffSmul a c) values (a * k) := by
  rw [h]
  unfold linEval coeffSmul
  have hZero : (Array.replicate c.size 0).size = c.size := by simp
  rw [dot_addSmul_left (Array.replicate c.size 0) c values a (by simp [hs]) hs]
  rw [dot_replicate_left_zero' values c.size (by rw [hs])]
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem linEval_mul_right_eq {e : Rat} {c values : Array Rat} {k a : Rat}
    (h : e = linEval c values k)
    (hs : c.size = values.size) :
    e * a = linEval (coeffSmul a c) values (a * k) := by
  rw [Rat.mul_comm e a]
  exact linEval_smul_eq h hs

private theorem rowUpper_of_linEval {e ax bound : Rat} {coeffs values : Array Rat} {k : Rat}
    (hRow : e ≤ 0)
    (hExpr : e = linEval coeffs values k)
    (hAx : ax = dot coeffs values)
    (hBound : bound = -k) :
    ax ≤ bound := by
  rw [hExpr] at hRow
  unfold linEval at hRow
  rw [hAx, hBound]
  exact rat_le_of_sub_nonpos (by
    simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
      using hRow)

private theorem primalObj_eq_of_linEval {m n : Nat} (p : Problem m n) (y : Array Rat)
    {obj : Rat} {coeffs : Array Rat} {k : Rat}
    (hObj : obj = linEval coeffs y k)
    (hCoeffs : p.c.toArray = coeffs)
    (hOffset : p.objOffset = k) :
    primalObj p y = obj := by
  rw [hObj]
  unfold primalObj linEval
  rw [hCoeffs, hOffset]

private theorem evalAx_get_eq_dot_of_evalATy_unit
    {m n : Nat} (p : Problem m n) (x : Array Rat) (i : Fin m)
    (coeffs : Array Rat)
    (hX : x.size = n)
    (hCoeffs : evalATy p (unitVector m i.val) = coeffs) :
    (evalAx p x)[i.val]! = dot coeffs x := by
  have hLeft :
      dot (unitVector m i.val) (evalAx p x) = (evalAx p x)[i.val]! :=
    dot_unitVector_left (evalAx p x) m i.val (evalAx_size p x) i.isLt
  rw [← hLeft]
  rw [dot_y_evalAx_eq_dot_evalATy_x p (unitVector m i.val) x
    (unitVector_size m i.val) hX]
  rw [hCoeffs]

private theorem ColBoundsSatisfied.allFree
    {m n : Nat} (p : Problem m n) (x : Array Rat)
    (hSize : x.size = n)
    (hFree : ∀ j : Fin n, p.colBounds[j] = (none, none)) :
    ColBoundsSatisfied p x := by
  constructor
  · exact hSize
  · intro j
    rw [hFree j]
    exact ⟨(by intro l h; cases h), (by intro u h; cases h)⟩

private theorem ColBoundsSatisfied.allFreeVector
    {m n : Nat} (p : Problem m n) (x : Array Rat)
    (hSize : x.size = n)
    (hFree : p.colBounds = Vector.replicate n (none, none)) :
    ColBoundsSatisfied p x := by
  apply ColBoundsSatisfied.allFree p x hSize
  intro j
  rw [hFree]
  simp

private theorem RowBoundsSatisfied.rowUpper
    {m n : Nat} (p : Problem m n) (x : Array Rat) (i : Fin m) {u : Rat}
    (hBound : p.rowBounds[i] = (none, some u))
    (hUpper : (evalAx p x)[i.val]! ≤ u) :
    let ax := evalAx p x
    let (lo, hi) := p.rowBounds[i]
    (∀ l, lo = some l → l ≤ ax[i.val]!) ∧
    (∀ h, hi = some h → ax[i.val]! ≤ h) := by
  rw [hBound]
  exact ⟨(by intro l h; cases h), (by intro h hEq; cases hEq; exact hUpper)⟩

private theorem RowBoundsSatisfied.ofRows
    {m n : Nat} (p : Problem m n) (x : Array Rat)
    (hRows :
      ∀ i : Fin m,
        let ax := evalAx p x
        let (lo, hi) := p.rowBounds[i]
        (∀ l, lo = some l → l ≤ ax[i.val]!) ∧
        (∀ h, hi = some h → ax[i.val]! ≤ h)) :
    RowBoundsSatisfied p x :=
  hRows

private theorem RowBoundsSatisfied.ofUpperVector
    {m n : Nat} (p : Problem m n) (x : Array Rat) (bounds : Vector Rat m)
    (hBounds : ∀ i : Fin m, p.rowBounds[i] = (none, some bounds[i]))
    (hUpper : ∀ i : Fin m, (evalAx p x)[i.val]! ≤ bounds[i]) :
    RowBoundsSatisfied p x := by
  apply RowBoundsSatisfied.ofRows
  intro i
  exact RowBoundsSatisfied.rowUpper p x i (hBounds i) (hUpper i)

private theorem IsFeasible.ofBounds
    {m n : Nat} {p : Problem m n} {x : Array Rat}
    (hCols : ColBoundsSatisfied p x)
    (hRows : RowBoundsSatisfied p x) :
    IsFeasible p x :=
  ⟨hCols, hRows⟩


inductive Rel where
  | le
  | lt
  | eq
  deriving Repr, DecidableEq

structure LinExpr where
  const : Rat := 0
  coeffs : Array (FVarId × Rat) := #[]
  deriving Inhabited

structure Row where
  term : Expr
  expr : LinExpr
  proof : MetaM Expr

structure FixedLin where
  coeffs : Array Rat
  coeffsExpr : Expr
  const : Rat
  constExpr : Expr
  proof : Expr
  sizeProof : Expr

structure ParseState where
  vars : Array FVarId := #[]
  deriving Inhabited

abbrev ParseM := StateT ParseState MetaM

private def ratType : Expr := mkConst ``Rat

private def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

private def addCoeff (coeffs : Array (FVarId × Rat)) (v : FVarId) (c : Rat) :
    Array (FVarId × Rat) := Id.run do
  if c = 0 then
    return coeffs
  let mut out := #[]
  let mut found := false
  for (v', c') in coeffs do
    if v' == v then
      found := true
      let c'' := c' + c
      if c'' != 0 then
        out := out.push (v', c'')
    else
      out := out.push (v', c')
  if found then out else out.push (v, c)

private def LinExpr.add (a b : LinExpr) : LinExpr :=
  { const := a.const + b.const
    coeffs := b.coeffs.foldl (fun acc (v, c) => addCoeff acc v c) a.coeffs }

private def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

private def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

private def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/--
Recognise an expression as a "reducibly-closed" `Rat` scalar.

Policy:
* Unfolding scope is **`withReducible <| whnfR`** — definitions that are
  not reducible-by-default remain opaque.
* Numeric literals are accepted via `OfNat.ofNat _ (.lit (.natVal _)) _`.
* `Neg.neg`, `HAdd`, `HSub`, `HMul` are accepted recursively when both
  operands are themselves scalars.
* `HDiv` is accepted only when both sides reduce to scalars **and** the
  denominator is nonzero. A general affine division such as `x / 2` is
  rejected by `parseExpr` (the variable side returns `none` here).
* An `fvar` is accepted only when it is `let`-bound (`.ldecl`) and its
  body parses as a scalar; `cdecl` parameters return `none`.

Returning `none` means "not a scalar". Two follow-on behaviours in
`parseExpr` depend on this:

* A bare `Rat` `fvar` whose `parseScalar?` returns `none` is treated as
  an LP variable.
* A non-`fvar` application (e.g. `f x` with `f : Rat → Rat` opaque)
  whose `parseScalar?` returns `none` falls through to the
  `unsupported Rat expression` error rather than being coerced into an
  LP variable.
-/
private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  let e ← withReducible <| whnfR e
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => parseScalar? value
      | none => return none
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``OfNat.ofNat _ =>
          if args.size == 3 then
            match args[1]! with
            | .lit (.natVal n) => return some (OfNat.ofNat n)
            | _ => return none
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? args[2]!).map (fun x => -x)
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a + b)
            | _, _ => return none
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some _, some 0 => return none
            | some a, some b => return some (a / b)
            | _, _ => return none
      | _ => return none
      return none

private partial def parseExpr (e : Expr) : ParseM LinExpr := do
  if let some v ← parseScalar? e then
    return { const := v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return { const := v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return { const := v }
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp: expected a Rat expression, found{indentExpr e}"
      addVar id
      return { coeffs := #[(id, 1)] }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).add (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).sub (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseExpr args[2]!).neg
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? e then
            return { const := v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              return (← parseExpr rhs).smul c
            if let some c ← parseScalar? rhs then
              return (← parseExpr lhs).smul c
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | .const ``HDiv.hDiv _ =>
          throwError "lp: division is outside the supported affine Rat grammar"
      | _ => pure ()
      throwError "lp: unsupported Rat expression{indentExpr e}"

private def ensureRat (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  unless ← isDefEq ty ratType do
    throwError "lp: expected a Rat expression, found{indentExpr e}"

private def isRatExpr (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) ratType

private def parseAtomicRat (rel : Rel) (lhs rhs : Expr) :
    ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  unless (← isRatExpr lhs) && (← isRatExpr rhs) do
    return none
  return some (rel, lhs, rhs, ← parseExpr lhs, ← parseExpr rhs)

private def parseAtomic? (type : Expr) : ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  let e := type
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``LE.le _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[2]! args[3]!
  | .const ``GE.ge _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[3]! args[2]!
  | .const ``LT.lt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[2]! args[3]!
  | .const ``GT.gt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[3]! args[2]!
  | .const ``Eq _ =>
      if args.size == 3 then
        return ← parseAtomicRat .eq args[1]! args[2]!
  | _ => pure ()
  return none

private def isAnd? (type : Expr) : Option (Expr × Expr) :=
  let fn := type.getAppFn
  let args := type.getAppArgs
  match fn with
  | .const ``And _ =>
      if args.size == 2 then some (args[0]!, args[1]!) else none
  | _ => none

private partial def collectHypProof (origin : Name) (proof : Expr) :
    ParseM (Array Row) := do
  let type ← inferType proof
  if (isAnd? type).isSome then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    return (← collectHypProof origin left) ++ (← collectHypProof origin right)
  match ← parseAtomic? type with
  | none => return #[]
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict hypothesis `{origin}` is not supported in Stage 1"
  | some (.le, lhsExpr, rhsExpr, lhs, rhs) =>
      let row := lhs.sub rhs
      let term ← mkAppM ``HSub.hSub #[lhsExpr, rhsExpr]
      return #[{ term := term, expr := row, proof := mkAppM ``rat_sub_nonpos_of_le #[proof] }]
  | some (.eq, lhsExpr, rhsExpr, lhs, rhs) =>
      let d := lhs.sub rhs
      let term₁ ← mkAppM ``HSub.hSub #[lhsExpr, rhsExpr]
      let term₂ ← mkAppM ``HSub.hSub #[rhsExpr, lhsExpr]
      return #[
        { term := term₁, expr := d, proof := mkAppM ``rat_sub_nonpos_of_eq #[proof] },
        { term := term₂, expr := d.neg, proof := do mkAppM ``rat_sub_nonpos_of_eq #[← mkEqSymm proof] }]

private def collectHyps : ParseM (Array Row) := do
  let mut rows := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        rows := rows ++ (← collectHypProof decl.userName decl.toExpr)
  return rows

private def mkEntriesFromFixedRows (rows : Array FixedLin) (n : Nat) :
    Array (Fin rows.size × Fin n × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rows.size] do
    if hi : i < rows.size then
      let row := rows[i]
      for j in [0:n] do
        if hj : j < n then
          let c := row.coeffs[j]!
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

private def buildProblemFixed (rows : Array FixedLin) (obj : FixedLin)
    (n : Nat) : Problem rows.size n :=
  let rowBounds := rows.map fun r => (none, some (-r.const))
  { c := Vector.ofFn fun j => obj.coeffs[j.val]!
    objOffset := obj.const
    a := mkEntriesFromFixedRows rows n
    rowBounds := ⟨rowBounds, by simp [rowBounds]⟩
    colBounds := Vector.replicate n (none, none) }

private def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

private def mkVectorExpr {α : Type} [ToExpr α] (xs : Array α) (n : Nat) : MetaM Expr := do
  let arr := toExpr xs
  let h ← mkDecideProof (← mkEq (← mkAppM ``Array.size #[arr]) (toExpr n))
  mkAppM ``Vector.mk #[arr, h]

private def mkVectorExprFromElems (type : Expr) (xs : Array Expr) (n : Nat) : MetaM Expr := do
  let arr ← mkArrayLit type xs.toList
  let h ← mkDecideProof (← mkEq (← mkAppM ``Array.size #[arr]) (toExpr n))
  mkAppM ``Vector.mk #[arr, h]

private def mkProblemExpr {m n : Nat} (p : Problem m n) : MetaM Expr := do
  let c ← mkVectorExpr p.c.toArray n
  let rowBounds ← mkVectorExpr p.rowBounds.toArray m
  let colBounds ← mkVectorExpr p.colBounds.toArray n
  mkAppM ``Problem.mk #[c, toExpr p.objOffset, toExpr p.a, rowBounds, colBounds]

private def mkDualExpr {m n : Nat} (d : DualBundle m n) : MetaM Expr := do
  let rowLower ← mkVectorExpr d.rowLower.toArray m
  let rowUpper ← mkVectorExpr d.rowUpper.toArray m
  let colLower ← mkVectorExpr d.colLower.toArray n
  let colUpper ← mkVectorExpr d.colUpper.toArray n
  mkAppM ``DualBundle.mk #[rowLower, rowUpper, colLower, colUpper]

private def mkAssignmentExpr (vars : Array FVarId) : MetaM Expr := do
  let values ← vars.mapM fun id => pure (mkFVar id)
  mkVectorExprFromElems (mkConst ``Rat) values vars.size

private def indexOfVar? (vars : Array FVarId) (id : FVarId) : Option Nat := Id.run do
  for h : i in [0:vars.size] do
    if vars[i] == id then
      return some i
  return none

private def mkSubExpr (lhs rhs : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[lhs, rhs]

private def mkArraySizeProof (xs ys : Expr) : MetaM Expr := do
  let lhs ← mkAppM ``Array.size #[xs]
  let rhs ← mkAppM ``Array.size #[ys]
  unless ← withReducible <| isDefEq lhs rhs do
    throwError "lp: internal affine proof size mismatch{indentExpr lhs}\nvs{indentExpr rhs}"
  mkEqRefl lhs

private def mkArraySizeNatProof (xs : Expr) (n : Nat) : MetaM Expr := do
  let lhs ← mkAppM ``Array.size #[xs]
  let rhs := toExpr n
  unless ← withReducible <| isDefEq lhs rhs do
    throwError "lp: internal affine proof size mismatch{indentExpr lhs}\nvs {n}"
  mkEqRefl lhs

private def mkCoeffSizeProof (coeffs : Expr) (n : Nat) (hYSize : Expr) : MetaM Expr := do
  let lhs ← mkAppM ``Array.size #[coeffs]
  let rhs := toExpr n
  let hCoeff ← mkDecideProof (← mkEq lhs rhs)
  let hYSym ← mkEqSymm hYSize
  mkAppM ``Eq.trans #[hCoeff, hYSym]

private def mkFixedLinConst (vars : Array FVarId) (yArrayExpr : Expr) (hYSize : Expr) (c : Rat) :
    MetaM FixedLin := do
  let coeffs := Array.replicate vars.size 0
  let coeffsExpr := toExpr coeffs
  let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
  let proof ← mkAppM ``linEval_const #[yArrayExpr, toExpr vars.size, toExpr c, hYSize]
  return { coeffs, coeffsExpr, const := c, constExpr := toExpr c, proof, sizeProof := hSize }

private partial def parseFixedExpr (vars : Array FVarId) (yArrayExpr : Expr) (hYSize : Expr) (e : Expr) :
    MetaM FixedLin := do
  if let some v ← parseScalar? e then
    return ← mkFixedLinConst vars yArrayExpr hYSize v
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return ← mkFixedLinConst vars yArrayExpr hYSize v
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return ← mkFixedLinConst vars yArrayExpr hYSize v
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp: expected a Rat expression, found{indentExpr e}"
      let some i := indexOfVar? vars id
        | throwError "lp: internal error: variable was not collected{indentExpr e}"
      let coeffs := unitVector vars.size i
      let coeffsExpr ← mkAppM ``unitVector #[toExpr vars.size, toExpr i]
      let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
      let hIdx ← mkDecideProof (← mkAppM ``LT.lt #[toExpr i, toExpr vars.size])
      let hVar ← mkAppM ``linEval_var #[yArrayExpr, toExpr vars.size, toExpr i, hYSize, hIdx]
      let getExpr ← mkAppM ``GetElem?.getElem! #[yArrayExpr, toExpr i]
      unless ← isDefEq e getExpr do
        throwError "lp: internal error: assignment array is not definitionally aligned with variable{indentExpr e}"
      let hGet ← mkEqRefl e
      let proof ← mkAppM ``Eq.trans #[hGet, hVar]
      return { coeffs, coeffsExpr, const := 0, constExpr := toExpr (0 : Rat), proof, sizeProof := hSize }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            let a ← parseFixedExpr vars yArrayExpr hYSize args[4]!
            let b ← parseFixedExpr vars yArrayExpr hYSize args[5]!
            let coeffs := coeffAdd a.coeffs b.coeffs
            let coeffsExpr ← mkAppM ``coeffAdd #[a.coeffsExpr, b.coeffsExpr]
            let constExpr ← mkAppM ``HAdd.hAdd #[a.constExpr, b.constExpr]
            let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
            let proof ← mkAppM ``linEval_add_eq #[a.proof, b.proof, a.sizeProof, b.sizeProof]
            return { coeffs, coeffsExpr, const := a.const + b.const, constExpr, proof, sizeProof := hSize }
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            let a ← parseFixedExpr vars yArrayExpr hYSize args[4]!
            let b ← parseFixedExpr vars yArrayExpr hYSize args[5]!
            let coeffs := coeffAdd a.coeffs (coeffNeg b.coeffs)
            let bNegExpr ← mkAppM ``coeffNeg #[b.coeffsExpr]
            let coeffsExpr ← mkAppM ``coeffAdd #[a.coeffsExpr, bNegExpr]
            let constExpr ← mkAppM ``HSub.hSub #[a.constExpr, b.constExpr]
            let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
            let proof ← mkAppM ``linEval_sub_eq #[a.proof, b.proof, a.sizeProof, b.sizeProof]
            return { coeffs, coeffsExpr, const := a.const - b.const, constExpr, proof, sizeProof := hSize }
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            let a ← parseFixedExpr vars yArrayExpr hYSize args[2]!
            let coeffs := coeffNeg a.coeffs
            let coeffsExpr ← mkAppM ``coeffNeg #[a.coeffsExpr]
            let constExpr ← mkAppM ``Neg.neg #[a.constExpr]
            let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
            let proof ← mkAppM ``linEval_neg_eq #[a.proof, a.sizeProof]
            return { coeffs, coeffsExpr, const := -a.const, constExpr, proof, sizeProof := hSize }
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? e then
            return ← mkFixedLinConst vars yArrayExpr hYSize v
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              let a ← parseFixedExpr vars yArrayExpr hYSize rhs
              let coeffs := coeffSmul c a.coeffs
              let coeffsExpr ← mkAppM ``coeffSmul #[lhs, a.coeffsExpr]
              let constExpr ← mkAppM ``HMul.hMul #[lhs, a.constExpr]
              let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
              let proof ← mkAppOptM ``linEval_smul_eq
                #[none, none, none, none, some lhs, some a.proof, some a.sizeProof]
              return { coeffs, coeffsExpr, const := c * a.const, constExpr, proof, sizeProof := hSize }
            if let some c ← parseScalar? rhs then
              let a ← parseFixedExpr vars yArrayExpr hYSize lhs
              let coeffs := coeffSmul c a.coeffs
              let coeffsExpr ← mkAppM ``coeffSmul #[rhs, a.coeffsExpr]
              let constExpr ← mkAppM ``HMul.hMul #[rhs, a.constExpr]
              let hSize ← mkCoeffSizeProof coeffsExpr vars.size hYSize
              let proof ← mkAppOptM ``linEval_mul_right_eq
                #[none, none, none, none, some rhs, some a.proof, some a.sizeProof]
              return { coeffs, coeffsExpr, const := c * a.const, constExpr, proof, sizeProof := hSize }
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | .const ``HDiv.hDiv _ =>
          throwError "lp: division is outside the supported affine Rat grammar"
      | _ => pure ()
      throwError "lp: unsupported Rat expression{indentExpr e}"

private partial def mkFinCasesFunction (n : Nat) (motive : Expr → MetaM Expr)
    (branches : Array Expr) : MetaM Expr := do
  unless branches.size = n do
    throwError "lp: internal Fin cases branch count mismatch"
  let finType ← mkAppM ``Fin #[toExpr n]
  withLocalDeclD `i finType fun i => do
    let rec go (n : Nat) (motive : Expr → MetaM Expr)
        (branches : Array Expr) (i : Expr) : MetaM Expr := do
      match n with
      | 0 =>
          let target ← motive i
          mkAppOptM ``Fin.elim0 #[some target, some i]
      | n' + 1 =>
          let motiveType ← (do
            let finType ← mkAppM ``Fin #[toExpr (n' + 1)]
            withLocalDeclD `j finType fun j => do
              let body ← motive j
              mkLambdaFVars #[j] body)
          let head := branches[0]!
          let tail := branches.extract 1 branches.size
          let succFn ←
            mkFinCasesFunction n'
              (fun j => do
                let sj ← mkAppM ``Fin.succ #[j]
                motive sj)
              tail
          mkAppOptM ``Fin.cases #[none, some motiveType, some head, some succFn, some i]
    let body ← go n motive branches i
    mkLambdaFVars #[i] body

private def mkFinExpr (i n : Nat) (h : i < n) : Expr :=
  toExpr (Fin.mk i h)

private def mkVectorGet (vec : Expr) (i : Expr) : MetaM Expr :=
  mkAppM ``Vector.get #[vec, i]

private def mkPairNoneSomeRat (x : Expr) : MetaM Expr := do
  let noneRat ← mkAppOptM ``Option.none #[some ratType]
  let someX ← mkAppM ``Option.some #[x]
  mkAppM ``Prod.mk #[noneRat, someX]

private def mkRowBoundsEqForallType (pExpr boundsVecExpr : Expr) (m : Nat) : MetaM Expr := do
  let finType ← mkAppM ``Fin #[toExpr m]
  withLocalDeclD `i finType fun i => do
    let rb ← mkAppM ``Problem.rowBounds #[pExpr]
    let lhs ← mkVectorGet rb i
    let b ← mkVectorGet boundsVecExpr i
    let rhs ← mkPairNoneSomeRat b
    let body ← mkEq lhs rhs
    mkForallFVars #[i] body

private def mkColBoundsFreeEq (pExpr : Expr) (n : Nat) : MetaM Expr := do
  let lhs ← mkAppM ``Problem.colBounds #[pExpr]
  let noneRat ← mkAppOptM ``Option.none #[some ratType]
  let freePair ← mkAppM ``Prod.mk #[noneRat, noneRat]
  let rhs ← mkAppM ``Vector.replicate #[toExpr n, freePair]
  mkEq lhs rhs

private def mkLeZero (e : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[e, toExpr (0 : Rat)]

private def mkLtZero (e : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[e, toExpr (0 : Rat)]

private def mkNonneg (e : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[toExpr (0 : Rat), e]

private def mkPos (e : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[toExpr (0 : Rat), e]

private def mkTrueEq (b : Expr) : MetaM Expr :=
  mkEq b (toExpr true)

private def mkFeasProof (rows : Array Row) (fixedRows : Array FixedLin)
    (vars : Array FVarId) (pExpr yArrayExpr hYSize : Expr) : TacticM Expr := do
  let m := fixedRows.size
  let n := vars.size
  let colFreeEq ← mkColBoundsFreeEq pExpr n
  let hColFree ← mkDecideProof colFreeEq
  let hCols ← mkAppM ``ColBoundsSatisfied.allFreeVector #[pExpr, yArrayExpr, hYSize, hColFree]
  let bounds := fixedRows.map fun r => -r.const
  let boundsVecExpr ← mkVectorExpr bounds m
  let rowBoundsEqForall ← mkRowBoundsEqForallType pExpr boundsVecExpr m
  let hRowBounds ← mkDecideProof rowBoundsEqForall
  let evalAxExpr ← mkAppM ``evalAx #[pExpr, yArrayExpr]
  let mut upperBranches := #[]
  for h : i in [0:fixedRows.size] do
    let fixed := fixedRows[i]
    let row ←
      if hrow : i < rows.size then
        pure rows[i]
      else
        throwError "lp: internal row proof count mismatch"
    let finExpr := mkFinExpr i m (by simpa [m] using h.upper)
    let coeffsExpr := fixed.coeffsExpr
    let unitExpr ← mkAppM ``unitVector #[toExpr m, toExpr i]
    let evalATyExpr ← mkAppM ``evalATy #[pExpr, unitExpr]
    let hCoeffs ← mkDecideProof (← mkEq evalATyExpr coeffsExpr)
    let hAx ← mkAppM ``evalAx_get_eq_dot_of_evalATy_unit
      #[pExpr, yArrayExpr, finExpr, coeffsExpr, hYSize, hCoeffs]
    let rowProof ← row.proof
    let boundExpr ← mkVectorGet boundsVecExpr finExpr
    let negConstExpr ← mkAppM ``Neg.neg #[fixed.constExpr]
    let hBound ← mkDecideProof (← mkEq boundExpr negConstExpr)
    let hUpper ← mkAppM ``rowUpper_of_linEval #[rowProof, fixed.proof, hAx, hBound]
    upperBranches := upperBranches.push hUpper
  let hUpperFn ← mkFinCasesFunction m
    (fun i => do
      let idx ← mkAppM ``Fin.val #[i]
      let lhs ← mkAppM ``GetElem?.getElem! #[evalAxExpr, idx]
      let rhs ← mkVectorGet boundsVecExpr i
      mkAppM ``LE.le #[lhs, rhs])
    upperBranches
  let hRows ← mkAppM ``RowBoundsSatisfied.ofUpperVector
    #[pExpr, yArrayExpr, boundsVecExpr, hRowBounds, hUpperFn]
  mkAppM ``IsFeasible.ofBounds #[hCols, hRows]

private def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) : TacticM Expr := do
  let yVecExpr ← mkAssignmentExpr vars
  let yArrayExpr ← mkAppM ``Vector.toArray #[yVecExpr]
  let hYSize ← mkAppM ``Vector.size_toArray #[yVecExpr]
  let fixedRows ← rows.mapM fun row => parseFixedExpr vars yArrayExpr hYSize row.term
  let objExpr ← mkSubExpr rhs lhs
  let objFixed ← parseFixedExpr vars yArrayExpr hYSize objExpr
  let p := buildProblemFixed fixedRows objFixed vars.size
  let opts : Options := { ({} : Options) with sense := .minimize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp: invalid generated problem: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => throwError "lp: solveExact failed: {repr e}"
    | .ok sol => pure sol
  let pExpr ← mkProblemExpr normalized
  let hFeas ← mkFeasProof rows fixedRows vars pExpr yArrayExpr hYSize
  let verified := verifyOutcome opts defaultDenomBudget normalized sol
  match verified with
  | .optimal x _ =>
      let m := primalObj normalized x.toArray
      if strict then
        unless decide (0 < m) do
          throwError "lp: goal is not entailed; verified optimum is {m}, not > 0"
      else
        unless decide (0 ≤ m) do
          throwError "lp: goal is not entailed; verified optimum is {m}, not ≥ 0"
      let some d := sol.certificate.dual
        | throwError "lp: verified optimal result is missing its dual certificate"
      unless checkOptimal normalized x d do
        throwError "lp: internal error: spliced optimal certificate no longer checks"
      let xExpr ← mkVectorExpr x.toArray vars.size
      let dExpr ← mkDualExpr d
      let checkExpr ← mkAppM ``checkOptimal #[pExpr, xExpr, dExpr]
      let hCheck ← mkDecideProof (← mkTrueEq checkExpr)
      let primalX ← mkAppM ``primalObj #[pExpr, ← mkAppM ``Vector.toArray #[xExpr]]
      let hOptType ← if strict then mkPos primalX else mkNonneg primalX
      let hOpt ← mkDecideProof hOptType
      let cToArray ← mkAppM ``Vector.toArray #[← mkAppM ``Problem.c #[pExpr]]
      let hCoeffs ← mkDecideProof (← mkEq cToArray objFixed.coeffsExpr)
      let offset ← mkAppM ``Problem.objOffset #[pExpr]
      let hOffset ← mkDecideProof (← mkEq offset objFixed.constExpr)
      let hObj ← mkAppM ``primalObj_eq_of_linEval
        #[pExpr, yArrayExpr, objFixed.proof, hCoeffs, hOffset]
      if strict then
        mkAppM ``lt_goal_of_min_certificate #[hCheck, hFeas, hOpt, hObj]
      else
        mkAppM ``le_goal_of_min_certificate #[hCheck, hFeas, hOpt, hObj]
  | .infeasible _ =>
      let some d := sol.certificate.dual
        | throwError "lp: verified infeasible result is missing its dual certificate"
      unless checkInfeasible normalized d do
        throwError "lp: internal error: spliced infeasibility certificate no longer checks"
      let dExpr ← mkDualExpr d
      let checkExpr ← mkAppM ``checkInfeasible #[pExpr, dExpr]
      let hCheck ← mkDecideProof (← mkTrueEq checkExpr)
      let goalType ←
        if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
      mkAppOptM ``any_of_checkInfeasible
        #[none, none, none, none, none, some goalType, some hCheck, some hFeas]
  | .unbounded x ray _ =>
      throwError "lp: objective is unbounded above; base={ratList x.toArray}, ray={ratList ray.toArray}"
  | .unchecked status =>
      throwError "lp: solver outcome was unchecked: {repr status}"

private def solveAtomic (g : MVarId) : TacticM Unit := do
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let ((parsed?, rows), st) ← (do
      let p ← parseAtomic? target
      let hs ← collectHyps
      pure (p, hs)).run {}
    let some (rel, lhsExpr, rhsExpr, _, _) := parsed?
      | throwError "lp: goal is not an atomic Rat comparison"
    match rel with
    | .le =>
        let proof ← proveEntailed rows false st.vars lhsExpr rhsExpr
        g.assign proof
    | .lt =>
        let proof ← proveEntailed rows true st.vars lhsExpr rhsExpr
        g.assign proof
    | .eq =>
        let h₁ ← proveEntailed rows false st.vars lhsExpr rhsExpr
        let h₂ ← proveEntailed rows false st.vars rhsExpr lhsExpr
        let proof ← mkAppM ``Rat.le_antisymm #[h₁, h₂]
        g.assign proof

private partial def solveGoal (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  g.withContext do
    let target ← whnfR (← g.getType)
    if let some (left, right) := isAnd? target then
      let leftProof ← mkFreshExprMVar left
      let rightProof ← mkFreshExprMVar right
      let proof ← mkAppM ``And.intro #[leftProof, rightProof]
      g.assign proof
      solveGoal leftProof.mvarId!
      solveGoal rightProof.mvarId!
    else
      solveAtomic g

elab "lp" : tactic => do
  let goals ← getGoals
  match goals with
  | [] => throwError "lp: no goals"
  | g :: rest =>
      setGoals [g]
      solveGoal g
      let newGoals ← getGoals
      setGoals (newGoals ++ rest)

end Soplex.Tactic.LP
