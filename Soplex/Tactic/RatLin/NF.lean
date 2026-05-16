/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Soplex.Tactic.RatLin.AST

/-! # `NF`: sparse linear normal form over `Q`

`NF` is a finite sum `Σᵢ cᵢ * xᵢ + const` represented as a sorted list of
`(atomIndex, coefficient)` pairs plus a constant.  Sortedness, the absence
of duplicate indices, and the absence of zero-coefficient entries are all
maintained as invariants by the combinators below; they are not enforced
in the type (which keeps reduction simple).

The combinators are structurally recursive on a single argument, so the
kernel reduces them on closed `NF` inputs.  `Lin.toNF` then reduces on a
closed `Lin` AST to a canonical `NF` value, which is what makes the final
`Eq.refl` succeed when LHS and RHS normalise identically.

The soundness theorem `Lin.eval_eq_evalNF` ties the semantic interpretation
of a `Lin` AST to that of its normalised form. -/

namespace Soplex.Tactic.RatLin

/-- Sparse linear normal form. -/
structure NF where
  coeffs : List (Nat × Q)
  const : Q
deriving Inhabited

namespace NF

/-! ## Constructors -/

@[inline] def zero : NF := ⟨[], Q.zero⟩
@[inline] def ofLit (q : Q) : NF := ⟨[], q⟩
@[inline] def ofAtom (i : Nat) : NF := ⟨[(i, Q.one)], Q.zero⟩

/-! ## Coefficient-list operations -/

/-- Insert `(i, q)` into a sorted coefficient list.  If `i` already has an
entry, the coefficients are added and the entry is dropped if the result
has numerator zero.  Structural on the list. -/
def insertOne (i : Nat) (q : Q) : List (Nat × Q) → List (Nat × Q)
  | [] => [(i, q)]
  | (j, b) :: rest =>
    if i < j then (i, q) :: (j, b) :: rest
    else if j < i then (j, b) :: insertOne i q rest
    else
      let s := Q.add q b
      if s.num = 0 then rest
      else (i, s) :: rest

/-- Pointwise sum of two coefficient lists.  Structural on the first. -/
def addCoeffs : List (Nat × Q) → List (Nat × Q) → List (Nat × Q)
  | [], bs => bs
  | (i, a) :: as, bs => insertOne i a (addCoeffs as bs)

/-- Negate every coefficient in a list. -/
def negCoeffs (l : List (Nat × Q)) : List (Nat × Q) :=
  l.map (fun p => (p.1, Q.neg p.2))

/-- Scale every coefficient by `q`, dropping zeros. -/
def smulCoeffs (q : Q) (l : List (Nat × Q)) : List (Nat × Q) :=
  l.filterMap (fun p =>
    let s := Q.mul q p.2
    if s.num = 0 then none else some (p.1, s))

/-! ## `NF` combinators -/

@[inline] def neg (a : NF) : NF := ⟨negCoeffs a.coeffs, Q.neg a.const⟩

@[inline] def add (a b : NF) : NF :=
  ⟨addCoeffs a.coeffs b.coeffs, Q.add a.const b.const⟩

@[inline] def smul (q : Q) (a : NF) : NF :=
  ⟨smulCoeffs q a.coeffs, Q.mul q a.const⟩

/-! ## `Lin → NF` -/

end NF

namespace Lin

/-- Normalise a `Lin` AST.  Structural recursion; reduces in the kernel on
closed inputs. -/
def toNF : Lin → NF
  | atom i    => NF.ofAtom i
  | lit q     => NF.ofLit q
  | neg e     => NF.neg (toNF e)
  | add e₁ e₂ => NF.add (toNF e₁) (toNF e₂)
  | sub e₁ e₂ => NF.add (toNF e₁) (NF.neg (toNF e₂))
  | smul q e  => NF.smul q (toNF e)

end Lin

namespace NF

/-! ## Evaluation -/

/-- Evaluate a coefficient list against an atom valuation. -/
def evalCoeffs (l : List (Nat × Q)) (ρ : Nat → Rat) : Rat :=
  l.foldr (fun e acc => e.2.toRat * ρ e.1 + acc) 0

/-- Evaluate an `NF` against an atom valuation. -/
def eval (a : NF) (ρ : Nat → Rat) : Rat := evalCoeffs a.coeffs ρ + a.const.toRat

@[simp] theorem evalCoeffs_nil (ρ : Nat → Rat) : evalCoeffs [] ρ = 0 := rfl

@[simp] theorem evalCoeffs_cons (p : Nat × Q) (rest : List (Nat × Q))
    (ρ : Nat → Rat) :
    evalCoeffs (p :: rest) ρ = p.2.toRat * ρ p.1 + evalCoeffs rest ρ := rfl

/-! ### Soundness of `insertOne` and `addCoeffs` -/

theorem evalCoeffs_insertOne (i : Nat) (q : Q) (l : List (Nat × Q))
    (ρ : Nat → Rat) :
    evalCoeffs (insertOne i q l) ρ = q.toRat * ρ i + evalCoeffs l ρ := by
  induction l with
  | nil => simp [insertOne]
  | cons head tail ih =>
    obtain ⟨j, b⟩ := head
    simp only [insertOne]
    by_cases hij : i < j
    · simp [hij]
    · by_cases hji : j < i
      · simp only [if_neg hij, if_pos hji, evalCoeffs_cons, ih]
        -- b.toRat * ρ j + (q.toRat * ρ i + tail) = q.toRat * ρ i + (b.toRat * ρ j + tail)
        rw [Rat.add_left_comm]
      · -- i = j
        simp only [if_neg hij, if_neg hji]
        have hij_eq : i = j := Nat.le_antisymm (Nat.not_lt.mp hji) (Nat.not_lt.mp hij)
        subst hij_eq
        by_cases hz : (Q.add q b).num = 0
        · simp only [if_pos hz]
          have hsum : q.toRat + b.toRat = 0 := by
            have h1 : (Q.add q b).toRat = 0 := Q.toRat_eq_zero_of_num_zero hz
            rw [Q.toRat_add] at h1
            exact h1
          -- evalCoeffs tail = q.toRat * ρ i + (b.toRat * ρ i + evalCoeffs tail)
          have : q.toRat * ρ i + b.toRat * ρ i = 0 := by
            rw [← Rat.add_mul, hsum, Rat.zero_mul]
          rw [show evalCoeffs ((i, b) :: tail) ρ
                 = b.toRat * ρ i + evalCoeffs tail ρ from rfl,
              ← Rat.add_assoc, this, Rat.zero_add]
        · simp only [if_neg hz, evalCoeffs_cons]
          show (Q.add q b).toRat * ρ i + evalCoeffs tail ρ
             = q.toRat * ρ i + (b.toRat * ρ i + evalCoeffs tail ρ)
          rw [Q.toRat_add, Rat.add_mul, Rat.add_assoc]

theorem evalCoeffs_addCoeffs (l₁ l₂ : List (Nat × Q)) (ρ : Nat → Rat) :
    evalCoeffs (addCoeffs l₁ l₂) ρ = evalCoeffs l₁ ρ + evalCoeffs l₂ ρ := by
  induction l₁ with
  | nil => show evalCoeffs l₂ ρ = 0 + evalCoeffs l₂ ρ; rw [Rat.zero_add]
  | cons head tail ih =>
    obtain ⟨i, a⟩ := head
    show evalCoeffs (insertOne i a (addCoeffs tail l₂)) ρ
       = a.toRat * ρ i + evalCoeffs tail ρ + evalCoeffs l₂ ρ
    rw [evalCoeffs_insertOne, ih, Rat.add_assoc]

theorem evalCoeffs_negCoeffs (l : List (Nat × Q)) (ρ : Nat → Rat) :
    evalCoeffs (negCoeffs l) ρ = -(evalCoeffs l ρ) := by
  induction l with
  | nil => simp [negCoeffs]
  | cons head tail ih =>
    obtain ⟨i, q⟩ := head
    show evalCoeffs ((i, Q.neg q) :: negCoeffs tail) ρ
       = -(q.toRat * ρ i + evalCoeffs tail ρ)
    rw [evalCoeffs_cons, ih, Q.toRat_neg, Rat.neg_mul, Rat.neg_add]

theorem evalCoeffs_smulCoeffs (q : Q) (l : List (Nat × Q)) (ρ : Nat → Rat) :
    evalCoeffs (smulCoeffs q l) ρ = q.toRat * evalCoeffs l ρ := by
  induction l with
  | nil => simp [smulCoeffs]
  | cons head tail ih =>
    obtain ⟨i, c⟩ := head
    show evalCoeffs (List.filterMap (fun p =>
            let s := Q.mul q p.2
            if s.num = 0 then none else some (p.1, s)) ((i, c) :: tail)) ρ
       = q.toRat * (c.toRat * ρ i + evalCoeffs tail ρ)
    simp only [List.filterMap]
    by_cases hz : (Q.mul q c).num = 0
    · simp only [hz]
      change evalCoeffs (smulCoeffs q tail) ρ = q.toRat * (c.toRat * ρ i + evalCoeffs tail ρ)
      have hqc : q.toRat * c.toRat = 0 := by
        rw [← Q.toRat_mul]; exact Q.toRat_eq_zero_of_num_zero hz
      rw [Rat.mul_add, ← Rat.mul_assoc, hqc, Rat.zero_mul, Rat.zero_add, ih]
    · simp only [hz]
      change evalCoeffs ((i, Q.mul q c) :: smulCoeffs q tail) ρ
           = q.toRat * (c.toRat * ρ i + evalCoeffs tail ρ)
      rw [evalCoeffs_cons, ih, Q.toRat_mul, Rat.mul_add, Rat.mul_assoc]

/-! ### Top-level `eval` lemmas -/

theorem eval_add (a b : NF) (ρ : Nat → Rat) :
    eval (add a b) ρ = eval a ρ + eval b ρ := by
  show evalCoeffs (addCoeffs a.coeffs b.coeffs) ρ + (Q.add a.const b.const).toRat
     = (evalCoeffs a.coeffs ρ + a.const.toRat) + (evalCoeffs b.coeffs ρ + b.const.toRat)
  rw [evalCoeffs_addCoeffs, Q.toRat_add]
  -- (X + Y) + (C + D) = (X + C) + (Y + D)
  rw [Rat.add_assoc, Rat.add_assoc (evalCoeffs a.coeffs ρ) a.const.toRat,
      ← Rat.add_assoc (evalCoeffs b.coeffs ρ),
      Rat.add_comm (evalCoeffs b.coeffs ρ) a.const.toRat,
      Rat.add_assoc a.const.toRat,
      ← Rat.add_assoc (evalCoeffs a.coeffs ρ)]

theorem eval_neg (a : NF) (ρ : Nat → Rat) : eval (neg a) ρ = -(eval a ρ) := by
  show evalCoeffs (negCoeffs a.coeffs) ρ + (Q.neg a.const).toRat
     = -(evalCoeffs a.coeffs ρ + a.const.toRat)
  rw [evalCoeffs_negCoeffs, Q.toRat_neg, Rat.neg_add]

theorem eval_smul (q : Q) (a : NF) (ρ : Nat → Rat) :
    eval (smul q a) ρ = q.toRat * eval a ρ := by
  show evalCoeffs (smulCoeffs q a.coeffs) ρ + (Q.mul q a.const).toRat
     = q.toRat * (evalCoeffs a.coeffs ρ + a.const.toRat)
  rw [evalCoeffs_smulCoeffs, Q.toRat_mul, Rat.mul_add]

@[simp] theorem eval_ofAtom (i : Nat) (ρ : Nat → Rat) :
    eval (ofAtom i) ρ = ρ i := by
  show (Q.one.toRat * ρ i + 0) + Q.zero.toRat = ρ i
  rw [Q.toRat_one, Q.toRat_zero, Rat.one_mul, Rat.add_zero, Rat.add_zero]

@[simp] theorem eval_ofLit (q : Q) (ρ : Nat → Rat) :
    eval (ofLit q) ρ = q.toRat := by
  show (0 : Rat) + q.toRat = q.toRat
  rw [Rat.zero_add]

end NF

/-- Look up a `Rat` in a list by `Nat` index, returning `default` on
out-of-range.  Structurally recursive on both arguments; reduces in the
kernel for closed inputs.  Used as the atom-decoder `ρ : Nat → Rat`
emitted by the `RatLin` tactic — bound to a single `def` rather than
nested `ite`s so that emitting `ρ` for N=100 atoms doesn't blow past
`maxRecDepth`. -/
def lookupAtom : Nat → List Rat → Rat → Rat
  | _,     [],      default => default
  | 0,     x :: _,  _       => x
  | n + 1, _ :: xs, default => lookupAtom n xs default

namespace Lin

/-- Soundness: a `Lin` AST and its normal form agree everywhere. -/
theorem eval_eq_evalNF (e : Lin) (ρ : Nat → Rat) :
    eval e ρ = NF.eval (toNF e) ρ := by
  induction e with
  | atom i => simp [eval, toNF]
  | lit q => simp [eval, toNF]
  | neg e ih => rw [eval, toNF, NF.eval_neg, ih]
  | add e₁ e₂ ih₁ ih₂ => rw [eval, toNF, NF.eval_add, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    rw [eval, toNF, NF.eval_add, NF.eval_neg, ih₁, ih₂, Rat.sub_eq_add_neg]
  | smul q e ih => rw [eval, toNF, NF.eval_smul, ih]

end Lin

end Soplex.Tactic.RatLin
