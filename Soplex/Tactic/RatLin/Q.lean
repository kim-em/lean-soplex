/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-! # `Q`: a kernel-reducible rational payload for `RatLin`'s normal form

`Rat.add` and `Rat.mul` are `@[irreducible]` in Lean core, so any normal form
whose internal arithmetic uses ordinary `+`/`*` on `Rat` leaves stuck terms
inside the kernel after `toNF` and the closing `rfl` fails.  We sidestep
this by working with a thin `(Int, Nat)`-payload `Q` whose addition,
multiplication, and negation use only `Int`/`Nat` arithmetic (which is
transparent) and only materialise a `Rat` value via `Rat.normalize` at the
leaves of the evaluation.

This file is internal to `Soplex.Tactic.RatLin`; it is not intended for
re-use elsewhere. -/

namespace Soplex.Tactic.RatLin

/-- A rational payload kept in `(numerator, denominator)` form with a
positivity proof.  Two `Q` values may represent the same rational without
being syntactically equal — we never rely on `Q` equality in proofs,
only on `Q.toRat` equality. -/
structure Q where
  num : Int
  den : Nat
  den_ne : den ≠ 0

instance : Inhabited Q := ⟨0, 1, by decide⟩

namespace Q

@[inline] def zero : Q := ⟨0, 1, by decide⟩
@[inline] def one  : Q := ⟨1, 1, by decide⟩

@[inline] def neg (a : Q) : Q := { a with num := -a.num }

@[inline] def add (a b : Q) : Q :=
  { num := a.num * b.den + b.num * a.den
    den := a.den * b.den
    den_ne := Nat.mul_ne_zero a.den_ne b.den_ne }

@[inline] def mul (a b : Q) : Q :=
  { num := a.num * b.num
    den := a.den * b.den
    den_ne := Nat.mul_ne_zero a.den_ne b.den_ne }

/-- Materialise a `Q` as a `Rat`.  Uses `Rat.normalize`, which reduces in the
kernel, so closed `Q.toRat` calls reduce to canonical `Rat.mk'` literals. -/
@[inline] def toRat (a : Q) : Rat := Rat.normalize a.num a.den a.den_ne

@[simp] theorem toRat_zero : Q.zero.toRat = 0 := Rat.normalize_zero _

@[simp] theorem toRat_one : Q.one.toRat = 1 := rfl

@[simp] theorem toRat_add (a b : Q) : (Q.add a b).toRat = a.toRat + b.toRat := by
  simp [Q.add, Q.toRat, Rat.normalize_add_normalize]

@[simp] theorem toRat_mul (a b : Q) : (Q.mul a b).toRat = a.toRat * b.toRat := by
  simp [Q.mul, Q.toRat, Rat.normalize_mul_normalize]

@[simp] theorem toRat_neg (a : Q) : (Q.neg a).toRat = -a.toRat := by
  simp [Q.neg, Q.toRat, Rat.neg_normalize]

theorem toRat_eq_zero_of_num_zero {a : Q} (h : a.num = 0) : a.toRat = 0 := by
  simp [Q.toRat, h]

theorem toRat_sub (a b : Q) : (Q.add a (Q.neg b)).toRat = a.toRat - b.toRat := by
  rw [toRat_add, toRat_neg, Rat.sub_eq_add_neg]

end Q

end Soplex.Tactic.RatLin
