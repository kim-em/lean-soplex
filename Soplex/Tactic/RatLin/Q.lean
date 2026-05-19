/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-! # `Q`: a kernel-reducible rational payload

`Rat.add` and `Rat.mul` are `@[irreducible]` in Lean core, so any normal
form whose internal arithmetic uses ordinary `+`/`*` on `Rat` leaves stuck
terms inside the kernel and the closing `rfl` fails.  We sidestep this by
working with a thin `(Int, Nat)`-payload `Q` whose addition, multiplication,
and negation use only `Int`/`Nat` arithmetic (which is transparent) and only
materialise a `Rat` value via `Rat.normalize` at the leaves of the
evaluation.

Used pervasively by `Soplex.Tactic.LP` to materialise scalar literals into
kernel-reducible form.  The module is kept under the `Soplex.Tactic.RatLin`
namespace for historical reasons (it originally backed a reflective `RatLin`
discharger that has since been removed); lifting it out is a cosmetic
follow-up. -/

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

@[simp] theorem toRat_add (a b : Q) : (Q.add a b).toRat = a.toRat + b.toRat := by
  simp [Q.add, Q.toRat, Rat.normalize_add_normalize]

@[simp] theorem toRat_mul (a b : Q) : (Q.mul a b).toRat = a.toRat * b.toRat := by
  simp [Q.mul, Q.toRat, Rat.normalize_mul_normalize]

@[simp] theorem toRat_neg (a : Q) : (Q.neg a).toRat = -a.toRat := by
  simp [Q.neg, Q.toRat, Rat.neg_normalize]

/-- Two `Q` payloads materialise to the same `Rat` whenever their numerators
and denominators agree under cross-multiplication.  The side condition is a
closed `Int` equality, so the explicit-proof-term discharger in the `lp`
tactic can build it with `decide` over GMP-backed `Int` arithmetic — the only
kernel reduction it ever incurs. -/
theorem toRat_eq_of_cross {x y : Q}
    (h : x.num * (y.den : Int) = y.num * (x.den : Int)) : x.toRat = y.toRat :=
  (Rat.normalize_eq_iff x.den_ne y.den_ne).mpr h

end Q

end Soplex.Tactic.RatLin
