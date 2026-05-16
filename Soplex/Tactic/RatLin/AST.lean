/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Soplex.Tactic.RatLin.Q

/-! # `Lin`: a reflective AST for linear `Rat` expressions

`Lin` mirrors the `Rat` operators the `lp` tactic feeds into its
algebraic-identity step: atoms (free variables, indexed by `Nat` into a
parser-provided table), closed `Rat` literals lifted via `Q`, negation,
addition, subtraction, and scalar multiplication by a `Q` literal.

`eval` is the semantic interpretation against an atom valuation
`ρ : Nat → Rat`.  We never reduce `eval` in the kernel: the soundness
theorem `eval_eq_evalNF` (in `Soplex.Tactic.RatLin.NF`) rewrites `eval e ρ`
to `evalNF (toNF e) ρ`, and *that* form's equality is closed by `rfl`
after kernel reduction of `toNF`. -/

namespace Soplex.Tactic.RatLin

/-- Reflective AST of a supported `Rat` expression.  Atoms are indexed by
`Nat`; out-of-bounds atoms evaluate to a parser-chosen default (we use
`0`, but the bound is enforced statically in the tactic). -/
inductive Lin where
  | atom (i : Nat)
  | lit (q : Q)
  | neg (e : Lin)
  | add (e₁ e₂ : Lin)
  | sub (e₁ e₂ : Lin)
  | smul (q : Q) (e : Lin)
  deriving Inhabited

namespace Lin

/-- Semantic interpretation of a `Lin` against an atom valuation. -/
def eval : Lin → (Nat → Rat) → Rat
  | atom i,    ρ => ρ i
  | lit q,     _ => q.toRat
  | neg e,     ρ => -(eval e ρ)
  | add e₁ e₂, ρ => eval e₁ ρ + eval e₂ ρ
  | sub e₁ e₂, ρ => eval e₁ ρ - eval e₂ ρ
  | smul q e,  ρ => q.toRat * eval e ρ

end Lin

end Soplex.Tactic.RatLin
