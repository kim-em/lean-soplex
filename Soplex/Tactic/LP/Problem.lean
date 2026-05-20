import Soplex.Tactic.LP.Parse

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

/-! ## Building the LP problem fed to SoPlex.

The LP is `min (rhs - lhs)` over free `Rat` variables, with constraints
`eᵢ ≤ 0` for each parsed `≤`-row (`=`-rows expand to two `≤`-rows in
`collectHypProof`). SoPlex is only used as an oracle; the returned
dual multipliers are re-checked numerically at tactic time before any
proof term is built. -/

def mkEntries (rowDense : Array (Array Rat)) (n : Nat) :
    Array (Fin rowDense.size × Fin n × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rowDense.size] do
    if hi : i < rowDense.size then
      let coeffs := rowDense[i]
      for j in [0:n] do
        if hj : j < n then
          let c := coeffs[j]!
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

def buildProblem (rowDense : Array (Array Rat)) (rowConsts : Array Rat)
    (objCoeffs : Array Rat) (objConst : Rat) (n : Nat)
    (h : rowDense.size = rowConsts.size := by rfl) :
    Problem rowDense.size n :=
  let rowBounds := rowConsts.map fun c => ((none : Option Rat), some (-c))
  { c := Vector.ofFn fun j => objCoeffs[j.val]!
    objOffset := objConst
    a := mkEntries rowDense n
    rowBounds := ⟨rowBounds, by simp [rowBounds, h]⟩
    colBounds := Vector.replicate n (none, none) }


end Soplex.Tactic.LP.Internal
