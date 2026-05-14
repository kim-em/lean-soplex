import Soplex
open Soplex Soplex.Verify

/--
  maximise  3 x₀ + 5 x₁
  subject to       x₀        ≤ 4
                        2 x₁ ≤ 12
                  3 x₀ + 2 x₁ ≤ 18
                  x₀, x₁ ≥ 0
  Optimum: `x = (2, 6)`, objective `36`.
-/
def lp : Problem 3 2 :=
  { c         := #v[3, 5]
    a         := #[(0, 0, 1), (1, 1, 2), (2, 0, 3), (2, 1, 2)]
    rowBounds := #v[(none, some 4), (none, some 12), (none, some 18)]
    colBounds := #v[(some 0, none), (some 0, none)] }

def main : IO Unit := do
  match solveVerified (opts := { sense := .maximize }) lp with
  | .error e => IO.println s!"solve failed: {repr e}"
  | .ok r =>
    match r.verified with
    | .optimal x h =>
      -- `h.1 : IsFeasible r.normalized x.toArray`
      -- `h.2 : IsOptimal  r.normalized .maximize x.toArray`
      let _ := h
      IO.println s!"optimal x = {repr x.toArray}"
    | .infeasible _    => IO.println "infeasible (with Lean proof)"
    | .unbounded _ _ _ => IO.println "unbounded (with Lean proof)"
    | .unchecked s     => IO.println s!"unchecked: {repr s}"

/--
  Whenever `solveVerified lp` returns `.optimal x h`, the witness `x`
  is a certified feasible and optimal point of the normalised LP. The
  proof is built into the `.optimal` constructor itself; this lemma
  just exposes the API contract.

  See https://github.com/kim-em/soplex/issues/40 for an `lp` tactic
  that would let us state and prove a fully pure-`Rat` version of this
  in a single line.
-/
theorem lp_optimum_correct {r x h}
    (_hr : solveVerified (opts := { sense := .maximize }) lp = .ok r)
    (_hopt : r.verified = .optimal x h) :
    IsFeasible r.normalized x.toArray ∧
      IsOptimal r.normalized .maximize x.toArray :=
  h
