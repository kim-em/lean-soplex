/-
  No-FFI lane: the verifier and tactic packages, with no SoPlex
  anywhere in the dependency graph.

  This file builds against `lp-core`, `lp-verify`, and `lp-tactic`,
  but NOT against `lp-backend-soplex-ffi` or `soplex-ffi`. A
  successful `lake build` here proves that the issue-50 split
  decoupled the verifier and tactic from the FFI backend: there is
  no `libsoplex`, no GMP, no Boost on the link line. A consumer who
  only wants to verify externally-produced certificates pays no
  build cost for SoPlex.

  We exercise enough of the API to keep the symbols live — if any
  module in the chain dragged in `SoplexFFI.Basic`, the link step
  would fail on the bare runner with a missing-library error. We do
  not call any solver, since by construction there is no backend
  registered in this build. -/

import LPCore
import LPVerify
import LPTactic

open Soplex Soplex.LP

/-- The empty 0×0 LP: trivially feasible, trivially optimal at the
    empty assignment. Lets us name a `Problem` value to keep the
    `LPCore.Types` symbols live without computing anything. -/
def emptyProblem : Problem 0 0 :=
  { c := Vector.mk #[] rfl
    a := #[]
    rowBounds := Vector.mk #[] rfl
    colBounds := Vector.mk #[] rfl }

/-- Reference `Options` so its symbol is linked too. -/
def defaultOptions : Options := {}

/-- Reference `LPBackend` (from `LPCore.Backend`) so its symbol is
    linked too. The "null" backend below would fail at runtime if
    anyone called it, but the no-FFI lane never actually solves
    anything — the point is to compile and link without `SoplexFFI`. -/
def nullBackend : LPBackend where
  name := "null"
  defaultPriority := 1000
  solveExact _ _ :=
    pure (Except.error (SolveError.bridge "no-ffi lane: no backend"))
  probe := pure (.error "no-ffi lane: probe deliberately fails")

/-- Sanity: the no-FFI lane builds. -/
example : True := trivial
