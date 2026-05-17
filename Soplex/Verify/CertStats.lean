/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Soplex.Verify.Budget

/-! # Certificate rational-shape diagnostics

Exploratory tooling for inspecting the exact rationals returned in SoPlex
certificates.  This is intentionally proof-free: it answers questions such
as "are the multipliers dyadic?" and "what integer scaling clears all
denominators?" without changing the trusted checker.
-/

namespace Soplex.Verify

/-- Return `some k` when `n = 2^k`, and `none` otherwise. -/
partial def pow2Exponent? (n : Nat) : Option Nat :=
  let rec go (d k : Nat) : Option Nat :=
    if d = 0 then none
    else if d = 1 then some k
    else if d % 2 = 0 then go (d / 2) (k + 1)
    else none
  go n 0

/-- Aggregated shape data for a collection of reduced `Rat` values. -/
structure RatProfile where
  count : Nat := 0
  nonzero : Nat := 0
  integers : Nat := 0
  dyadic : Nat := 0
  nonDyadic : Nat := 0
  maxDen : Nat := 1
  maxDenBits : Nat := 1
  lcmDen : Nat := 1
  lcmDenBits : Nat := 1
  maxNumBits : Nat := 0
  maxBitLen : Nat := 0
  maxDyadicExponent : Nat := 0
  deriving Repr, Inhabited

namespace RatProfile

def empty : RatProfile := {}

/-- Add one rational to a profile. -/
def add (p : RatProfile) (q : Rat) : RatProfile :=
  let den := q.den
  let denBits := den.bitLen
  let numBits := q.num.natAbs.bitLen
  let lcmDen := Nat.lcm p.lcmDen den
  let exp? := pow2Exponent? den
  { count := p.count + 1
    nonzero := p.nonzero + if q = 0 then 0 else 1
    integers := p.integers + if den = 1 then 1 else 0
    dyadic := p.dyadic + if exp?.isSome then 1 else 0
    nonDyadic := p.nonDyadic + if exp?.isSome then 0 else 1
    maxDen := max p.maxDen den
    maxDenBits := max p.maxDenBits denBits
    lcmDen := lcmDen
    lcmDenBits := lcmDen.bitLen
    maxNumBits := max p.maxNumBits numBits
    maxBitLen := max p.maxBitLen (numBits + denBits)
    maxDyadicExponent := max p.maxDyadicExponent (exp?.getD 0) }

/-- Combine two profiles, including the integer scale that clears every
denominator seen by either input. -/
def merge (a b : RatProfile) : RatProfile :=
  { count := a.count + b.count
    nonzero := a.nonzero + b.nonzero
    integers := a.integers + b.integers
    dyadic := a.dyadic + b.dyadic
    nonDyadic := a.nonDyadic + b.nonDyadic
    maxDen := max a.maxDen b.maxDen
    maxDenBits := max a.maxDenBits b.maxDenBits
    lcmDen := Nat.lcm a.lcmDen b.lcmDen
    lcmDenBits := (Nat.lcm a.lcmDen b.lcmDen).bitLen
    maxNumBits := max a.maxNumBits b.maxNumBits
    maxBitLen := max a.maxBitLen b.maxBitLen
    maxDyadicExponent := max a.maxDyadicExponent b.maxDyadicExponent }

def ofArray (xs : Array Rat) : RatProfile :=
  xs.foldl add empty

def allDyadic (p : RatProfile) : Bool :=
  p.nonDyadic = 0

def allInteger (p : RatProfile) : Bool :=
  p.integers = p.count

/-- Human-readable one-line summary. `lcmDen` is the exact integer scale
which clears all denominators in the profiled collection. -/
def summary (label : String) (p : RatProfile) : String :=
  s!"{label}: count={p.count}, nonzero={p.nonzero}, integers={p.integers}, " ++
  s!"dyadic={p.dyadic}, nonDyadic={p.nonDyadic}, maxDen={p.maxDen}, " ++
  s!"maxDenBits={p.maxDenBits}, lcmDen={p.lcmDen}, lcmDenBits={p.lcmDenBits}, " ++
  s!"maxNumBits={p.maxNumBits}, maxBitLen={p.maxBitLen}, " ++
  s!"maxDyadicExponent={p.maxDyadicExponent}"

end RatProfile

def profileRatArray (xs : Array Rat) : RatProfile :=
  RatProfile.ofArray xs

/-- Profile all four multiplier vectors in a dual certificate separately
and together. -/
structure DualProfile where
  rowLower : RatProfile
  rowUpper : RatProfile
  colLower : RatProfile
  colUpper : RatProfile
  all : RatProfile
  deriving Repr

def profileDual {m n : Nat} (d : DualBundle m n) : DualProfile :=
  let rowLower := profileRatArray d.rowLower.toArray
  let rowUpper := profileRatArray d.rowUpper.toArray
  let colLower := profileRatArray d.colLower.toArray
  let colUpper := profileRatArray d.colUpper.toArray
  { rowLower
    rowUpper
    colLower
    colUpper
    all :=
      RatProfile.merge
        (RatProfile.merge (RatProfile.merge rowLower rowUpper) colLower)
        colUpper }

def DualProfile.summary (p : DualProfile) : String :=
  String.intercalate "\n"
    [ RatProfile.summary "dual.rowLower" p.rowLower
    , RatProfile.summary "dual.rowUpper" p.rowUpper
    , RatProfile.summary "dual.colLower" p.colLower
    , RatProfile.summary "dual.colUpper" p.colUpper
    , RatProfile.summary "dual.all" p.all ]

end Soplex.Verify
