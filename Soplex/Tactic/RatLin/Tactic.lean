/-
Copyright (c) 2026 Kim Morrison.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import Soplex.Tactic.RatLin.NF

/-! # `proveLinearIdentity`: discharge a closed `Rat` affine identity

The `lp` tactic builds an algebraic identity of one of these two shapes:

* LE/LT: `(rhs - lhs) + (λ₀ * t₀ + (λ₁ * t₁ + ... + λₖ * tₖ)) = c`
* Infeasible: `λ₀ * t₀ + (λ₁ * t₁ + ... + λₖ * tₖ) = c`

where each `tᵢ ≡ lhsᵢ - rhsᵢ` is a user-side `Rat` expression (a linear
combination of free `Rat` variables), each `λᵢ` and `c` is a closed `Rat`
literal, and the equation is algebraically valid because all variables
cancel.

`proveLinearIdentity goal` parses both sides of the equation into a
shared `Lin` AST (atoms keyed by `FVarId`), verifies that they normalise
to the same `NF` value, and emits the proof term

```
(Lin.eval_eq_evalNF lhs ρ).trans (Lin.eval_eq_evalNF rhs ρ).symm
```

which the kernel checks by reducing `Lin.toNF lhs` and `Lin.toNF rhs` to
the same canonical `NF`.  See `NF.lean` for the soundness theorem and
the design rationale.

This module is the SoPlex-internal replacement for the
`Soplex.Tactic.LP.proveAlgebraicIdentity` call to `grobner`.  It carries
its work in `Int × Nat` payloads (`Q`) to avoid the irreducibility of
`Rat.add`/`Rat.mul`. -/

open Lean Meta Elab

namespace Soplex.Tactic.RatLin

/-! ## Parser state -/

/-- Mutable state of the parser.  `atoms` is the shared atom table keyed
by `FVarId`; both sides of the identity are parsed against this single
table so that the emitted `Lin` ASTs use compatible atom indices. -/
structure ParseState where
  atoms : Array FVarId := #[]
  deriving Inhabited

abbrev ParseM := StateRefT ParseState MetaM

/-- Look up or extend the atom table with `id`, returning its `Nat`
index.  This is the only way atom indices are minted. -/
private def addAtom (id : FVarId) : ParseM Nat := do
  let st ← get
  match st.atoms.findIdx? (· == id) with
  | some i => return i
  | none =>
      modify fun s => { s with atoms := s.atoms.push id }
      return st.atoms.size

/-! ## Recognising closed `Rat` scalars -/

private def ratType : Expr := mkConst ``Rat

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  match ← id.getDecl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/-- Parse a closed `Nat` literal Expr, returning its `Nat` value.
Accepts `.lit (.natVal n)`, `Nat.zero`, and `Nat.succ` chains. -/
private partial def parseNatLit (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  match e with
  | .lit (.natVal n) => return some n
  | .const ``Nat.zero _ => return some 0
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``Nat.succ _ =>
          if args.size == 1 then
            return (← parseNatLit args[0]!).map (· + 1)
          else return none
      | .const ``OfNat.ofNat _ =>
          -- `OfNat.ofNat Nat n instance` — args[1] is the `n` (Nat literal).
          if args.size ≥ 2 then
            return ← parseNatLit args[1]!
          else return none
      | _ => return none

/-- Parse a closed `Int` literal Expr (in `Int.ofNat n` or `Int.negSucc n`
form), returning its `Int` value. -/
private def parseIntLit (e : Expr) : MetaM (Option Int) := do
  let e ← whnfR e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``Int.ofNat _ =>
      if args.size == 1 then
        return (← parseNatLit args[0]!).map (Int.ofNat ·)
      else return none
  | .const ``Int.negSucc _ =>
      if args.size == 1 then
        return (← parseNatLit args[0]!).map (Int.negSucc ·)
      else return none
  | _ => return none

/-- Try to read a `Q.toRat` Expr (in its raw, pre-whnf form) and return
its rational value.  This is checked BEFORE `whnfR` so that the
`@[inline]` `Q.toRat` isn't unfolded out of the parse. -/
private def tryQToRat? (e : Expr) : MetaM (Option Rat) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``Soplex.Tactic.RatLin.Q.toRat && args.size == 1 do
    return none
  let q ← whnfR args[0]!
  let qFn := q.getAppFn
  let qArgs := q.getAppArgs
  unless qFn.isConstOf ``Soplex.Tactic.RatLin.Q.mk && qArgs.size == 3 do
    return none
  let some n ← parseIntLit qArgs[0]! | return none
  let some d ← parseNatLit qArgs[1]! | return none
  if h : d = 0 then return none
  else return some (Rat.normalize n d h)

/-- Recognise `@OfNat.ofNat Rat n inst`.  Returns the underlying `Nat`
value (parsed from the second argument). -/
private def tryRatOfNatLit? (e : Expr) : MetaM (Option Nat) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``OfNat.ofNat && args.size == 3 do return none
  unless ← isDefEq args[0]! ratType do return none
  parseNatLit args[1]!

/-- Recognise `(OfNat.ofNat n : Rat) / (OfNat.ofNat d : Rat)` with
`d ≠ 0`.  Returns the two `Nat` values. -/
private def tryRatDivLit? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``HDiv.hDiv && args.size == 6 do return none
  unless ← isDefEq args[0]! ratType do return none
  let some n ← tryRatOfNatLit? args[4]! | return none
  let some d ← tryRatOfNatLit? args[5]! | return none
  if d == 0 then return none
  return some (n, d)

/-- Walk `e` rebuilding it so that every `(OfNat n : Rat) / (OfNat d : Rat)`
(with `d ≠ 0`) is replaced by `Q.toRat ⟨Int.ofNat n, d, _⟩`.  Returns the
rewritten Expr and, if any rewrite happened, a proof `e = rewritten`.

The proof is constructed directly from the bridge lemma
`Q.div_ofNat_ofNat_eq_toRat` and `mkCongr` for the surrounding context —
no `simp` or other tactic is involved. -/
private partial def bridgeRatDivLits (e : Expr) : MetaM (Expr × Option Expr) := do
  if let some (n, d) ← tryRatDivLit? e then
    let nNatLit := mkNatLit n
    let dNatLit := mkNatLit d
    let denNeq ← mkAppM ``Ne #[dNatLit, mkNatLit 0]
    let denNeqProof ← mkDecideProof denNeq
    let nIntLit := mkApp (mkConst ``Int.ofNat) nNatLit
    let qLit := mkApp3 (mkConst ``Soplex.Tactic.RatLin.Q.mk) nIntLit dNatLit denNeqProof
    let newE := mkApp (mkConst ``Soplex.Tactic.RatLin.Q.toRat) qLit
    let proof := mkApp3 (mkConst ``Soplex.Tactic.RatLin.Q.div_ofNat_ofNat_eq_toRat)
                   nNatLit dNatLit denNeqProof
    return (newE, some proof)
  match e with
  | .app f x =>
    let (f', pf?) ← bridgeRatDivLits f
    let (x', px?) ← bridgeRatDivLits x
    if pf?.isNone && px?.isNone then
      return (e, none)
    let pf ← match pf? with
      | some p => pure p
      | none => mkEqRefl f
    let px ← match px? with
      | some p => pure p
      | none => mkEqRefl x
    let cong ← mkCongr pf px
    return (mkApp f' x', some cong)
  | _ => return (e, none)

/-- Recognise an expression as a **primitive** closed `Rat` scalar
literal — `OfNat.ofNat n`, `Neg.neg <primitive>`, or
`Q.toRat ⟨n, d, _⟩`.  Compound expressions like `2 - 1` are NOT folded
here; they are parsed as `Lin.sub (Lin.lit 2) (Lin.lit 1)` so that
`Lin.eval` reproduces the user's structure by `rfl`. -/
private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  if let some r ← tryQToRat? e then return some r
  let e ← withReducible <| whnfR e
  if let some r ← tryQToRat? e then return some r
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
          else return none
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? args[2]!).map (fun x => -x)
          else return none
      | _ => return none

/-! ## Parsing into the metaprogram-level `Lin` -/

/-- Metaprogram-level mirror of `Lin`.  We keep this distinct from the
Lean-level `Lin` so that we can normalise to `NF` without crossing into
the Lean kernel; the Lean-level `Lin` Expr is built once at the end. -/
inductive LinM where
  | atom (i : Nat)
  | lit (q : Q)
  | neg (e : LinM)
  | add (e₁ e₂ : LinM)
  | sub (e₁ e₂ : LinM)
  | smul (q : Q) (e : LinM)
  deriving Inhabited

/-- A `Q` literal built from a closed `Rat`.  Both numerator and
denominator come from the materialised `Rat`. -/
private def Q.ofRat (r : Rat) : Q :=
  { num := r.num
    den := r.den
    den_ne := r.den_nz }

/-- Recursively parse a `Rat` expression into a `LinM`. -/
private partial def parseExpr (e : Expr) : ParseM LinM := do
  if let some v ← parseScalar? e then
    return .lit (Q.ofRat v)
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return .lit (Q.ofRat v)
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return .lit (Q.ofRat v)
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp/RatLin: expected a `Rat` expression, found{indentExpr e}"
      let i ← addAtom id
      return .atom i
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return .add (← parseExpr args[4]!) (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            return .sub (← parseExpr args[4]!) (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return .neg (← parseExpr args[2]!)
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              return .smul (Q.ofRat c) (← parseExpr rhs)
            if let some c ← parseScalar? rhs then
              return .smul (Q.ofRat c) (← parseExpr lhs)
            throwError "lp/RatLin: nonlinear multiplication; one side of `*` must be a closed `Rat` scalar{indentExpr e}"
      | _ => pure ()
      throwError "lp/RatLin: unsupported `Rat` expression{indentExpr e}"

/-! ## Normalising at the metaprogram level

`toNFM` mirrors `Lin.toNF` but runs at the metaprogram level so we can
inspect the result for equality.  The Lean-level `Lin` Expr we emit is
the *input* to the kernel-side `Lin.toNF`, not its output: we trust the
metaprogram's `toNFM` to compute the same `NF` as the kernel will, and
the soundness theorem `Lin.eval_eq_evalNF` ties the two together. -/

private def Q.beq (x y : Q) : Bool :=
  x.num * (y.den : Int) == y.num * (x.den : Int)

private def NF.listBEq : List (Nat × Q) → List (Nat × Q) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (i, x) :: xs, (j, y) :: ys => i == j && Q.beq x y && NF.listBEq xs ys

private def NF.beq (a b : NF) : Bool :=
  Q.beq a.const b.const && NF.listBEq a.coeffs b.coeffs

def LinM.toNF : LinM → NF
  | .atom i    => NF.ofAtom i
  | .lit q     => NF.ofLit q
  | .neg e     => NF.neg e.toNF
  | .add e₁ e₂ => NF.add e₁.toNF e₂.toNF
  | .sub e₁ e₂ => NF.add e₁.toNF (NF.neg e₂.toNF)
  | .smul q e  => NF.smul q e.toNF

/-! ## Emitting Expr from `LinM` -/

private def mkIntLit (n : Int) : Expr :=
  match n with
  | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
  | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)

/-- Emit an `Expr` of type `Q`.  Side conditions are discharged by
`mkDecideProof` on closed `Nat` goals. -/
private def mkQExpr (q : Q) : MetaM Expr := do
  let numE := mkIntLit q.num
  let denE := mkNatLit q.den
  let denNeqType ← mkAppM ``Ne #[denE, mkNatLit 0]
  let denNeqProof ← mkDecideProof denNeqType
  return mkApp3 (mkConst ``Q.mk) numE denE denNeqProof

/-- Emit an `Expr` of type `Lin`. -/
private partial def mkLinExpr (l : LinM) : MetaM Expr := do
  match l with
  | .atom i => return mkApp (mkConst ``Lin.atom) (mkNatLit i)
  | .lit q => return mkApp (mkConst ``Lin.lit) (← mkQExpr q)
  | .neg e => return mkApp (mkConst ``Lin.neg) (← mkLinExpr e)
  | .add e₁ e₂ => return mkApp2 (mkConst ``Lin.add) (← mkLinExpr e₁) (← mkLinExpr e₂)
  | .sub e₁ e₂ => return mkApp2 (mkConst ``Lin.sub) (← mkLinExpr e₁) (← mkLinExpr e₂)
  | .smul q e => return mkApp2 (mkConst ``Lin.smul) (← mkQExpr q) (← mkLinExpr e)

/-- Emit an `Expr` of type `Nat → Rat` that decodes atom indices into the
corresponding user `Rat` `FVarId`s.

The decoder is `fun (i : Nat) => arr.get i` where `arr : Lean.RArray Rat`
is a balanced binary search tree built at meta-time by `RArray.ofArray`
and emitted as a closed `.leaf` / `.branch` constructor tree via
`RArray.toExpr`.  The emitted ρ contains no `RArray.ofFn`: the meta-side
`ofFn` only happens here, before `toExpr`, so the proof term shipped to
the kernel has no well-founded-recursion machinery in it.  `RArray.get`
is a reducible abbrev unfolding to `RArray.rec` + `Nat.ble`, which
reduces in `O(log atoms.size)` per lookup.

By construction every atom index that appears in a generated AST is
in range, so the empty-table case is unreachable from the discharger
itself; we still need to emit *some* `Nat → Rat`, and use `fun _ => 0`
in that case. -/
private def mkRho (atoms : Array FVarId) : MetaM Expr := do
  if h : 0 < atoms.size then
    let arr : Lean.RArray FVarId := Lean.RArray.ofArray atoms h
    let arrExpr ← arr.toExpr (mkConst ``Rat) Expr.fvar
    withLocalDecl `i .default (mkConst ``Nat) fun iVar => do
      let body := mkApp3 (mkConst ``Lean.RArray.get [.zero])
        (mkConst ``Rat) arrExpr iVar
      mkLambdaFVars #[iVar] body
  else
    let zero ← mkAppM ``Rat.normalize
      #[mkApp (mkConst ``Int.ofNat) (mkNatLit 0), mkNatLit 1,
        ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 1, mkNatLit 0])]
    withLocalDecl `i .default (mkConst ``Nat) fun iVar => do
      mkLambdaFVars #[iVar] zero

/-! ## The discharger -/

/-- Discharge a closed `Rat` affine identity goal `lhs = rhs`.  Returns
a proof term.  Fails with a descriptive message if either side cannot
be parsed in the supported grammar or the two sides do not normalise
to the same `NF`. -/
def proveLinearIdentity (target : Expr) : MetaM Expr := Lean.withAtLeastMaxRecDepth 65536 do
  -- The target should be `@Eq Rat lhs rhs`.
  let target ← whnfR target
  let fn := target.getAppFn
  let args := target.getAppArgs
  unless fn.isConstOf ``Eq && args.size == 3 do
    throwError "lp/RatLin: expected an Eq goal, got{indentExpr target}"
  let ty := args[0]!
  unless ← isDefEq ty (mkConst ``Rat) do
    throwError "lp/RatLin: expected an Eq on Rat, got{indentExpr target}"
  let lhsExpr0 := args[1]!
  let rhsExpr0 := args[2]!
  -- Bridge any user-side `(p/q : Rat)` literals to canonical `Q.toRat` form
  -- so the parsed `Lin.eval` is `rfl`-equal to the bridged expression.
  let (lhsExpr, lhsBridge?) ← bridgeRatDivLits lhsExpr0
  let (rhsExpr, rhsBridge?) ← bridgeRatDivLits rhsExpr0
  -- Parse both sides against a shared atom table.
  let ((lhsLin, rhsLin), st) ← (do
      let l ← parseExpr lhsExpr
      let r ← parseExpr rhsExpr
      pure (l, r)).run {}
  let nfL := lhsLin.toNF
  let nfR := rhsLin.toNF
  unless NF.beq nfL nfR do
    throwError "lp/RatLin: the two sides do not normalise to the same NF{
      ""}\n  lhs: {lhsExpr}\n  rhs: {rhsExpr}{
      ""}\n  nfL.const = {nfL.const.num}/{nfL.const.den}{
      ""}, nfL.coeffs = {nfL.coeffs.map (fun p => (p.1, p.2.num, p.2.den))}{
      ""}\n  nfR.const = {nfR.const.num}/{nfR.const.den}{
      ""}, nfR.coeffs = {nfR.coeffs.map (fun p => (p.1, p.2.num, p.2.den))}"
  -- Emit Exprs.
  let lhsAst ← mkLinExpr lhsLin
  let rhsAst ← mkLinExpr rhsLin
  let rho ← mkRho st.atoms
  -- proofInternal : Lin.eval lhsAst ρ = Lin.eval rhsAst ρ
  --                ≡ lhsExpr = rhsExpr   (by `rfl` on the eval reductions)
  let pL ← mkAppM ``Lin.eval_eq_evalNF #[lhsAst, rho]
  let pR ← mkAppM ``Lin.eval_eq_evalNF #[rhsAst, rho]
  let pRsym ← mkAppM ``Eq.symm #[pR]
  let proofInternal ← mkAppM ``Eq.trans #[pL, pRsym]
  -- If a bridge was needed on either side, transport through the bridges:
  --   lhsExpr0 = lhsExpr (= rhsExpr via proofInternal) = rhsExpr0
  match lhsBridge?, rhsBridge? with
  | none, none => return proofInternal
  | _, _ =>
    let lhsBridge ← match lhsBridge? with
      | some p => pure p
      | none => mkEqRefl lhsExpr0
    let rhsBridge ← match rhsBridge? with
      | some p => pure p
      | none => mkEqRefl rhsExpr0
    let rhsBridgeSym ← mkAppM ``Eq.symm #[rhsBridge]
    let step1 ← mkAppM ``Eq.trans #[lhsBridge, proofInternal]
    mkAppM ``Eq.trans #[step1, rhsBridgeSym]

end Soplex.Tactic.RatLin
