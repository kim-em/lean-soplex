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

/-- Build a `List Rat` Expr from the atom table. -/
private def mkAtomList (atoms : Array FVarId) : MetaM Expr := do
  let nil := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Rat)
  let mut acc : Expr := nil
  for _h : k in [0:atoms.size] do
    let revIdx := atoms.size - 1 - k
    acc := mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Rat)
            (Expr.fvar atoms[revIdx]!) acc
  return acc

/-- Emit an `Expr` of type `Nat → Rat` that decodes atom indices into the
corresponding user `Rat` `FVarId`s, via `NF.lookupAtom`.  Out-of-range
indices map to the first atom (a deliberately wrong default value that
is never reached on goals produced by the LP tactic) or `0` when the
atom table is empty. -/
private def mkRho (atoms : Array FVarId) : MetaM Expr := do
  let lst ← mkAtomList atoms
  let default : Expr ←
    if h : atoms.size > 0 then
      pure (Expr.fvar atoms[0])
    else
      -- Fallback: `(0 : Rat)` materialised via `Rat.normalize 0 1` (kernel-reducible).
      mkAppM ``Rat.normalize
        #[mkApp (mkConst ``Int.ofNat) (mkNatLit 0), mkNatLit 1,
          ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 1, mkNatLit 0])]
  withLocalDecl `i .default (mkConst ``Nat) fun iVar => do
    let body := mkApp3 (mkConst ``Soplex.Tactic.RatLin.lookupAtom) iVar lst default
    mkLambdaFVars #[iVar] body

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
  let lhsExpr := args[1]!
  let rhsExpr := args[2]!
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
  -- proof : Lin.eval lhsAst ρ = Lin.eval rhsAst ρ
  let pL ← mkAppM ``Lin.eval_eq_evalNF #[lhsAst, rho]
  let pR ← mkAppM ``Lin.eval_eq_evalNF #[rhsAst, rho]
  let pRsym ← mkAppM ``Eq.symm #[pR]
  let proof ← mkAppM ``Eq.trans #[pL, pRsym]
  return proof

end Soplex.Tactic.RatLin
