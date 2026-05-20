import Soplex.Tactic.LP.Problem

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

/-! ## Tactic-side proof assembly. -/

def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

/-! ## Cached `Rat`-arithmetic operator templates.

The explicit-proof-term discharger calls `mkRatAdd`/`mkRatMul`/`mkRatLit`
O(N²) times per certificate. Pre-built fully-applied instance Exprs
avoid repeated typeclass inference for `HAdd`/`HMul`/`HSub`/`Ne` in
this hot path; they are constant Exprs with no metavariables and are
used via raw `mkApp2`/`mkApp`. -/

/-- `@HAdd.hAdd Rat Rat Rat instHAdd_Rat_Rat_Rat` — partially-applied,
takes the two `Rat` arguments. -/
def addRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHAdd [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instAdd)
  mkApp4 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HMul.hMul Rat Rat Rat _` partially applied. -/
def mulRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHMul [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instMul)
  mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HSub.hSub Rat Rat Rat _` partially applied. -/
def subRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHSub [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instSub)
  mkApp4 (mkConst ``HSub.hSub [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@Neg.neg Rat Rat.instNeg` partially applied. -/
def negRatFn : Expr :=
  mkApp2 (mkConst ``Neg.neg [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instNeg)

/-- Build `-a : Rat` Expr without typeclass inference. -/
def mkRatNeg (a : Expr) : Expr := mkApp negRatFn a

/-- Build a `Rat` `HMul.hMul a b` Expr without typeclass inference. -/
def mkRatMul (a b : Expr) : MetaM Expr :=
  return mkApp2 mulRatFn a b

/-- Build a `Rat` `HAdd.hAdd a b` Expr without typeclass inference. -/
def mkRatAdd (a b : Expr) : MetaM Expr :=
  return mkApp2 addRatFn a b

/-- Build a `Rat` `HSub.hSub a b` Expr without typeclass inference. -/
def mkRatSub (a b : Expr) : MetaM Expr :=
  return mkApp2 subRatFn a b

/-- The standing proof `Nat.one_ne_zero : (1 : Nat) ≠ 0`, used as the
denominator-nonzero proof for every integer-denominator `Q` payload. -/
def den1NeZeroProof : Expr := mkConst ``Nat.one_ne_zero

/-- Emit a `Q.mk num den den_ne` Expr for the `Rat` value `r`. For the
overwhelmingly common `r.den = 1` case (integer coefficients) we use the
cached `Nat.one_ne_zero` proof instead of running `mkDecideProof`. -/
def mkQLit (r : Rat) : MetaM Expr := do
  let numE : Expr := match r.num with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)
  let denE : Expr := mkNatLit r.den
  let denNeProof ←
    if r.den == 1 then
      pure den1NeZeroProof
    else
      let denNeType : Expr := mkApp3 (mkConst ``Ne [Level.succ Level.zero])
        (mkConst ``Nat) denE (mkNatLit 0)
      mkDecideProof denNeType
  return mkApp3 (mkConst ``Soplex.Tactic.Q.mk) numE denE denNeProof

/-- Build a `Rat` literal Expr.  We emit a `Q.toRat`-normalised form so
that the explicit-proof-term discharger can apply `Q.toRat_add`/
`toRat_mul`/`toRat_neg` without bridging through `Rat.div`-form
literals. -/
def mkRatLit (r : Rat) : MetaM Expr := do
  return mkApp (mkConst ``Soplex.Tactic.Q.toRat) (← mkQLit r)

/--
Build a Lean expression representing the weighted sum
`λ_{i₀} * term_{i₀} + λ_{i₁} * term_{i₁} + ... + λ_{iₖ₋₁} * term_{iₖ₋₁}`
together with a proof that this sum is `≤ 0`. `entries` lists only the
nonzero multipliers, in iteration order.

Returns `(sumExpr, sumProof)` where:
* `sumExpr : Rat` is the literal sum expression;
* `sumProof : sumExpr ≤ 0`.

The empty list yields `sumExpr = (0 : Rat)` and the trivial proof
`Rat.le_refl : (0 : Rat) ≤ 0`. -/
def buildWeightedSumAndProof
    (entries : Array (Rat × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  if entries.size = 0 then
    let zero ← mkRatLit 0
    let proof ← mkAppOptM ``Rat.le_refl #[some zero]
    return (zero, proof)
  -- Right-fold so the sum nests on the right and the proof is built
  -- bottom-up. We accumulate (sumExpr, sumProof) as we go.
  let n := entries.size
  let last := n - 1
  let (lamₖ, termₖ, hRowₖ) := entries[last]!
  let lamₖExpr ← mkRatLit lamₖ
  let hLamₖ ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), lamₖExpr])
  let sumₖ ← mkRatMul lamₖExpr termₖ
  let proofₖ ← mkAppM ``rat_smul_nonpos #[hRowₖ, hLamₖ]
  let mut sumExpr := sumₖ
  let mut sumProof := proofₖ
  for i in [0:last] do
    let idx := last - 1 - i
    let (lam, term, hRow) := entries[idx]!
    let lamExpr ← mkRatLit lam
    let hLam ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), lamExpr])
    let head ← mkRatMul lamExpr term
    let headProof ← mkAppM ``rat_smul_nonpos #[hRow, hLam]
    let newSum ← mkRatAdd head sumExpr
    let newProof ← mkAppM ``rat_add_nonpos #[headProof, sumProof]
    sumExpr := newSum
    sumProof := newProof
  return (sumExpr, sumProof)

/-- Look up a variable's coefficient inside a `LinExpr`. -/
def LinExpr.coeffOf (e : LinExpr) (v : FVarId) : Rat := Id.run do
  for (v', c) in e.coeffs do
    if v' == v then return c
  return 0

/-- Compute the numerical residual `c = (rhs - lhs) + Σ λᵢ * eᵢ`
expressed as a `LinExpr`. The caller verifies that the variable
coefficients all vanish; what remains is the closed `Rat` constant
that gets fed to `decide` for the sign check and to
`proveCertificateIdentity` for the algebraic identity proof. -/
def computeResidual (objLin : LinExpr) (rowLins : Array LinExpr)
    (mults : Array Rat) : LinExpr := Id.run do
  let mut acc : LinExpr := objLin
  for h : i in [0:rowLins.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      acc := acc.add (LinExpr.smul lam rowLins[i])
  return acc

def isLinExprClosed (e : LinExpr) : Bool :=
  e.coeffs.all (fun (_, c) => c == 0)

/-! ## Explicit-proof-term discharger machinery.

`normalize` walks the affine grammar of a `Rat` expression and returns
`(L : LinExpr, pf : e = ⟦L⟧)` with `L.coeffs` strictly sorted by atom
position in the global `vars` array. `⟦L⟧` is a concrete `Expr`
right-nested rendering with the constant innermost. The proof `pf` is
built from fixed-arity lemmas; the kernel only structurally typechecks
the resulting term, reducing only closed `Int` literal arithmetic inside
the `ratlit_*` side conditions. -/

/-- Position of `v` in the global `vars` array. The caller guarantees
membership; on lookup failure we return `vars.size` so the result is
still a valid total order (the unknown atom sorts last). -/
def varIdx (vars : Array FVarId) (v : FVarId) : Nat :=
  vars.idxOf? v |>.getD vars.size

/-- Render a sorted `LinExpr` into the canonical right-nested `Rat`
Expr `c₀*x₀ + (c₁*x₁ + (… + (cₙ₋₁*xₙ₋₁ + r) …))`. -/
def render (L : LinExpr) : MetaM Expr := do
  let mut acc ← mkRatLit L.const
  let n := L.coeffs.size
  for i in [0:n] do
    let idx := n - 1 - i
    let (v, c) := L.coeffs[idx]!
    let cE ← mkRatLit c
    let head ← mkRatMul cE (Expr.fvar v)
    acc ← mkRatAdd head acc
  return acc

/-! ### Cached side-condition templates for the numeral leaves.

`proveRatlit{Add,Mul,Neg}` are called O(N²) times per certificate. Each
leaf needs the same side-condition shape, such as
`(Q.add qa qb).num * (qm.den : Int) = …`. We compute that template just
once per `lp` invocation, keyed in an `IO.Ref`, and instantiate
`qa`/`qb`/`qm` per leaf. -/

initialize ratlitAddDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitMulDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitNegDomainRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Walk past `n` `Pi` binders and return the body. -/
def stripForalls (n : Nat) (e : Expr) : Expr :=
  match n with
  | 0 => e
  | n + 1 => stripForalls n e.bindingBody!

/-- Compute / fetch the cached side-condition template of `ratlit_add`,
i.e. the type of its 4th explicit argument with the first three
arguments left as bvars `#2, #1, #0` (referring to `qa, qb, qm`). -/
def getRatlitAddDomain : MetaM Expr := do
  if let some t ← ratlitAddDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_add)
  -- typ : ∀ qa qb qm, hType → conclusion
  let body3 := stripForalls 3 typ
  let dom := body3.bindingDomain!
  ratlitAddDomainRef.set (some dom)
  return dom

def getRatlitMulDomain : MetaM Expr := do
  if let some t ← ratlitMulDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_mul)
  let dom := (stripForalls 3 typ).bindingDomain!
  ratlitMulDomainRef.set (some dom)
  return dom

def getRatlitNegDomain : MetaM Expr := do
  if let some t ← ratlitNegDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_neg)
  let dom := (stripForalls 2 typ).bindingDomain!
  ratlitNegDomainRef.set (some dom)
  return dom

/-- Build an `Eq.refl`-shaped proof of a closed `Int` literal equality.
The two sides are kernel-reducible to the same numeric value (this is
what makes the leaf valid in the first place), so `Eq.refl LHS` typechecks
where `LHS = RHS` is expected — moving the literal arithmetic work from
the tactic-side `mkDecideProof` into a single kernel reduction. -/
def mkEqReflProof (hType : Expr) : Expr :=
  -- hType has shape `@Eq Int LHS RHS`; extract LHS and emit `Eq.refl LHS`.
  let lhs := hType.appFn!.appArg!
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Int) lhs

/-- Numeral leaf builder: build a proof of `qaE.toRat + qbE.toRat = qmE.toRat`
where `qmE` is the `Q` payload of `(qaVal + qbVal : Rat)`. -/
def proveRatlitAdd (qaE qbE : Expr) (qaVal qbVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := qaVal + qbVal
  let qmE ← mkQLit mVal
  let template ← getRatlitAddDomain
  let hType := template.instantiate #[qmE, qbE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp4 (mkConst ``ratlit_add) qaE qbE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Numeral leaf builder: build a proof of `qaE.toRat * qbE.toRat = qmE.toRat`. -/
def proveRatlitMul (qaE qbE : Expr) (qaVal qbVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := qaVal * qbVal
  let qmE ← mkQLit mVal
  let template ← getRatlitMulDomain
  let hType := template.instantiate #[qmE, qbE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp4 (mkConst ``ratlit_mul) qaE qbE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Numeral leaf builder: build a proof of `-qaE.toRat = qmE.toRat`. -/
def proveRatlitNeg (qaE : Expr) (qaVal : Rat) :
    MetaM (Rat × Expr × Expr) := do
  let mVal := -qaVal
  let qmE ← mkQLit mVal
  let template ← getRatlitNegDomain
  let hType := template.instantiate #[qmE, qaE]
  let hProof := mkEqReflProof hType
  let lemmaApp := mkApp3 (mkConst ``ratlit_neg) qaE qmE hProof
  return (mVal, qmE, lemmaApp)

/-- Precompute a "spine" of a sorted `LinExpr`: an array of head Exprs
`c_k * x_k`, an array of `Q.mk` payloads for each coefficient (for the
numeral leaves), and an array of suffix renderings where
`suffix[k] = ⟦{coeffs.drop k, const}⟧`. Suffix Exprs are built once and
shared by reference across the whole proof, avoiding the O(N³)
re-rendering of every merge step. -/
def precomputeSpine (L : LinExpr) :
    MetaM (Array Expr × Array Expr × Array Expr) := do
  let n := L.coeffs.size
  let mut heads : Array Expr := Array.mkEmpty n
  let mut qs : Array Expr := Array.mkEmpty n
  for k in [0:n] do
    let (v, c) := L.coeffs[k]!
    let qE ← mkQLit c
    qs := qs.push qE
    let cE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qE
    heads := heads.push (← mkRatMul cE (Expr.fvar v))
  -- Suffix renderings, built right-to-left so each entry references the next.
  let mut suffix : Array Expr := Array.mkEmpty (n + 1)
  suffix := suffix.push (← mkRatLit L.const)
  for k in [0:n] do
    -- The k-th iteration produces `suffix[k+1]` ... no wait, we build from
    -- right to left so suffix[i] is built when k = n - i.
    let _ := k
    let idx := suffix.size  -- next slot
    let cur := suffix[suffix.size - 1]!
    let h := heads[n - idx]!  -- correct head to prepend
    suffix := suffix.push (← mkRatAdd h cur)
  -- `suffix` now has size n+1, with suffix[0] = mkRatLit const (the
  -- innermost) and suffix[n] = full ⟦L⟧. Reverse so suffix[k] is the
  -- rendering starting at coeff k.
  return (heads, qs, suffix.reverse)

/-- The linear ordered merge primitive — the one core proof primitive.

Given two `LinExpr`s `La` and `Lb` whose `coeffs` are sorted ascending by
`varIdx vars`, produce the sorted merge `L = La ⊕ Lb` together with a
proof `pf : ⟦La⟧ + ⟦Lb⟧ = ⟦L⟧`. Linear in `|La.coeffs| + |Lb.coeffs|`,
with all suffix Exprs precomputed and shared by reference. -/
partial def proveMerge (vars : Array FVarId) (La Lb : LinExpr) :
    MetaM (LinExpr × Expr) := do
  let (headA, qA, suffA) ← precomputeSpine La
  let (headB, qB, suffB) ← precomputeSpine Lb
  let (L, pf, _resE) ← go headA qA suffA headB qB suffB 0 0
  return (L, pf)
where
  /-- Returns `(L, pf, ⟦L⟧)` where `pf : ⟦La⟧.suffix i + ⟦Lb⟧.suffix j = ⟦L⟧`
  and `⟦L⟧` is the result-side spine built incrementally (each step
  prepends a single head Expr to the shared previous tail). -/
  go (headA qA suffA headB qB suffB : Array Expr) (i j : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    let aDone := i ≥ La.coeffs.size
    let bDone := j ≥ Lb.coeffs.size
    if aDone && bDone then
      -- Base: pure constants. The leaf expects bare `Q` payloads.
      let qaE ← mkQLit La.const
      let qbE ← mkQLit Lb.const
      let (mVal, _qmE, pf) ← proveRatlitAdd qaE qbE La.const Lb.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    if aDone then
      let (vB, cB) := Lb.coeffs[j]!
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!  -- bare const since i = La.coeffs.size
      let tbE := suffB[j+1]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_right) #[aE, h, tbE, resPrev, pRest]
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    if bDone then
      let (vA, cA) := La.coeffs[i]!
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!
      let bE := suffB[j]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_left) #[h, taE, bE, resPrev, pRest]
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    let (vA, cA) := La.coeffs[i]!
    let (vB, cB) := Lb.coeffs[j]!
    let iA := varIdx vars vA
    let iB := varIdx vars vB
    -- Descending-varIdx convention: coeffs[0] is the largest varIdx, which
    -- the render places outermost. The overall next-outermost head comes
    -- from whichever side has the strictly larger varIdx at its current
    -- position; equal varIdx triggers the `combine` rule.
    if iA > iB then
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!
      let bE := suffB[j]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_left) #[h, taE, bE, resPrev, pRest]
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    else if iA < iB then
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!
      let tbE := suffB[j+1]!
      let resE ← mkRatAdd h resPrev
      let pf := mkAppN (mkConst ``take_right) #[aE, h, tbE, resPrev, pRest]
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    else
      let (mVal, qmE, hm) ← proveRatlitAdd qA[i]! qB[j]! cA cB
      let xE := Expr.fvar vA
      let (restL, pRest, resPrev) ←
        go headA qA suffA headB qB suffB (i+1) (j+1)
      let taE := suffA[i+1]!
      let tbE := suffB[j+1]!
      let cAE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qA[i]!
      let cBE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qB[j]!
      let mE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qmE
      if mVal = 0 then
        let pf := mkAppN (mkConst ``combine_zero)
          #[xE, taE, tbE, resPrev, cAE, cBE, pRest, hm]
        return (restL, pf, resPrev)
      else
        let newHead ← mkRatMul mE xE
        let resE ← mkRatAdd newHead resPrev
        let pf := mkAppN (mkConst ``combine)
          #[xE, taE, tbE, resPrev, cAE, cBE, mE, pRest, hm]
        return ({ restL with coeffs := #[(vA, mVal)] ++ restL.coeffs }, pf, resE)

/-- Scale a sorted `LinExpr` by a closed nonzero `Rat` literal `k`, with
proof `k * ⟦La⟧ = ⟦L⟧`. Linear walk; preserves sortedness. -/
partial def proveSmul (kE : Expr) (kVal : Rat) (La : LinExpr) :
    MetaM (LinExpr × Expr) := do
  let (_headA, qA, suffA) ← precomputeSpine La
  let qkE ← mkQLit kVal
  let (L, pf, _) ← go qA suffA qkE 0
  return (L, pf)
where
  go (qA suffA : Array Expr) (qkE : Expr) (i : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let qaE ← mkQLit La.const
      let (mVal, _qmE, pf) ← proveRatlitMul qkE qaE kVal La.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    let (v, c) := La.coeffs[i]!
    let (mVal, qmE, hm) ← proveRatlitMul qkE qA[i]! kVal c
    let xE := Expr.fvar v
    let (restL, pRest, resPrev) ← go qA suffA qkE (i+1)
    let cE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qA[i]!
    let mE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qmE
    let restE := suffA[i+1]!
    let pf := mkAppN (mkConst ``smul_cons)
      #[kE, xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal = 0 then
      return (restL, pf, resPrev)
    else
      let newHead ← mkRatMul mE xE
      let resE ← mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)

/-- Negate a sorted `LinExpr`, with proof `-⟦La⟧ = ⟦L⟧`. Linear walk;
preserves sortedness. -/
partial def proveNeg (La : LinExpr) : MetaM (LinExpr × Expr) := do
  let (_headA, qA, suffA) ← precomputeSpine La
  let (L, pf, _) ← go qA suffA 0
  return (L, pf)
where
  go (qA suffA : Array Expr) (i : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let qaE ← mkQLit La.const
      let (mVal, _qmE, pf) ← proveRatlitNeg qaE La.const
      let resE ← mkRatLit mVal
      return ({const := mVal}, pf, resE)
    let (v, c) := La.coeffs[i]!
    let (mVal, qmE, hm) ← proveRatlitNeg qA[i]! c
    let xE := Expr.fvar v
    let (restL, pRest, resPrev) ← go qA suffA (i+1)
    let cE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qA[i]!
    let mE := mkApp (mkConst ``Soplex.Tactic.Q.toRat) qmE
    let restE := suffA[i+1]!
    let pf := mkAppN (mkConst ``neg_cons)
      #[xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal = 0 then
      return (restL, pf, resPrev)
    else
      let newHead ← mkRatMul mE xE
      let resE ← mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)

/-- Build `Eq.refl` typed as `lhs = rhs` for two `Rat` Exprs which are
defeq under kernel reduction. Used at literal leaves and atoms, where
`mkRatLit r` and the user's literal Expr (or `1*x + 0` from `atom_norm`)
agree under closed-`Rat` reduction. -/
def mkRatEqByDefeq (lhs rhs : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)

/-- Build `Eq.trans` directly via `mkApp` on the `Eq.trans` constant,
without `Lean.Meta.mkEqTrans`'s `isDefEq` middle-term unification, which
is unnecessary when the two halves agree syntactically by construction. -/
def mkEqTransFast (α aE bE cE p q : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) α aE bE cE p q

/-- Like `proveNeg`, `proveSmul`, `proveMerge` — except this also returns
the rendered `⟦L⟧` Expr alongside the proof, so callers can chain without
re-rendering. The rendered Expr is built incrementally, sharing tails. -/
partial def proveNegR (La : LinExpr) : MetaM (LinExpr × Expr × Expr) := do
  let (L, pf) ← proveNeg La
  return (L, pf, ← render L)

/-- Structural-recursion normaliser. Returns `(L, pf, rL)` with
`pf : e = rL` and `rL = ⟦L⟧`. The rendered `rL` is threaded through the
recursion so the proof terms reference shared spine Exprs instead of
re-rendering them at every syntax node. -/
partial def normalizeR (vars : Array FVarId) (e : Expr) :
    MetaM (LinExpr × Expr × Expr) := do
  -- Quick scalar-literal check (no recursion through `HAdd`/etc.). The
  -- full recursive `parseScalar?` is far more expensive — calling it at
  -- every syntax node dominated tactic-side typeclass inference.
  if let some r ← quickScalarLit? e then
    let lit ← mkRatLit r
    let pf ← mkRatEqByDefeq e lit
    return ({const := r}, pf, lit)
  let eW := e   -- skip `whnfR`: dense rows from `parseExpr` are already in
                -- the recognised head-symbol shape.
  match eW with
  | .fvar id =>
      -- `parseExpr` has already type-checked the atoms in this row/goal
      -- (only `Rat`-typed fvars survive into `vars`), so `normalizeR`
      -- can reuse that invariant instead of rechecking every atom.
      let L : LinExpr := {coeffs := #[(id, 1)]}
      let pf := mkApp (mkConst ``atom_norm) eW
      let rL ← render L
      return (L, pf, rL)
  | _ =>
      let fn := eW.getAppFn
      let args := eW.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HAdd in{indentExpr eW}"
          let aE := args[4]!
          let bE := args[5]!
          let (La, pa, rA) ← normalizeR vars aE
          let (Lb, pb, rB) ← normalizeR vars bE
          let step1 := mkAppN (mkConst ``add_congr_eq) #[aE, rA, bE, rB, pa, pb]
          if Lb.coeffs.size == 1 && Lb.const == 0 then
            let (vB, cB) := Lb.coeffs[0]!
            if !La.coeffs.any (·.1 == vB) then
              let h := rB.appFn!.appArg!  -- extract `cB*vB` from `cB*vB + 0`
              let zeroE ← mkRatLit 0
              let addZeroProof := mkApp (mkConst ``Rat.add_zero) rA
              let pm := mkAppN (mkConst ``take_right)
                #[rA, h, zeroE, rA, addZeroProof]
              let rAddRB ← mkRatAdd rA rB
              let rL ← mkRatAdd h rA
              let pf := mkEqTransFast ratType eW rAddRB rL step1 pm
              let L : LinExpr := { La with coeffs := #[(vB, cB)] ++ La.coeffs }
              return (L, pf, rL)
          let (L, pm) ← proveMerge vars La Lb
          let rL ← render L
          let rAddRB ← mkRatAdd rA rB
          let pf := mkEqTransFast ratType eW rAddRB rL step1 pm
          return (L, pf, rL)
      | .const ``HSub.hSub _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HSub in{indentExpr eW}"
          let aE := args[4]!
          let bE := args[5]!
          let (La, pa, rA) ← normalizeR vars aE
          let (Lb, pb, rB) ← normalizeR vars bE
          let (Lnb, pn, rLnb) ← proveNegR Lb
          let (L, pm) ← proveMerge vars La Lnb
          let rL ← render L
          let negBExpr := mkRatNeg bE
          let negRB := mkRatNeg rB
          let midSub ← mkRatAdd aE negBExpr
          let midAdd ← mkRatAdd rA rLnb
          let step1 := mkAppN (mkConst ``sub_to_add_neg) #[aE, bE]
          let step_neg := mkAppN (mkConst ``neg_congr_eq) #[bE, rB, pb]
          let step_neg_full := mkEqTransFast ratType negBExpr negRB rLnb step_neg pn
          let step2 := mkAppN (mkConst ``add_congr_eq)
            #[aE, rA, negBExpr, rLnb, pa, step_neg_full]
          let chained1 := mkEqTransFast ratType eW midSub midAdd step1 step2
          let pf := mkEqTransFast ratType eW midAdd rL chained1 pm
          return (L, pf, rL)
      | .const ``Neg.neg _ =>
          unless args.size == 3 do
            throwError "lp(normalize): malformed Neg.neg in{indentExpr eW}"
          let aE := args[2]!
          if aE.isFVar then
            let xFVar := aE.fvarId!
            let L : LinExpr := {coeffs := #[(xFVar, -1)]}
            let pf := mkApp (mkConst ``neg_atom_norm) aE
            let rL ← render L
            return (L, pf, rL)
          let (La, pa, rA) ← normalizeR vars aE
          let (L, pn, rL) ← proveNegR La
          let negRA := mkRatNeg rA
          let step1 := mkAppN (mkConst ``neg_congr_eq) #[aE, rA, pa]
          let pf := mkEqTransFast ratType eW negRA rL step1 pn
          return (L, pf, rL)
      | .const ``HMul.hMul _ =>
          unless args.size == 6 do
            throwError "lp(normalize): malformed HMul in{indentExpr eW}"
          let lhsE := args[4]!
          let rhsE := args[5]!
          if let some kVal ← quickScalarLit? lhsE then
            -- Fast path: `k * fvar x` directly to {coeffs:[(x, k)]}.
            if kVal ≠ 0 && rhsE.isFVar then
              let xFVar := rhsE.fvarId!
              let L : LinExpr := {coeffs := #[(xFVar, kVal)]}
              let pf := mkAppN (mkConst ``mul_atom_norm) #[lhsE, rhsE]
              let rL ← render L
              return (L, pf, rL)
            let (Lr, pr, rLr) ← normalizeR vars rhsE
            if kVal = 0 then
              let L : LinExpr := {}
              let zeroE ← mkRatLit 0
              let zeroMulPf ← mkAppM ``Rat.zero_mul #[rhsE]
              return (L, zeroMulPf, zeroE)
            let (L, ps) ← proveSmul lhsE kVal Lr
            let rL ← render L
            let step1 := mkAppN (mkConst ``mul_congr_eq_r)
              #[lhsE, rhsE, rLr, pr]
            let kMulRLr ← mkRatMul lhsE rLr
            let pf := mkEqTransFast ratType eW kMulRLr rL step1 ps
            return (L, pf, rL)
          else if let some kVal ← quickScalarLit? rhsE then
            let (Lr, pr, rLr) ← normalizeR vars lhsE
            let kE := rhsE
            if kVal = 0 then
              let L : LinExpr := {}
              let zeroE ← mkRatLit 0
              let mulZeroPf ← mkAppM ``Rat.mul_zero #[lhsE]
              return (L, mulZeroPf, zeroE)
            let (L, ps) ← proveSmul kE kVal Lr
            let rL ← render L
            let mulComm ← mkAppM ``Rat.mul_comm #[lhsE, kE]
            let step1 := mkAppN (mkConst ``mul_congr_eq_r)
              #[kE, lhsE, rLr, pr]
            let kMulLhs ← mkRatMul kE lhsE
            let kMulRLr ← mkRatMul kE rLr
            let pf := mkEqTransFast ratType eW kMulLhs rL mulComm
              (mkEqTransFast ratType kMulLhs kMulRLr rL step1 ps)
            return (L, pf, rL)
          else
            throwError "lp(normalize): nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | _ =>
          throwError "lp(normalize): unsupported Rat expression{indentExpr eW}"

/-- Phase 2 closer: given `lhsId : Expr` and a closed `Rat` value `cVal`,
build a proof `lhsId = mkRatLit cVal`. Normalises `lhsId` and, since the
algebraic identity already holds numerically, the resulting `LinExpr` has
no surviving coefficients and the constant matches `cVal` — closing by a
`rfl` step at the rendered constant. -/
def proveCertificateIdentity (vars : Array FVarId) (lhsId : Expr)
    (cVal : Rat) : MetaM Expr := do
  let (L, pfNorm, _rL) ← normalizeR vars lhsId
  unless L.const == cVal do
    throwError "lp(closeIdentity): normalised constant {L.const} does not match expected residual {cVal}"
  unless L.coeffs.isEmpty do
    throwError "lp(closeIdentity): normalization invariant violated; {L.coeffs.size} surviving atom(s)"
  -- `pfNorm : lhsId = rL` and `rL = mkRatLit cVal`, so `pfNorm` is the proof we want.
  let cExpr ← mkRatLit cVal
  let target ← mkEq lhsId cExpr
  mkExpectedTypeHint pfNorm target

end Soplex.Tactic.LP.Internal
