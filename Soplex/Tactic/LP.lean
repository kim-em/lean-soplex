import Lean
import Init.Data.Vector.Lemmas
import Soplex.Basic

open Lean Meta Elab Tactic
open Soplex Soplex.Verify

namespace Soplex.Tactic.LP

@[simp] theorem vector_get_mk {α : Type u} {n : Nat} {xs : Array α}
    {h : xs.size = n} (i : Fin n) :
    (Vector.mk xs h).get i = xs[i.val]'(by rw [h]; exact i.isLt) := by
  rfl

theorem rat_le_of_sub_nonpos {a b : Rat} (h : a - b ≤ 0) : a ≤ b := by
  have hAdd := (Rat.add_le_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_le {a b : Rat} (h : a ≤ b) : a - b ≤ 0 := by
  have hAdd := (Rat.add_le_add_right (a := a) (b := b) (c := -b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_eq {a b : Rat} (h : a = b) : a - b ≤ 0 := by
  subst h
  simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel]

theorem rat_lt_of_sub_neg {a b : Rat} (h : a - b < 0) : a < b := by
  have hAdd := (Rat.add_lt_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_le_of_nonneg_sub {a b : Rat} (h : 0 ≤ b - a) : a ≤ b := by
  exact Soplex.Verify.RatAux.sub_nonneg.mp h

theorem rat_lt_of_pos_sub {a b : Rat} (h : 0 < b - a) : a < b := by
  have hle : a ≤ b := rat_le_of_nonneg_sub (Rat.le_of_lt h)
  exact Rat.lt_of_le_of_ne hle (by
    intro hEq
    subst hEq
    simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel] at h)

theorem lower_bound_of_checkOptimal
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y) :
    primalObj p x.toArray ≤ primalObj p y :=
  (checkOptimal_sound hCheck).2.2 y hFeas

theorem nonneg_obj_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {obj : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptNonneg : 0 ≤ primalObj p x.toArray)
    (hObj : primalObj p y = obj) :
    0 ≤ obj := by
  rw [← hObj]
  exact Rat.le_trans hOptNonneg (lower_bound_of_checkOptimal hCheck hFeas)

theorem pos_obj_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {obj : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptPos : 0 < primalObj p x.toArray)
    (hObj : primalObj p y = obj) :
    0 < obj := by
  rw [← hObj]
  exact Std.lt_of_lt_of_le hOptPos (lower_bound_of_checkOptimal hCheck hFeas)

theorem le_goal_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {lhs rhs : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptNonneg : 0 ≤ primalObj p x.toArray)
    (hObj : primalObj p y = rhs - lhs) :
    lhs ≤ rhs :=
  rat_le_of_nonneg_sub (nonneg_obj_of_min_certificate hCheck hFeas hOptNonneg hObj)

theorem lt_goal_of_min_certificate
    {m n : Nat} {p : Problem m n} {x : Vector Rat n} {d : DualBundle m n}
    {y : Array Rat} {lhs rhs : Rat}
    (hCheck : checkOptimal p x d = true)
    (hFeas : IsFeasible p y)
    (hOptPos : 0 < primalObj p x.toArray)
    (hObj : primalObj p y = rhs - lhs) :
    lhs < rhs :=
  rat_lt_of_pos_sub (pos_obj_of_min_certificate hCheck hFeas hOptPos hObj)

theorem false_of_checkInfeasible
    {m n : Nat} {p : Problem m n} {y : Array Rat} {d : DualBundle m n}
    (hCheck : checkInfeasible p d = true)
    (hFeas : IsFeasible p y) :
    False :=
  checkInfeasible_sound hCheck ⟨y, hFeas⟩

theorem any_of_checkInfeasible
    {m n : Nat} {p : Problem m n} {y : Array Rat} {d : DualBundle m n} {α : Prop}
    (hCheck : checkInfeasible p d = true)
    (hFeas : IsFeasible p y) :
    α :=
  (false_of_checkInfeasible hCheck hFeas).elim


inductive Rel where
  | le
  | lt
  | eq
  deriving Repr, DecidableEq

structure LinExpr where
  const : Rat := 0
  coeffs : Array (FVarId × Rat) := #[]
  deriving Inhabited

structure Row where
  expr : LinExpr
  proof : MetaM Expr

structure ParseState where
  vars : Array FVarId := #[]
  deriving Inhabited

abbrev ParseM := StateT ParseState MetaM

private def ratType : Expr := mkConst ``Rat

private def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

private def addCoeff (coeffs : Array (FVarId × Rat)) (v : FVarId) (c : Rat) :
    Array (FVarId × Rat) := Id.run do
  if c = 0 then
    return coeffs
  let mut out := #[]
  let mut found := false
  for (v', c') in coeffs do
    if v' == v then
      found := true
      let c'' := c' + c
      if c'' != 0 then
        out := out.push (v', c'')
    else
      out := out.push (v', c')
  if found then out else out.push (v, c)

private def LinExpr.add (a b : LinExpr) : LinExpr :=
  { const := a.const + b.const
    coeffs := b.coeffs.foldl (fun acc (v, c) => addCoeff acc v c) a.coeffs }

private def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

private def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

private def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/--
Recognise an expression as a "reducibly-closed" `Rat` scalar.

Policy:
* Unfolding scope is **`withReducible <| whnfR`** — definitions that are
  not reducible-by-default remain opaque.
* Numeric literals are accepted via `OfNat.ofNat _ (.lit (.natVal _)) _`.
* `Neg.neg`, `HAdd`, `HSub`, `HMul` are accepted recursively when both
  operands are themselves scalars.
* `HDiv` is accepted only when both sides reduce to scalars **and** the
  denominator is nonzero. A general affine division such as `x / 2` is
  rejected by `parseExpr` (the variable side returns `none` here).
* An `fvar` is accepted only when it is `let`-bound (`.ldecl`) and its
  body parses as a scalar; `cdecl` parameters return `none`.

Returning `none` means "not a scalar". Two follow-on behaviours in
`parseExpr` depend on this:

* A bare `Rat` `fvar` whose `parseScalar?` returns `none` is treated as
  an LP variable.
* A non-`fvar` application (e.g. `f x` with `f : Rat → Rat` opaque)
  whose `parseScalar?` returns `none` falls through to the
  `unsupported Rat expression` error rather than being coerced into an
  LP variable.
-/
private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  let e ← withReducible <| whnfR e
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
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? args[2]!).map (fun x => -x)
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a + b)
            | _, _ => return none
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some _, some 0 => return none
            | some a, some b => return some (a / b)
            | _, _ => return none
      | _ => return none
      return none

private partial def parseExpr (e : Expr) : ParseM LinExpr := do
  if let some v ← parseScalar? e then
    return { const := v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return { const := v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return { const := v }
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp: expected a Rat expression, found{indentExpr e}"
      addVar id
      return { coeffs := #[(id, 1)] }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).add (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).sub (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseExpr args[2]!).neg
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? e then
            return { const := v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              return (← parseExpr rhs).smul c
            if let some c ← parseScalar? rhs then
              return (← parseExpr lhs).smul c
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | .const ``HDiv.hDiv _ =>
          throwError "lp: division is outside the supported affine Rat grammar"
      | _ => pure ()
      throwError "lp: unsupported Rat expression{indentExpr e}"

private def ensureRat (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  unless ← isDefEq ty ratType do
    throwError "lp: expected a Rat expression, found{indentExpr e}"

private def isRatExpr (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) ratType

private def parseAtomicRat (rel : Rel) (lhs rhs : Expr) :
    ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  unless (← isRatExpr lhs) && (← isRatExpr rhs) do
    return none
  return some (rel, lhs, rhs, ← parseExpr lhs, ← parseExpr rhs)

private def parseAtomic? (type : Expr) : ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  let e := type
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``LE.le _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[2]! args[3]!
  | .const ``GE.ge _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[3]! args[2]!
  | .const ``LT.lt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[2]! args[3]!
  | .const ``GT.gt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[3]! args[2]!
  | .const ``Eq _ =>
      if args.size == 3 then
        return ← parseAtomicRat .eq args[1]! args[2]!
  | _ => pure ()
  return none

private def isAnd? (type : Expr) : Option (Expr × Expr) :=
  let fn := type.getAppFn
  let args := type.getAppArgs
  match fn with
  | .const ``And _ =>
      if args.size == 2 then some (args[0]!, args[1]!) else none
  | _ => none

private partial def collectHypProof (origin : Name) (proof : Expr) :
    ParseM (Array Row) := do
  let type ← inferType proof
  if (isAnd? type).isSome then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    return (← collectHypProof origin left) ++ (← collectHypProof origin right)
  match ← parseAtomic? type with
  | none => return #[]
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict hypothesis `{origin}` is not supported in Stage 1"
  | some (.le, _, _, lhs, rhs) =>
      let row := lhs.sub rhs
      return #[{ expr := row, proof := mkAppM ``rat_sub_nonpos_of_le #[proof] }]
  | some (.eq, _, _, lhs, rhs) =>
      let d := lhs.sub rhs
      return #[
        { expr := d, proof := mkAppM ``rat_sub_nonpos_of_eq #[proof] },
        { expr := d.neg, proof := do mkAppM ``rat_sub_nonpos_of_eq #[← mkEqSymm proof] }]

private def collectHyps : ParseM (Array Row) := do
  let mut rows := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        rows := rows ++ (← collectHypProof decl.userName decl.toExpr)
  return rows

private def coeffAt (e : LinExpr) (v : FVarId) : Rat :=
  match e.coeffs.find? (fun (v', _) => v' == v) with
  | some (_, c) => c
  | none => 0

private def mkEntries (rows : Array LinExpr) (vars : Array FVarId) :
    Array (Fin rows.size × Fin vars.size × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rows.size] do
    if hi : i < rows.size then
      let row := rows[i]
      for j in [0:vars.size] do
        if hj : j < vars.size then
          let c := coeffAt row vars[j]
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

private def buildProblem (rows : Array LinExpr) (obj : LinExpr)
    (vars : Array FVarId) : Problem rows.size vars.size :=
  let rowBounds := rows.map fun r => (none, some (-r.const))
  { c := Vector.ofFn fun j => coeffAt obj vars[j]
    objOffset := obj.const
    a := mkEntries rows vars
    rowBounds := ⟨rowBounds, by simp [rowBounds]⟩
    colBounds := Vector.replicate vars.size (none, none) }

private def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

private def proveByTactic (type : Expr) (tac : TacticM Unit) : TacticM Expr := do
  let proof ← mkFreshExprMVar type
  let mvarId := proof.mvarId!
  let savedGoals ← getGoals
  setGoals [mvarId]
  tac
  let remaining ← getGoals
  unless remaining.isEmpty do
    throwError "lp: internal proof reconstruction left unsolved goals"
  setGoals savedGoals
  instantiateMVars proof

private def mkVectorExpr {α : Type} [ToExpr α] (xs : Array α) (n : Nat) : MetaM Expr := do
  let arr := toExpr xs
  let h ← mkDecideProof (← mkEq (← mkAppM ``Array.size #[arr]) (toExpr n))
  mkAppM ``Vector.mk #[arr, h]

private def mkVectorExprFromElems (type : Expr) (xs : Array Expr) (n : Nat) : MetaM Expr := do
  let arr ← mkArrayLit type xs.toList
  let h ← mkDecideProof (← mkEq (← mkAppM ``Array.size #[arr]) (toExpr n))
  mkAppM ``Vector.mk #[arr, h]

private def mkProblemExpr {m n : Nat} (p : Problem m n) : MetaM Expr := do
  let c ← mkVectorExpr p.c.toArray n
  let rowBounds ← mkVectorExpr p.rowBounds.toArray m
  let colBounds ← mkVectorExpr p.colBounds.toArray n
  mkAppM ``Problem.mk #[c, toExpr p.objOffset, toExpr p.a, rowBounds, colBounds]

private def mkDualExpr {m n : Nat} (d : DualBundle m n) : MetaM Expr := do
  let rowLower ← mkVectorExpr d.rowLower.toArray m
  let rowUpper ← mkVectorExpr d.rowUpper.toArray m
  let colLower ← mkVectorExpr d.colLower.toArray n
  let colUpper ← mkVectorExpr d.colUpper.toArray n
  mkAppM ``DualBundle.mk #[rowLower, rowUpper, colLower, colUpper]

private def mkAssignmentExpr (vars : Array FVarId) : MetaM Expr := do
  let values ← vars.mapM fun id => pure (mkFVar id)
  mkVectorExprFromElems (mkConst ``Rat) values vars.size

private def mkSubExpr (lhs rhs : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[lhs, rhs]

private def mkLeZero (e : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[e, toExpr (0 : Rat)]

private def mkLtZero (e : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[e, toExpr (0 : Rat)]

private def mkNonneg (e : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[toExpr (0 : Rat), e]

private def mkPos (e : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[toExpr (0 : Rat), e]

private def mkTrueEq (b : Expr) : MetaM Expr :=
  mkEq b (toExpr true)

private def reconstructionTactic : TacticM Unit := do
  evalTactic (← `(tactic|
    simp [Soplex.Verify.IsFeasible, Soplex.Verify.ColBoundsSatisfied,
      Soplex.Verify.RowBoundsSatisfied, Soplex.Verify.evalAx, Soplex.Verify.applyAx,
      Soplex.Verify.primalObj, Soplex.Verify.dot]))
  evalTactic (← `(tactic|
    all_goals grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]))

private def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) : TacticM Expr := do
  let rowExprs := rows.map (·.expr)
  let obj := (← (parseExpr rhs).run' { vars := vars }).sub
    (← (parseExpr lhs).run' { vars := vars })
  let p := buildProblem rowExprs obj vars
  let opts : Options := { ({} : Options) with sense := .minimize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp: invalid generated problem: {repr e}"
    | .ok p => pure p
  let sol ←
    match solveExact opts normalized with
    | .error e => throwError "lp: solveExact failed: {repr e}"
    | .ok sol => pure sol
  let pExpr ← mkProblemExpr normalized
  let yVecExpr ← mkAssignmentExpr vars
  let yArrayExpr ← mkAppM ``Vector.toArray #[yVecExpr]
  let hFeasType ← mkAppM ``IsFeasible #[pExpr, yArrayExpr]
  let hFeas ← proveByTactic hFeasType reconstructionTactic
  let verified := verifyOutcome opts defaultDenomBudget normalized sol
  match verified with
  | .optimal x _ =>
      let m := primalObj normalized x.toArray
      if strict then
        unless decide (0 < m) do
          throwError "lp: goal is not entailed; verified optimum is {m}, not > 0"
      else
        unless decide (0 ≤ m) do
          throwError "lp: goal is not entailed; verified optimum is {m}, not ≥ 0"
      let some d := sol.certificate.dual
        | throwError "lp: verified optimal result is missing its dual certificate"
      unless checkOptimal normalized x d do
        throwError "lp: internal error: spliced optimal certificate no longer checks"
      let xExpr ← mkVectorExpr x.toArray vars.size
      let dExpr ← mkDualExpr d
      let checkExpr ← mkAppM ``checkOptimal #[pExpr, xExpr, dExpr]
      let hCheck ← mkDecideProof (← mkTrueEq checkExpr)
      let primalX ← mkAppM ``primalObj #[pExpr, ← mkAppM ``Vector.toArray #[xExpr]]
      let hOptType ← if strict then mkPos primalX else mkNonneg primalX
      let hOpt ← mkDecideProof hOptType
      let objExpr ← mkSubExpr rhs lhs
      let primalY ← mkAppM ``primalObj #[pExpr, yArrayExpr]
      let hObj ← proveByTactic (← mkEq primalY objExpr) reconstructionTactic
      if strict then
        mkAppM ``lt_goal_of_min_certificate #[hCheck, hFeas, hOpt, hObj]
      else
        mkAppM ``le_goal_of_min_certificate #[hCheck, hFeas, hOpt, hObj]
  | .infeasible _ =>
      let some d := sol.certificate.dual
        | throwError "lp: verified infeasible result is missing its dual certificate"
      unless checkInfeasible normalized d do
        throwError "lp: internal error: spliced infeasibility certificate no longer checks"
      let dExpr ← mkDualExpr d
      let checkExpr ← mkAppM ``checkInfeasible #[pExpr, dExpr]
      let hCheck ← mkDecideProof (← mkTrueEq checkExpr)
      let goalType ←
        if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
      mkAppOptM ``any_of_checkInfeasible
        #[none, none, none, none, none, some goalType, some hCheck, some hFeas]
  | .unbounded x ray _ =>
      throwError "lp: objective is unbounded above; base={ratList x.toArray}, ray={ratList ray.toArray}"
  | .unchecked status =>
      throwError "lp: solver outcome was unchecked: {repr status}"

private def solveAtomic (g : MVarId) : TacticM Unit := do
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let ((parsed?, rows), st) ← (do
      let p ← parseAtomic? target
      let hs ← collectHyps
      pure (p, hs)).run {}
    let some (rel, lhsExpr, rhsExpr, _, _) := parsed?
      | throwError "lp: goal is not an atomic Rat comparison"
    match rel with
    | .le =>
        let proof ← proveEntailed rows false st.vars lhsExpr rhsExpr
        g.assign proof
    | .lt =>
        let proof ← proveEntailed rows true st.vars lhsExpr rhsExpr
        g.assign proof
    | .eq =>
        let h₁ ← proveEntailed rows false st.vars lhsExpr rhsExpr
        let h₂ ← proveEntailed rows false st.vars rhsExpr lhsExpr
        let proof ← mkAppM ``Rat.le_antisymm #[h₁, h₂]
        g.assign proof

private partial def solveGoal (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  g.withContext do
    let target ← whnfR (← g.getType)
    if isAnd? target |>.isSome then
      replaceMainGoal [g]
      evalTactic (← `(tactic| constructor))
      let goals ← getGoals
      for subgoal in goals do
        solveGoal subgoal
    else
      solveAtomic g

elab "lp" : tactic => do
  let goals ← getGoals
  match goals with
  | [] => throwError "lp: no goals"
  | g :: rest =>
      setGoals [g]
      solveGoal g
      let newGoals ← getGoals
      setGoals (newGoals ++ rest)

end Soplex.Tactic.LP
