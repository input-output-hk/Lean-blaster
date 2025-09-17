import Lean
import Solver.Optimize.Telescope

open Lean Meta Declaration

namespace Solver.Optimize

/-- Return `true` if `n` corresponds to an unsafe definition
    (e.g, partial recursive function, partial inductive predicate, etc). -/
def isUnsafeDef (n : Name) : TranslateEnvT Bool :=
 return (← getConstEnvInfo n).isUnsafe

/-- Return `true` if e corresponds to an enumerator constructor (i.e., constructor without any parameters).
-/
def isEnumConst (e : Expr) : TranslateEnvT Bool := do
  match e with
  | Expr.const n _ =>
      let ConstantInfo.ctorInfo info ← getConstEnvInfo n | return false
      return (info.numFields == 0 && info.numParams == 0 && !info.type.isProp)
  | _ => return false

/-- Return `true` if e corresponds to a nullary constructor or a fully applied parametric constructor.
-/
def isFullyAppliedConst (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const n _ =>
     let ConstantInfo.ctorInfo info ← getConstEnvInfo n | return false
     -- should be fully applied
     -- numFields corresponds to the constructor parameters
     -- numParams corresponds to the Inductive type parameters
     return (e.getAppNumArgs' == info.numFields + info.numParams && !info.type.isProp)
 | _ => return false

/-- Return `true` if e corresponds to a constructor that may contain free or bounded variables. -/
@[always_inline, inline]
def isConstructor (e : Expr) : TranslateEnvT Bool :=
  isEnumConst e <||> (pure e.isLit) <||> isFullyAppliedConst e

/-- Return `true` if e corresponds to a constructor applied to only constant values (e.g., no free or bounded variables). -/
@[always_inline, inline]
def isConstant (e : Expr) : TranslateEnvT Bool :=
  isConstructor e <&&> (pure !(hasVars e))


/-- Return `true` if `c` corresponds to a nullary constructor. -/
def isNullaryCtor (c : Name) : TranslateEnvT Bool := do
  match (← getConstEnvInfo c) with
  | ConstantInfo.ctorInfo info =>
      -- numFields corresponds to the constructor parameters
      pure (info.numFields == 0 && !info.type.isProp)
  | _ => pure false

/-- Return `true` if `t` is not a Prop and corresponds to one of the following:
    - is a sort type; or
    - is a class constraint; or
    - is an inductive type for which either at least one nullary constructor or an Inhabited instance exists.
 TODO: extends check to also consider parametric constructor for which each parameter type satisfy `isSortOrInhabited`.
-/
def isSortOrInhabited (t : Expr) : TranslateEnvT Bool := do
 if (← isPropEnv t) then return false
 else
   match t.getAppFn' with
   | Expr.const n _ =>
       if (← isClassConstraint n) then return true -- break if class constraint
       else match (← getConstEnvInfo n) with
            | ConstantInfo.inductInfo indVal =>
                for ctorName in indVal.ctors do
                  -- inductive type has at least one nullary constructor
                  if (← isNullaryCtor ctorName) then return true
                -- check if InHabited instance exists for t
                hasInhabitedInstance t
            | _ => isType t
   | _ => isType t


/-- Return `! e` when `b = false`. Otherwise return `e`. -/
def toBoolNotExpr (b : Bool) (e : Expr) : TranslateEnvT Expr := do
  if b
  then return e
  else return mkApp (← mkBoolNotOp) e

/-- Return `true` when `e1 := ¬ ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isNotExprOf (e1 : Expr) (e2 : Expr) : MetaM Bool := do
  match propNot? e1 with
  | some op =>
         exprEq e2 op
  | _ => return false


/-- Return `true` when `e1 := not ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isBoolNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool := do
  match boolNot? e1 with
  | some op => exprEq e2 op
  | _ => return false

/-- Return `true` when `e1 := false = c ∧ e2 := true = c`. -/
def isNegBoolEqOf (e1: Expr) (e2: Expr) : MetaM Bool := do
 match eq? e1, eq? e2 with
 | some (_, e1_op1, e1_op2), some (_, e2_op1, e2_op2) =>
     match e1_op1, e2_op1 with
      | Expr.const ``false _, Expr.const ``true _ => exprEq e1_op2 e2_op2
      | _, _ => return false
 | _, _ => return false


/-- Inductive type used to characterize Nat binary operators when
    at least one operand is a constant.
    This type is exclusively used by function `toNatCstOpExpr?`
-/
inductive NatCstOpInfo where
  /-- Nat.add N e info. -/
  | NatAddExpr (n : Nat) (e : Expr) : NatCstOpInfo
  /-- Nat.sub N e info. -/
  | NatSubLeftExpr (n : Nat) (e : Expr) : NatCstOpInfo
  /-- Nat.sub e N info. -/
  | NatSubRightExpr (e : Expr) (n : Nat)  : NatCstOpInfo
  /-- Nat.mul N e info. -/
  | NatMulExpr (n : Nat) (e : Expr) : NatCstOpInfo
  /-- Nat.div N e info. -/
  | NatDivLeftExpr (n : Nat) (e : Expr) : NatCstOpInfo
  /-- Nat.div e N info. -/
  | NatDivRightExpr (e : Expr) (n : Nat) : NatCstOpInfo
  /-- Nat.mod N e info. -/
  | NatModLeftExpr (n : Nat) (e : Expr) : NatCstOpInfo
  /-- Nat.mod e N info. -/
  | NatModRightExpr (e : Expr) (n : Nat) : NatCstOpInfo


/-- Return a `NatCstOpInfo` for `e` according to the following rules:
    - NatAddExpr N n (if e := Nat.add N n)
    - NatSubLeftExpr N n (if e := Nat.sub N n)
    - NatSubRightExpr n N (if e := Nat.sub n N)
    - NatMulExpr N n (if e := Nat.mul N n)
    - NatDivLeftExpr N n (if e := Nat.div N n)
    - NatDivLeftExpr n N (if e := Nat.div n N)
    - NatModLeftExpr N n (if e := Nat.mod N n)
    - NatModRightExpr n N (if e := Nat.mod n N)

    Return `none` when `e` is not a full applied Nat binary operator.
    Assume that operands have already been reordered for commutative operators.
-/
def toNatCstOpExpr? (e: Expr) : Option NatCstOpInfo :=
 match binOp? e with
 | some (f, op1, op2) =>
    match f, (isNatValue? op1), (isNatValue? op2) with
    | Expr.const ``Nat.add _, some n, _ => some (NatCstOpInfo.NatAddExpr n op2)
    | Expr.const ``Nat.sub _, some n, _ => some (NatCstOpInfo.NatSubLeftExpr n op2)
    | Expr.const ``Nat.sub _, _, some n => some (NatCstOpInfo.NatSubRightExpr op1 n)
    | Expr.const ``Nat.mul _, some n, _ => some (NatCstOpInfo.NatMulExpr n op2)
    | Expr.const ``Nat.div _, some n, _ => some (NatCstOpInfo.NatDivLeftExpr n op2)
    | Expr.const ``Nat.div _, _, some n => some (NatCstOpInfo.NatDivRightExpr op1 n)
    | Expr.const ``Nat.mod _, some n, _ => some (NatCstOpInfo.NatModLeftExpr n op2)
    | Expr.const ``Nat.mod _, _, some n => some (NatCstOpInfo.NatModRightExpr op1 n)
    | _, _, _ => none
 | _ => none


/-- Return `true` when `e1 := -ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
@[always_inline, inline]
def isIntNegExprOf (e1: Expr) (e2 : Expr) : MetaM Bool := do
  match intNeg? e1 with
  | some op => exprEq e2 op
  | _ => return false


/-- Inductive type used to characterize Int binary operators when
    at least one operand is a constant.
    This type is exclusively used by function `toIntCstOpExpr?`
-/
inductive IntCstOpInfo where
  /-- Int.add N e info. -/
  | IntAddExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.mul N e info. -/
  | IntMulExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.tdiv N e info. -/
  | IntTDivLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.tdiv e N info. -/
  | IntTDivRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.tmod N e info. -/
  | IntTModLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.tmod e N info. -/
  | IntTModRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.ediv N e info. -/
  | IntEDivLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.ediv e N info. -/
  | IntEDivRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.emod N e info. -/
  | IntEModLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.emod e N info. -/
  | IntEModRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.fdiv N e info. -/
  | IntFDivLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.fdiv e N info. -/
  | IntFDivRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.fmod N e info. -/
  | IntFModLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.fmod e N info. -/
  | IntFModRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.neg (Int.add N e).  -/
  | IntNegAddExpr (n : Int) (e : Expr) : IntCstOpInfo


/-- Return a `IntCstOpInfo` for `e` according to the following rules:
    - IntAddExpr N n (if e := Int.add N n)
    - IntMulExpr N n (if e := Int.mul N n)
    - IntTDivLeftExpr N n (if e := Int.tdiv N n)
    - IntTDivLeftExpr n N (if e := Int.tdiv n N)
    - IntTModLeftExpr N n (if e := Int.tmod N n)
    - IntTModRightExpr n N (if e := Int.tmod n N)
    - IntEDivLeftExpr N n (if e := Int.ediv N n)
    - IntEDivLeftExpr n N (if e := Int.ediv n N)
    - IntEModLeftExpr N n (if e := Int.emod N n)
    - IntEModRightExpr n N (if e := Int.emod n N)
    - IntFDivLeftExpr N n (if e := Int.fdiv N n)
    - IntFDivLeftExpr n N (if e := Int.fdiv n N)
    - IntFModLeftExpr N n (if e := Int.fmod N n)
    - IntFModRightExpr n N (if e := Int.fmod n N)
    - IntNegAddExpr N n (if e := Int.neg (Int.add N n))

    Return `none` when e is not a full applied Int binary operator.
    Assume that operands have already been reordered for commutative operators.
-/
def toIntCstOpExpr? (e: Expr) : Option IntCstOpInfo := do
 match intNeg? e with
 | some op =>
    match intAdd? op with
    | some (op1, op2) =>
         match (isIntValue? op1) with
         | some n => some (IntCstOpInfo.IntNegAddExpr n op2)
         | _ => none
    | _ => none
 | none =>
    match binOp? e with
    | some (f, op1, op2) =>
       match f, (isIntValue? op1), (isIntValue? op2) with
       | Expr.const ``Int.add _, some n, _ => some (IntCstOpInfo.IntAddExpr n op2)
       | Expr.const ``Int.mul _, some n, _ => some (IntCstOpInfo.IntMulExpr n op2)
       | Expr.const ``Int.tdiv _, some n, _ => some (IntCstOpInfo.IntTDivLeftExpr n op2)
       | Expr.const ``Int.tdiv _, _, some n => some (IntCstOpInfo.IntTDivRightExpr op1 n)
       | Expr.const ``Int.tmod _, some n, _ => some (IntCstOpInfo.IntTModLeftExpr n op2)
       | Expr.const ``Int.tmod _, _, some n => some (IntCstOpInfo.IntTModRightExpr op1 n)
       | Expr.const ``Int.ediv _, some n, _ => some (IntCstOpInfo.IntEDivLeftExpr n op2)
       | Expr.const ``Int.ediv _, _, some n => some (IntCstOpInfo.IntEDivRightExpr op1 n)
       | Expr.const ``Int.emod _, some n, _ => some (IntCstOpInfo.IntEModLeftExpr n op2)
       | Expr.const ``Int.emod _, _, some n => some (IntCstOpInfo.IntEModRightExpr op1 n)
       | Expr.const ``Int.fdiv _, some n, _ => some (IntCstOpInfo.IntFDivLeftExpr n op2)
       | Expr.const ``Int.fdiv _, _, some n => some (IntCstOpInfo.IntFDivRightExpr op1 n)
       | Expr.const ``Int.fmod _, some n, _ => some (IntCstOpInfo.IntFModLeftExpr n op2)
       | Expr.const ``Int.fmod _, _, some n => some (IntCstOpInfo.IntFModRightExpr op1 n)
       | _, _, _ => none
    | none => none

@[always_inline, inline]
def swapOnCond (cond : Bool) (args : Array Expr) : Array Expr :=
  if cond then args.swapIfInBounds 0 1 else args

@[always_inline, inline]
private def reorderCommon (e1 : Expr) (e2 : Expr) : Expr × Expr :=
 if (isTaggedRecursiveCall e1) && !(isTaggedRecursiveCall e2) then (e2, e1)
 else if e2.lt e1 then (e2, e1)
 else (e1, e2)

/-- Reorder operands for commutative Bool operators as follows:
     - #[``false, _] ===> args
     - #[e,``false] ===> #[``false, e]
     - #[``true, _] ===> args
     - #[e ``true] ===> #[``true, e]
     - #[fvar id1, fvar id2] ===> #[fvar id2, fvar id1] (if id2.name < id1.name)
     - #[fvar _, _] ===> args
     - #[e, fvar id] ===> #[fvar id, e]
     - #[e1, e2] ===> #[e2, e1] (if isTaggedRecursiveCall e1 ∧ ¬ (isTaggedRecursiveCall e2))
     - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
     - #[not e, e] ===> #[e, not e]
     - #[e1, e2] ===> args
-/
def reorderBoolOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  if args.size != 2 then throwEnvError "reorderBoolOp: two arguments expected"
  let e1 := args[0]!
  let e2 := args[1]!
  match e1, e2 with
  | Expr.const ``false _, _ => return args
  | _, Expr.const ``false _ => return (args.swapIfInBounds 0 1)
  | Expr.const ``true _, _ => return args
  | _, Expr.const ``true _ => return (args.swapIfInBounds 0 1)
  | Expr.fvar _, Expr.fvar _ => return (swapOnCond (e2.lt e1) args)
  | Expr.fvar _, _ => return args
  | _, Expr.fvar _ => return (args.swapIfInBounds 0 1)
  | _, _ =>
    let (e1', e2') := reorderCommon e1 e2
    if (← isBoolNotExprOf e1' e2') then return #[e2', e1']
    else return #[e1', e2']

/-- Reorder operands for commutative Prop operators as follows:
     - #[``False, _] ===> args
     - #[e,``False] ===> #[``False, e]
     - #[True, _] ===> args
     - #[e ``True] ===> #[``True, e]
     - #[fvar id1, fvar id2] ===> #[fvar id2, fvar id1] (if id2.name < id1.name)
     - #[fvar _, _] ===> args
     - #[e, fvar _] ===> #[fvar _, e]
     - #[¬ e, e] ===> #[e, ¬ e]
     - #[false = c, true = c] ===> #[true = c, false = c]
     - #[e1 -> e2, e1] ===> #[e1, e1 -> e2]
     - #[e1, e2] ===> #[e2, e1] (if isTaggedRecursiveCall e1 ∧ ¬ (isTaggedRecursiveCall e2))
     - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
     - #[e1, e2] ===> args
-/
def reorderPropOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  if args.size != 2 then throwEnvError "reorderPropOp: two arguments expected"
  let e1 := args[0]!
  let e2 := args[1]!
  match e1, e2 with
  | Expr.const ``False _, _ => return args
  | _, Expr.const ``False _ => return (args.swapIfInBounds 0 1)
  | Expr.const ``True _, _ => return args
  | _, Expr.const ``True _ => return (args.swapIfInBounds 0 1)
  | Expr.fvar _, Expr.fvar _ => return (swapOnCond (e2.lt e1) args)
  | Expr.fvar _, _ => return args
  | _, Expr.fvar _ => return (args.swapIfInBounds 0 1)
  | _, _ =>
     let (e1', e2') := reorderCommon e1 e2
     if (← isNotExprOf e1' e2') then return #[e2', e1']
     if (← isNegBoolEqOf e1' e2') then return #[e2', e1']
     if e1'.isForall && !e2'.isForall then return #[e2', e1']
     return #[e1', e2']

/-- Reorder operands for `Eq` operators by applying `reorderPropOp` first and followed by
    the rules:
     - #[Expr.lit _, _] ===> args
     - #[e, Expr.lit l] ===> #[Expr.lit l, e]
     - #[e1, e2] ===> args (if isConstructor e1) -- already ordered by reorderPropOp
     - #[e1, e2] ===> #[e2, e1] (if isConstructor e2)
     - #[e1, e2] ===> args

    An error is triggered when args.size ≠ 2.
    NOTE: Precedence is applied according to the order in which the rules have been specified.
-/
def reorderEq (args : Array Expr) : TranslateEnvT (Array Expr) := do
 let args' ← reorderPropOp args
 let e1 := args'[0]!
 let e2 := args'[1]!
 match e1, e2 with
 | Expr.lit _, _ => return args'
 | _, Expr.lit _ => return (args'.swapIfInBounds 0 1)
 | _, _ =>
   if (← isConstructor e1) then return args'
   if (← isConstructor e2) then return (args'.swapIfInBounds 0 1)
   if (← isBoolNotExprOf e1 e2) then return (args'.swapIfInBounds 0 1)
   return args'

/-- Reorder operands for commutative `Int` operators as follows:
    - #[N1, N2] ===> args
    - #[N, e] ===> args
    - #[e, N] ===> #[N, e]
    - #[fvar id1, fvar id2] ===> #[fvar id2, fvar id1] (if id2.name < id1.name)
    - #[fvar _, _] ===> args
    - #[e, fvar _] ===> #[fvar _, e]
    - #[(Nat.sub x y), (Nat.add p q)] ===> #[Nat.add p q, Nat.sub x y]
    - #[(Nat.pow x y), e] ===> #[e, Nat.pow x y] if ¬ (isNatPowExpr e)
    - #[e1, e2] ===> #[e2, e1] (if isTaggedRecursiveCall e1 ∧ ¬ (isTaggedRecursiveCall e2))
    - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
    - #[e1, e2] ===> args
-/
def reorderNatOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  if args.size != 2 then throwEnvError "reorderNatOp: two arguments expected"
  let e1 := args[0]!
  let e2 := args[1]!
  match isNatValue e1, isNatValue e2 with
  | true, _ => return args
  | _, true => return (args.swapIfInBounds 0 1)
  | _, _ =>
    match e1, e2 with
    | Expr.fvar _, Expr.fvar _ => return (swapOnCond (e2.lt e1) args)
    | Expr.fvar _, _ => return args
    | _, Expr.fvar _ => return (args.swapIfInBounds 0 1)
    | _, _ =>
      let (e1', e2') := reorderCommon e1 e2
      if (isNatSubExpr e1' && isNatAddExpr e2') then return #[e2', e1']
      if (isNatPowExpr e1' && !isNatPowExpr e2') then return #[e2', e1']
      return #[e1', e2']

-- set_option trace.compiler.ir.result true
/-- Reorder operands for commutative `Int` operators as follows:
    - #[N1, N2] ===> args
    - #[N, e] ===> args
    - #[e, N] ===> #[N, e]
    - #[fvar id1, fvar id2] ===> #[fvar id2, fvar id1] (if id2.name < id1.name)
    - #[fvar _, _] ===> args
    - #[e, fvar _] ===> #[fvar _, e]
    - #[Int.neg x, x] ===> #[x, Int.neg x]
    - #[e1, e2] ===> #[e2, e1] (if isTaggedRecursiveCall e1 ∧ ¬ (isTaggedRecursiveCall e2))
    - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
    - #[e1, e2] ===> args
-/
def reorderIntOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  if args.size != 2 then throwEnvError "reorderIntOp: two arguments expected"
  let e1 := args[0]!
  let e2 := args[1]!
  match isIntValue e1, isIntValue e2 with
  | true, _ => return args
  | _, true => return (args.swapIfInBounds 0 1)
  | _, _ =>
    match e1, e2 with
    | Expr.fvar _, Expr.fvar _ => return swapOnCond (e2.lt e1) args
    | Expr.fvar _, _ => return args
    | _, Expr.fvar _ => return (args.swapIfInBounds 0 1)
    | _, _ =>
      let (e1', e2') := reorderCommon e1 e2
      if (← isIntNegExprOf e1' e2') then return (args.set! 0 e2').set! 1 e1'
      return (args.set! 0 e1').set! 1 e2'

/-- Return `true` if `e` corresponds t a casesOn function. -/
def isCasesOnRec (e : Expr) : TranslateEnvT Bool := do
  match e with
  | Expr.const n _ => return isCasesOnRecursor (← getEnv) n
  | _ => return false

/-- Return `true` if `e` corresponds to a match or casesOn function. -/
def isMatchExpr (e : Expr) : TranslateEnvT Bool := do
  match e with
  | Expr.const n l => Option.isSome <$> getMatcherRecInfo? n l
  | _ => return false

/- Return the function definition for `f` whenever `f` corresponds to:
   - a lambda expression
   - a defined function (recursive or not).
   Otherwise `none`.
   Assumes that `f` cannot be one of the following:
     - an instance class;
     - a match function;
     - a class constraint.
-/
def getFunBodyAux? (f : Expr) : TranslateEnvT (Option Expr) := do
  match f with
  | Expr.lam .. => return f
  | Expr.const n l =>
      if (← isRecursiveFun n)
      then
        let some eqThm ← getUnfoldEqnFor? n
          | throwEnvError "getFunBody: equation theorem expected for {n}"
        forallTelescope ((← getConstEnvInfo eqThm).type) fun xs eqn => do
          let some (_, _, fbody) := eq? eqn
            | throwEnvError "getFunBody: equation expected but got {reprStr eqn}"
          let auxApp ← mkLambdaFVars xs fbody
          let cinfo ← getConstEnvInfo n
          return auxApp.instantiateLevelParams cinfo.levelParams l
      else
        if let cInfo@(ConstantInfo.defnInfo _) ← getConstEnvInfo n
        then instantiateValueLevelParams cInfo l
        else return none

  | Expr.proj .. => reduceProj? f  -- case when f is a function defined in a class instance
  | _ => return none

/-- Return `true` if the given type expression `t` (e.g., obtained via `inferType`)
    satisfy the following:
      - ¬ isProp t
      - `t :=  α₁ → ... → αₙ`
-/
def isFunType (t : Expr) : TranslateEnvT Bool := do
  if (← isPropEnv t) then return false
  else if t.isForall then return true
  else match autoParam? t with  -- considering case where function is wrapped in an autoParam arg
       | some (t', _tactic) => return t'.isForall
       | _ => return false


/-- Determine if `e` is an `implies` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
def propImplies? (e : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
 match e with
 | Expr.forallE _ t b _ =>
     if b.hasLooseBVars then return none
     if (← isPropEnv b) then return some (t, b)
     else return none
 | _ => return none

/-- Same as getFunBodyAux? but cache result -/
@[always_inline, inline]
def getFunBody (f : Expr) : TranslateEnvT (Option Expr) := do
  match (← get).optEnv.memCache.getFunBodyCache.get? f with
  | some m => return m
  | none =>
       let body ← getFunBodyAux? f
       modify (fun env => { env with
                                optEnv.memCache.getFunBodyCache :=
                                env.optEnv.memCache.getFunBodyCache.insert f body })
       return body


/-- Return `true` if `e` corresponds to an undefined type class function application, s.t.:
      - `e := app (Expr.proj c _ _) ...`; and
      - `c` is the name of a type class in the given environment; and
      - `Expr.proj c _ _` cannot be reduced.
-/
def isUndefinedClassFunApp (e : Expr) : TranslateEnvT Bool := do
  match e.getAppFn' with
  | p@(Expr.proj c _ _) => return ((← reduceProj? p).isNone && (← isClassConstraint c))
  | _ => return false

/-- Return `true` only when `e := Expr.const n l` and one of the following condition is satisfied:
     - `n := namedPattern`; or
     - `n` is a class instance; or
     - `n` is a match expression; or
     - `n` is a class constraint; or
     - `n` is an inductive datatype ∧ n ∉ opaqueFuns;
-/
def isNotFun (e : Expr) : TranslateEnvT Bool := do
 let Expr.const n l := e | return false
 if n == ``namedPattern then return true
 if (← isInstanceClass n) then return true
 if (← isMatchExpr e) then return true
 if (← isClassConstraint n) then return true
 if opaqueFuns.contains n then return false -- consider Eq/And/Or case
 isInductiveType n l



/-- Return `true` only when `e := Expr.const n l` and one of the following condition is satisfied:
     - `n` is not tagged as an opaque definition when flag `opaqueCheck` is set to true;
     - `n` is not a recursive function when flag `recFunCheck` is set to `true`;
     - `n` is a class instance;
     - `n` is an inductive datatype;
     - `n := namedPattern`;
     - `n` is not a match expression; or
     - `n` is not a class constraint.
-/
def isNotFoldable
  (e : Expr) (args : Array Expr) : TranslateEnvT Bool := do
  match e with
  | Expr.const n _ =>
      if (← isRecursiveFun n) then return true
      else if args.size == 0 && opaqueFuns.contains n then return true
      else if (← (pure (args.size != 0)) <&&> (isOpaqueFun n args)) then return true
      else isNotFun e
  | _ => return false


/-- Unfold fuction `f` w.r.t. the effective parameters `args` only when:
     - f is not a constructor
     - f is not tagged as an opaque definition
     - f is not a recursive function
     - f is not a class constraint
     - f is not an undefined type class function
     - f is not a match application
-/
def getUnfoldFunDef? (f: Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if (← isNotFoldable f args) then return none
 match ← getFunBody f with
 | some fbody =>
    let reduced := Expr.beta fbody args
    if (← isUndefinedClassFunApp reduced)
    then return none
    else
      -- check if reduced application is an instance class function
      let f' := reduced.getAppFn'
      if Expr.isProj f' then
        match ← getFunBody f' with
        | some fbody' => return Expr.beta fbody' reduced.getAppArgs
        | none => return reduced -- structure projection case
      else return reduced
 | none => return none


/-- Unfold an opaque relation function up to its base definition
    Assume that `f` corresponds to an opaque relation function on first call.
-/
partial def unfoldOpaqueFunDef (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  match ← getFunBody f with
  | none => return none -- case when class function is undefined but has the expected constraints (e.g., LawfulBEq)
  | some fbody =>
     let reduced := Expr.beta fbody args
     let f' := reduced.getAppFn'
     let args' := reduced.getAppArgs
     if (← isFoldable f' args')
     then unfoldOpaqueFunDef f' args'
     else return reduced

  where
    isFoldable (f : Expr) (args : Array Expr) : TranslateEnvT Bool := do
      match f with
      | Expr.const .. => return !(← isNotFoldable f args)
      | Expr.lam ..
      | Expr.proj .. => return true
      | _ => return false

/-- Return `true` when the following conditions are satisfied:
      - `f` is an opaque relation function
      - `f` has a sort parameter not in `relationalCompatibleTypes`
      - `f` is an alias to a well-founded recursive definition.
-/
def isOpaqueRecFun (f : Expr) (args : Array Expr) : TranslateEnvT Bool := do
  match f with
  | Expr.const n _ =>
      if h : 2 ≤ args.size then
        -- check for recursive definition for opaque relational function
        if (← (pure $ !(isCompatibleRelationalType args[0])) <&&> isOpaqueRelational n args) then
          let some auxDef ← unfoldOpaqueFunDef f args | return false
          let Expr.const n' _  := (getLambdaBody auxDef).getAppFn' | return false
          return (← isRecursiveFun n')
      return false
  | _ => return false


/-- Trigger an error if e contains at least one theorem with sorry demonstration. -/
partial def hasSorryTheorem (e : Expr) (msg : MessageData) : TranslateEnvT Unit :=
  Expr.forEach e findSorry

 where
  findSorry (e : Expr) : TranslateEnvT Unit := do
    match e with
    | Expr.const n _ =>
        if n == ``sorryAx then throwEnvError msg
        else if let ConstantInfo.thmInfo info ← getConstEnvInfo n then hasSorryTheorem (info.value) msg
        else return ()
    | _ => return ()

/-- Given `pType := λ α₁ → .. → λ αₙ → t` returns `λ α₁ → .. → λ αₙ → eType`
    This function is expected to be used only when updating a match return type
-/
def updateMatchReturnType (eType : Expr) (pType : Expr) : TranslateEnvT Expr := do
  lambdaTelescope pType fun params _body => mkLambdaFVars params eType

end Solver.Optimize
