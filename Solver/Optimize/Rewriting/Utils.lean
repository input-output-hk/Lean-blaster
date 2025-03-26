import Lean
import Solver.Optimize.Env

open Lean Meta Declaration

namespace Solver.Optimize


/-- Return `true` if c corresponds to a constructor. -/
def isCtorName (c : Name) : MetaM Bool := do  pure (← getConstInfo c).isCtor

/-- Return `true` if e corresponds to a constructor expression. -/
def isCtorExpr (e : Expr) : MetaM Bool := do
 let Expr.const n _ := e | return false
 return (← getConstInfo n).isCtor

/-- Return `true` if `n` is a function tagged with the `partial` keyword. -/
def isPartialDef (n : Name) : MetaM Bool := do
  if (← isRecursiveFun n <||> isInstance n) then return false
  return ((← getEnv).find? (Compiler.mkUnsafeRecName n)).isSome

/-- Return `true` if `n` corresponds to an unsafe definition
    (e.g, partial recursive function, partial inductive predicate, etc). -/
def isUnsafeDef (n : Name) : MetaM Bool := do
 return (← getConstInfo n).isUnsafe

/-- Return `true` if e corresponds to an enumerator constructor (i.e., constructor without any parameters).
-/
def isEnumConst (e : Expr) : MetaM Bool := do
 let Expr.const n _ := e | return false
 let ConstantInfo.ctorInfo info ← getConstInfo n | return false
 return (info.numFields == 0 && info.numParams == 0 && !info.type.isProp)

/-- Return `true` if e corresponds to a nullary constructor or a fully applied parametric constructor.
-/
def isFullyAppliedConst (e : Expr) : MetaM Bool := do
 match e.getAppFn' with
 | Expr.const n _ =>
    let ConstantInfo.ctorInfo info ← getConstInfo n | return false
    -- should be fully applied
    -- numFields corresponds to the constructor parameters
    -- numParams corresponds to the Inductive type parameters
    return (e.getAppArgs.size == info.numFields + info.numParams && !info.type.isProp)
 | _ => return false

/-- Return `true` if e corresponds to a constructor that may contain free or bounded variables. -/
def isConstructor (e : Expr) : MetaM Bool := isEnumConst e <||> (pure e.isLit) <||> isFullyAppliedConst e

/-- Return `true` if e contains free / bounded variables. -/
def hasVars (e : Expr) : Bool := e.hasFVar || e.hasLooseBVars


/-- Return `true` if `v` occurs at least once in `e`. -/
def fVarInExpr (v : FVarId) (e : Expr) : Bool :=
 if e.hasFVar
 then e.containsFVar v
 else false

/-- Return `true` if e corresponds to a constructor applied to only constant values (e.g., no free or bounded variables). -/
def isConstant (e : Expr) : MetaM Bool :=
  isConstructor e <&&> (pure !(hasVars e))

/-- Return `true` if e corresponds to an implication, i.e., a → b,
    with Type(a) = Prop and Type(b) = Prop.
-/
def isImplies (e : Expr) : MetaM Bool :=
 match e with
 | Expr.forallE _ t b _ =>
     if !b.hasLooseBVars
     then isProp t
     else return false
 | _ => return true


/-- If the `e` is a sequence of lambda `fun x₁ => fun x₂ => ... fun xₙ => b`,
    return `b`. Otherwise return `e`.
-/
def getLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getLambdaBody b
 | _ => e

/-- Return `true` if `f` corresponds to a class function. -/
def isClassFun (f : Expr) : MetaM Bool := do
 match f with
 | Expr.const n _ =>
    let ConstantInfo.defnInfo d ← getConstInfo n | return false
    let Expr.proj c _ _ := (getLambdaBody d.value).getAppFn' | return false
    return (isClass (← getEnv) c)
 | Expr.proj c _ _ => return (isClass (← getEnv) c)
 | _ => return false

/-- Return `true` if `c` corresponds to a nullary constructor. -/
def isNullaryCtor (c : Name) : MetaM Bool := do
  match (← getConstInfo c) with
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
 if (← isProp t) then return false
 match t.getAppFn' with
 | Expr.const n _ =>
    if isClass (← getEnv) n then return true -- break if class constraint
    match (← getConstInfo n) with
    | ConstantInfo.inductInfo indVal =>
       for ctorName in indVal.ctors do
         if (← isNullaryCtor ctorName) then return true -- inductive type has at least one nullary constructor
       -- check if InHabited instance exists for t
       hasInhabitedInstance t
    | _ => isType t
 | _ => isType t


/-- Determine if `e` is a boolean `not` expression and return it's corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolNot? (e: Expr) : Option Expr := e.app1? ``not

/-- Determine if `e` is a boolean `and` expression and return it's corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolAnd? (e: Expr) : Option (Expr × Expr) := e.app2? ``and

/-- Determine if `e` is a boolean `or` expression and return it's corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolOr? (e: Expr) : Option (Expr × Expr) := e.app2? ``or

/-- Determine if `e` is a `Bool` literal expression b and return `some b`.
    Otherwise `none`
-/
def isBoolValue? (e : Expr) : Option Bool :=
 match e with
 | Expr.const ``true _ => some true
 | Expr.const ``false _ => some false
 | _ => none

/-- Determine if `e` is an boolean `==` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def beq? (e : Expr) : Option (Expr × Expr × Expr × Expr) := e.app4? ``BEq.beq


/-- Determine if `e` is an `Not` expression and return it's corresponding argument.
    Otherwise return `none`.
-/
@[inline] def propNot? (e : Expr) : Option Expr := e.not?

/-- Determine if `e` is an `And` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def propAnd? (e : Expr) : Option (Expr × Expr) := e.and?

/-- Determine if `e` is an `Or` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def propOr? (e : Expr) : Option (Expr × Expr) := e.app2? ``Or

/-- Return `! e` when `b = false`. Otherwise return `e`.
-/
def toBoolNotExpr? (b : Bool) (e : Expr) : TranslateEnvT Expr := do
  if b then return e
  mkExpr (mkApp (← mkBoolNotOp) e)

/-- Return `true` when `e1 := ¬ ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool := do
  let some op := propNot? e1 | return false
  exprEq e2 op

/-- Determine if `e` is an `implies` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
def propImplies? (e : Expr) : MetaM (Option (Expr × Expr)) := do
 match e with
 | Expr.forallE _ t b _ =>
     if b.hasLooseBVars then return none
     if (← isProp t) then return some (t, b)
     return none
 | _ => return none

/-- Return `true` when `e1 := not ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isBoolNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool := do
  let some op := boolNot? e1 | return false
  exprEq e2 op

/-- Return `true` when `e1 := false = c ∧ e2 := true = c`. -/
def isNegBoolEqOf (e1: Expr) (e2: Expr) : MetaM Bool := do
 match e1.eq?, e2.eq? with
 | some (_, e1_op1, e1_op2), some (_, e2_op1, e2_op2) =>
     match e1_op1, e2_op1 with
      | Expr.const ``false _, Expr.const ``true _ => exprEq e1_op2 e2_op2
      | _, _ => return false
 | _, _ => return false

/-- Return `true` if the given expression is of the form `const ``Bool`. -/
def isBoolType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Bool _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Nat`. -/
def isNatType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Nat _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Int`. -/
def isIntType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Int _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``String`. -/
def isStringType (e : Expr) : Bool :=
  match e with
  | Expr.const ``String _ => true
  | _ => false

/-- Return `true` if the given type expression `t` (e.g., obtained via `inferType`)
    satisfy the following:
      - ¬ isProp t
      - `t :=  α₁ → ... → αₙ`
-/
def isFunType (t : Expr) : MetaM Bool := do
  if (← isProp t) then return false
  match t with
  | Expr.forallE .. => return true
  | _ => return false

/-- Determine if `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
    and return `some n` as result. Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
def isNatValue? (e : Expr) : Option Nat :=
  match e with
  | Expr.lit (Literal.natVal n) => some n
  | _ => none

/-- Determine if `e` is a `String` literal expression `Expr.lit (Literal.strVal s)`
    and return `some s` as result. Otherwise return `none`.
-/
def isStrValue? (e : Expr) : Option String :=
  match e with
  | Expr.lit (Literal.strVal s) => some s
  | _ => none

/-- Determine if `e` is a `UInt32` literal expression `UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some n` only when n < UInt32.size.
    Otherwise return `none`
-/
def isUInt32Value? (e : Expr) : Option Nat :=
  match e.app1? ``UInt32.mk with
  | some fn1 =>
     match fn1.app2? ``BitVec.ofFin with
     | some (_, fn2) =>
        match fn2.app3? ``Fin.mk with
        | some (Expr.lit (Literal.natVal s), Expr.lit (Literal.natVal n), _) =>
          if s != UInt32.size || Nat.ble UInt32.size n
          then none
          else some n
        | _ => none
     | _ => none
  | _ => none


/-- Determine if `e` is a `Char` literal expression `Char.mk (UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some Char.ofNat n)` only when `Nat.isValidChar n`.
    Otherwise return `none`
-/
def isCharValue? (e : Expr) : Option Char :=
  match e.app2? ``Char.mk with
  | some (ui, _) =>
      match isUInt32Value? ui with
      | some n => if Nat.isValidChar n then some (Char.ofNat n) else none
      | _ => none
  | _ => none


/-- Return `true` if `e := Nat.add e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.add expression.
-/
def isNatAddExpr (e : Expr) : Bool := e.isAppOfArity ``Nat.add 2

/-- Return `true` if `e := Nat.sub e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.sub expression.
-/
def isNatSubExpr (e: Expr) : Bool := e.isAppOfArity ``Nat.sub 2

/-- Return `true` if `e := Nat.pow e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.pow expression.
-/
def isNatPowExpr (e : Expr) : Bool := e.isAppOfArity ``Nat.pow 2

/-- Determine if `e` is a `Nat.mul` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natMul? (e: Expr) : Option (Expr × Expr) := e.app2? ``Nat.mul

/-- Determine if `e` is a `Nat.add` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natAdd? (e: Expr) : Option (Expr × Expr) := e.app2? ``Nat.add

/-- Determine if `e` is a `Nat.sub` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natSub? (e: Expr) : Option (Expr × Expr) := e.app2? ``Nat.sub

/-- Determine if `e` is a `Nat.pow` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natPow? (e: Expr) : Option (Expr × Expr) := e.app2? ``Nat.pow

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


/-- Return `true` if `e` is a `const` application of arity `n`. -/
def isFunAppOfArity : Expr → Nat → Bool
  | Expr.const .., 0 => true
  | Expr.app f _, a+1 => isFunAppOfArity f a
  | _, _   => false

/-- Return `some (op1, op2)` when `e` is a binary operator. Otherwise `none`. -/
@[inline] def binOp? (e : Expr) : Option (Expr × Expr) :=
  if isFunAppOfArity e 2
  then some (e.appFn!.appArg!, e.appArg!)
  else none

/-- Return `some op` is e is a unary operator. Otherwise `none`. -/
@[inline] def unaryOp? (e : Expr) : Option Expr :=
  if isFunAppOfArity e 1
  then some (e.appArg!)
  else none

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
 | some (op1, op2) =>
    match e.getAppFn, (isNatValue? op1), (isNatValue? op2) with
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

/-- Determine if `e` is an Int.neg expression and return it's corresponding argument.
    Otherwise return `none`.
-/
@[inline] def intNeg? (e : Expr) : Option Expr := e.app1? ``Int.neg

/-- Determine if `e` is a `Decidable.decide` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def decide? (e : Expr) : Option (Expr × Expr) := e.app2? ``Decidable.decide


/-- Determine if `e := fName x₁ ... xₙ` and return `some (x₁, ..., xₙ)`.
    Otherwise return `none`
-/
@[inline] def app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appFn!.appArg!,
          e.appFn!.appFn!.appFn!.appArg!,
          e.appFn!.appFn!.appArg!,
          e.appFn!.appArg!,
          e.appArg!)
  else
    none

/-- Determine if `e` is an `ite` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def ite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := app5? e ``ite

/-- Determine if `e` is an `dite` expression and return it's corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def dite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := app5? e ``dite

/-- Return `true` when `e1 := -ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isIntNegExprOf (e1: Expr) (e2 : Expr) : MetaM Bool := do
  if let some op := intNeg? e1 then return (← exprEq e2 op)
  return false

/-- Determine if `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
    Return either `some (Int.ofNat n)` or `some (Int.negSucc n)` as result.
    Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
def isIntValue? (e : Expr) : Option Int :=
  match unaryOp? e with
  | some op =>
    match isNatValue? op with
    | some n =>
        match e.getAppFn with
        | Expr.const ``Int.ofNat _ => Int.ofNat n
        | Expr.const ``Int.negSucc _ => Int.negSucc n
        | _ => none
    | none => none
  | _ => none

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
partial def toIntCstOpExpr? (e: Expr) : Option IntCstOpInfo := do
 match intNeg? e with
 | some op =>
    match toIntCstOpExpr? op with
    | IntCstOpInfo.IntAddExpr n op2 => some (IntCstOpInfo.IntNegAddExpr n op2)
    | _ => none
 | none =>
    match binOp? e with
    | some (op1, op2) =>
       match e.getAppFn, (isIntValue? op1), (isIntValue? op2) with
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

/-- Reorders operands `args` for commutative operator to normalize expression, such that:
     - #[``False, _] ===> args
     - #[e,``False] ===> #[``False, e]
     - #[True, _] ===> args
     - #[e ``True] ===> #[``True, e]
     - #[Expr.lit _, _] ===> args
     - #[e, Expr.lit l] ===> #[Expr.lit l, e]
     - #[e1, e2] ===> #[e2, e1] (if isConstructor e1 ∧ isConstructor e2 ∧ isConstant e1 ∧ isConstant e2 ∧ e2 < e1)
     - #[e1, e2] ===> #[e2, e1] (if isConstructor e1 ∧ isConstructor e2 ∧ ¬ (isConstant e1) ∧ isConstant e2)
     - #[e1, e2] ===> args      (if isConstructor e1 ∧ isConstructor e2 ∧ isConstant e1 ∧ ¬ (isConstant e2))
     - #[e1, e2] ===> #[e2, e1] (if isConstructor e1 ∧ isConstructor e2 ∧ ¬ (isConstant e1) ∧ ¬ (isConstant e2) ∧ e2 < e1)
     - #[e1, e2] ===> #[e2, e1] (if ¬ (isConstructor e1) ∧ isConstructor e2)
     - #[e1, e2] ===> args (if isConstructor e1 ∧ ¬ (isConstructor e2))
     - #[bvar n1, bvar n2] ===> #[bvar n2, bvar n1] (if n2 < n1)
     - #[fvar id1, fvar id2] ===> #[fvar id2, fvar id1] (if id2.name < id1.name)
     - #[mvar id1, mvar id2] ===> #[mvar id2, mvar id1] (if id2.name < id1.name)
     - #[bvar _, _] ===> args
     - #[e, bvar b] ===> #[bvar b, e]
     - #[fvar _, _] ===> args
     - #[e, fvar id] ===> #[fvar id, e]
     - #[mvar _, _] ===> args
     - #[e, mvar id] ===> #[mvar id, e]
     - #[e1, e2] ===> #[e2, e1] (if isTaggedRecursiveCall e1 ∧ ¬ (isTaggedRecursiveCall e2))
     - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
     - #[e1, e2] ===> args

    An error is triggered when args.size ≠ 2.
    NOTE: Precedence is applied according to the order in which the rules have been specified.
-/
def reorderArgs (args : Array Expr) : TranslateEnvT (Array Expr) := do
 if args.size != 2 then throwEnvError "reorderArgs: two arguments expected"
 let e1 := args[0]!
 let e2 := args[1]!
 match e1, e2 with
 | Expr.const ``False _, _ => pure args
 | _, Expr.const ``False _ => pure (args.swapIfInBounds 0 1)
 | Expr.const ``True _, _ => pure args
 | _, Expr.const ``True _ => pure (args.swapIfInBounds 0 1)
 | Expr.lit _, _ => pure args
 | _, Expr.lit _ => pure (args.swapIfInBounds 0 1)
 | _, _ =>
   match (← isConstructor e1), (← isConstructor e2) with
   | true, true =>
      match hasVars e1, hasVars e2 with
      | false, false | true, true => pure (swapOnCond (e2.lt e1))
      | false, true => pure args
      | true, false => pure (args.swapIfInBounds 0 1)
   | false, true => pure (args.swapIfInBounds 0 1)
   | true, false => pure args
   | false, false =>
      match e1, e2 with
      | Expr.bvar n1, Expr.bvar n2 => pure (swapOnCond (n2 <= n1))
      | Expr.fvar id1, Expr.fvar id2 => pure (swapOnCond (id2.name.lt id1.name))
      | Expr.mvar id1, Expr.mvar id2 => pure (swapOnCond (id2.name.lt id1.name))
      | Expr.bvar _, _ => pure args
      | _, Expr.bvar _ => pure (args.swapIfInBounds 0 1)
      | Expr.fvar _, _ => pure args
      | _, Expr.fvar _ => pure (args.swapIfInBounds 0 1)
      | Expr.mvar _, _ => pure args
      | _, Expr.mvar _ => pure (args.swapIfInBounds 0 1)
      | _, _ =>
         if (isTaggedRecursiveCall e1) && !(isTaggedRecursiveCall e2) then return (args.swapIfInBounds 0 1)
         pure (swapOnCond (e2.lt e1))

 where
   swapOnCond (cond : Bool) : Array Expr :=
    if cond then args.swapIfInBounds 0 1 else args


/-- call `reorderArgs` but consider the following additional rule:
     - #[not e, e] ===> #[e, not e]
-/
def reorderBoolOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isBoolNotExprOf e1 e2) then return (args'.swapIfInBounds 0 1)
  return args'

/-- call `reorderBoolOp` but consider the following additional rule:
     - #[¬ e, e] ===> #[e, ¬ e]
     - #[false = c, true = c] ===> #[true = c, false = c]
-/
def reorderPropOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  let args' ← reorderBoolOp args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isNotExprOf e1 e2) then return ((args'.swapIfInBounds 0 1))
  if (← isNegBoolEqOf e1 e2) then return ((args'.swapIfInBounds 0 1))
  return args'

/-- call `reorderArgs` but consider the following additional rule:
    - #[(Nat.sub x y), (Nat.add p q)] ===> #[Nat.add p q, Nat.sub x y]
    - #[(Nat.pow x y), e] ===> #[e, Nat.pow x y] if ¬ (isNatPowExpr e)
-/
def reorderNatOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (isNatSubExpr e1 && isNatAddExpr e2) then return (args'.swapIfInBounds 0 1)
  if (isNatPowExpr e1 && !isNatPowExpr e2) then return (args'.swapIfInBounds 0 1)
  return args'


/-- call `reorderArgs` but consider the following additional rule:
    - #[Int.neg x, x] ===> #[x, Int.neg x]
-/
def reorderIntOp (args: Array Expr) : TranslateEnvT (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isIntNegExprOf e1 e2)
  then pure (args'.swapIfInBounds 0 1)
  else pure args'


/-- Same as the default `getMatcherInfo` in the Lean library but also handles casesOn recursor application. -/
def getMatcherRecInfo? (n : Name) (l : List Level) : MetaM (Option MatcherInfo) := do
 if let some r ← getMatcherInfo? n then return r
 if !(isCasesOnRecursor (← getEnv) n) then return none
 let indName := n.getPrefix
 let ConstantInfo.inductInfo info ← getConstInfo indName | return none
 let mut altNumParams := #[]
 for ctor in info.ctors do
   let ConstantInfo.ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
   altNumParams := altNumParams.push ctorInfo.numFields
 return some { numParams := info.numParams,
               numDiscrs := info.numIndices + 1,
               altNumParams,
               uElimPos? := if info.levelParams.length == l.length then none else some 0
               discrInfos := Array.mkArray (info.numIndices + 1) {}
             }

/-- Return `true` if `n` corresponds to a matcher expression name or a casesOn recursor application. -/
def isMatchExpr (n : Name) : MetaM Bool := do
  Option.isSome <$> getMatcherInfo? n <||> (pure $ isCasesOnRecursor (← getEnv) n)


/- Return the function definition for `f` whenever `f` corresponds to:
   - a lambda expression
   - a defined function (recursive or not).
   Otherwise `none`.
   Assumes that `f` cannot be one of the following:
     - an instance class;
     - a match function;
     - a class constraint.
-/
def getFunBody (f : Expr) : TranslateEnvT (Option Expr) := do
  match f with
  | Expr.lam .. => return f
  | Expr.const n l =>
      if (← isRecursiveFun n)
      then
        let some eqThm ← getUnfoldEqnFor? n
          | throwEnvError f!"getFunBody: equation theorem expected for {n}"
        forallTelescope ((← getConstInfo eqThm).type) fun xs eqn => do
          let some (_, _, fbody) := eqn.eq?
            | throwEnvError f!"getFunBody: equation expected but got {reprStr eqn}"
          let auxApp ← mkLambdaFVars xs fbody
          let cinfo ← getConstInfo n
          return auxApp.instantiateLevelParams cinfo.levelParams l
      else
        let cInfo@(ConstantInfo.defnInfo _) ← getConstInfo n | return none
        instantiateValueLevelParams cInfo l
  | Expr.proj .. => reduceProj? f  -- case when f is a function defined in a class instance
  | _ => return none

/-- Return `true` if `e` corresponds to an undefined type class function application, s.t.:
      - `e := app (Expr.proj c _ _) ...`; and
      - `c` is the name of a type class in the given environment; and
      - `Expr.proj c _ _` cannot be reduced.
-/
def isUndefinedClassFunApp (e : Expr) : MetaM Bool := do
  let p@(Expr.proj c _ _) := e.getAppFn' | return false
  return ((← reduceProj? p).isNone && (isClass (← getEnv) c))

/-- Return `true` only when `e := Expr.const n l` and one of the following condition is satisfied:
     - `n` is not tagged as an opaque definition when flag `opaqueCheck` is set to true;
     - `n` is not a recursive function when flag `recFunCheck` is set to `true`;
     - `n` is a class instance;
     - `n` is an inductive datatype;
     - `n := namedPattern`;
     - `n` is not a match expression; or
     - `n` is not a class constraint.
     Otherwise `false`.
-/
def isNotFoldable
  (e : Expr) (args : Array Expr)
  (opaqueCheck := true) (recFunCheck := true) : TranslateEnvT Bool := do
  let Expr.const n l := e | return false
  if recFunCheck && (← isRecursiveFun n) then return true
  unless !opaqueCheck do
    if args.size == 0 && opaqueFuns.contains n then return true
    if (← (pure (args.size != 0)) <&&> (isOpaqueFun n args)) then return true
  if n == ``namedPattern then return true
  (isInductiveType n l)
  <||> (isInstance n)
  <||>  (isMatchExpr n)
  <||> (isClassConstraint n)


/-- Unfold fuction `f` w.r.t. the effective parameters `args` only when:
     - f is not a constructor
     - f is not tagged as an opaque definition
     - f is not a recursive function
     - f is not a class constraint
     - f is not an undefined type class function
     - f is not a match application
-/
def getUnfoldFunDef? (f: Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 if (← isNotFoldable f args) then return none
 let some fbody ← getFunBody f | return none
 let reduced := Expr.beta fbody args
 if (← isUndefinedClassFunApp reduced) then return none
 -- check if reduced application is an instance class function
 let f' := reduced.getAppFn'
 if Expr.isProj f' then
   let some fbody' ← getFunBody f' | return reduced -- structure projection case
   return Expr.beta fbody' reduced.getAppArgs
 else return reduced


/-- Unfold an opaque relation function up to its base definition
    Assume that `f` corresponds to an opaque relation function on first call.
-/
partial def unfoldOpaqueFunDef (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let some fbody ← getFunBody f
   | return none -- case when class function is still undefined but has the expected constraints (e.g., LawfulBEq)
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
  let Expr.const n _ := f | return false
  if args.size ≥ 2 then
   -- check for recursive definition for opaque relational function
   if (← (pure $ !(isCompatibleRelationalType args[0]!)) <&&> isOpaqueRelational n args) then
     let some auxDef ← unfoldOpaqueFunDef f args | return false
     let Expr.const n' _  := (getLambdaBody auxDef).getAppFn' | return false
     return (← isRecursiveFun n')
  return false

/-- Given `e` of the form `forall (a₁ : A₁) ... (aₙ : Aₙ), B[a₁, ..., aₙ]`
    and `p₁ : A₁, ... pₘ : Aₙ`, return `B[p₁, ..., pₘ]`.
    An error is triggered when n ≠ m.
-/
partial def betaForAll (e : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let rec visit (i : Nat) (size : Nat) (e : Expr) : TranslateEnvT Expr := do
    if i < size then
       match e with
       | Expr.forallE _ _ b _ => visit (i + 1) size (b.instantiate1 args[i]!)
       | _ => throwEnvError "betaForAll: too many arguments !!!"
    else return e
  visit 0 args.size e

/-- Trigger an error if e contains at least one theorem with sorry demonstration. -/
partial def hasSorryTheorem (e : Expr) (msg : MessageData) : TranslateEnvT Unit :=
  Expr.forEach e findSorry

 where
  findSorry (e : Expr) : TranslateEnvT Unit := do
    let Expr.const n _ := e | return ()
    if n == ``sorryAx then throwEnvError msg
    let ConstantInfo.thmInfo info ← getConstInfo n | return ()
    hasSorryTheorem (info.value) msg

end Solver.Optimize
