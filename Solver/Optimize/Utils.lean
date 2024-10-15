import Lean
import Solver.Translate.Env

open Lean Meta Declaration

namespace Solver.Optimize

/-- Return `true` if `op1` and `op2` are physically equivalent, i.e., points to same memory address.
-/
@[inline] private unsafe def exprEqUnsafe (op1 : Expr) (op2 : Expr) : MetaM Bool :=
  pure (ptrEq op1 op2)

/-- Safe implementation of physically equivalence for Expr.
-/
@[implemented_by exprEqUnsafe]
def exprEq (op1 : Expr) (op2 : Expr) : MetaM Bool := isDefEqGuarded op1 op2


/-- list of operators that must not be unfolded, i.e., they will directly be
translated to their corresponding SMT counterpart.
-/
def opaqueFuns : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [
    -- structural equality
    ``Eq,
    -- DecidableEq constraint
    ``DecidableEq,
    -- Prop operators
    ``And,
    ``Or,
    ``Not,
    -- ite
    ``ite,
    -- dependent ite
    ``dite,
    -- existential quantifier
    ``Exists,
    -- Int operators
    ``Int.add, -- Int.sub is defined as m + (-n)
    ``Int.neg,
    ``Int.mul,
    ``Int.toNat,
    -- Division rounding towards zero
    ``Int.div,
    ``Int.mod,
    -- Division rounding towards negative infinity
    ``Int.fdiv,
    ``Int.fmod,
    -- Euclidean division (default one)
    ``Int.ediv,
    ``Int.emod,
    ``Int.pow,
    -- Relational operators
    ``LE.le, -- GE.ge a b is abbrev for LE.le b a
    ``LT.lt, -- Gt.gt a b is abbrev for LT.lt b a
    -- Bool operators
    ``and,
    ``or,
    ``not,
    -- Nat operators
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.pred,
    ``Nat.ble,
    ``Nat.blt,
    ``Nat.beq,
    ``Nat.pow,
  ]

/-- list of types for which the BEq instance is guaranteed to be reflexive, symmetric and transitive.
TODO: add other basic lean types (e.g., Char, etc)
-/
def beqCompatibleTypes : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [ ``Nat,
    ``Int,
    ``Bool,
    ``String
  ]

/-- Return `true` if function name is `BEq.beq` with a sort parameter in `beqCompatibletypes`.
In fact, we can't assume that `BEq.beq` will properly be defined for any user-defined types or
parametric inductive types (e.g., List, Option, etc). Indeed, the provided definition
may not satisfy refl, symm and trans.
-/
def isOpaqueBeq (f : Name) (args : Array Expr) : Bool :=
  if f == `BEq.beq && args.size > 0
  then
    match args[0]! with
    | Expr.const n _ => beqCompatibleTypes.contains n
    | _ => false
  else false

/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : Bool :=
  opaqueFuns.contains f || isOpaqueBeq f args

/-- Same as `isOpaqueFun` expect that `f` is an expression. -/
def isOpaqueFunExpr (f : Expr) (args: Array Expr) : Bool :=
  match f with
  | Expr.const n _ => isOpaqueFun n args
  | _ => false

/-- Return `true` if c corresponds to a constructor. -/
def isCtorName (c : Name) : MetaM Bool := do
  pure (← getConstInfo c).isCtor

/-- Return `true` if e corresponds to a constructor expression. -/
def isCtorExpr (e : Expr) : MetaM Bool := do
  match e with
  | Expr.const n _ =>
       if isRecFunInternal n
       then pure false
       else pure (← getConstInfo n).isCtor
  | _ => pure false

/-- Return `true` if e corresponds to an enumerator constructor (i.e., constructor without any parameters).
-/
def isEnumConst (e : Expr) : MetaM Bool := do
 match e with
 | Expr.const n _ =>
     if isRecFunInternal n
     then pure false
     else match (← getConstInfo n) with
           | ConstantInfo.ctorInfo info => pure (info.numFields == 0 && info.numParams == 0 && !info.type.isProp)
           | _ => pure false
 | _ => pure false

/-- Return `true` if e correponds to a fully applied parametric constructor.
-/
def isFullyAppliedConst (e : Expr) : MetaM Bool := do
 match e with
 | Expr.app .. =>
     -- parameteric constructor case
     Expr.withApp e fun f as => do
       match f with
       | Expr.const n _ =>
          if isRecFunInternal n
          then pure false
          else match (← getConstInfo n) with
                | ConstantInfo.ctorInfo info =>
                   -- should be fully applied
                   -- numFields corresponds to the constructor parameters
                   -- numParams corresponds to the Inductive type parameters
                   pure (as.size == info.numFields + info.numParams && !info.type.isProp)
                | _ => pure false
       | _ => pure false
 | _ => pure false

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
     then isProp t <&&> isProp b
     else return false
 | _ => return true


/-- If the `e` is a sequence of lambda `fun x₁ => fun x₂ => ... fun xₙ => b`,
    return `b`. Otherwise return `e`.
-/
def getLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getLambdaBody b
 | _ => e


/-- Return `true` if f corresponds to a class function. -/
def isClassFun (f : Expr) : MetaM Bool := do
 match f with
 | Expr.const n _ =>
    if isRecFunInternal n
    then return false
    else
      let ConstantInfo.defnInfo d ← getConstInfo n | return false
      match (getLambdaBody d.value).getAppFn with
      | Expr.proj c _ _ => return (isClass (← getEnv) c)
      | _ => return false
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
-/
def isSortOrInhabited (t : Expr) : TranslateEnvT Bool := do
 if (← isProp t) then return false
 match t.getAppFn with
 | Expr.const n _ =>
    match (← getConstInfo n) with
    | ConstantInfo.inductInfo indVal =>
       if isClass (← getEnv) n then return (← isType t) -- break if class constraint
       for ctorName in indVal.ctors do
         if (← isNullaryCtor ctorName) then
           return true -- inductive type has at least one nullary constructor
       -- check if InHabited instance exists for t
       hasInhabitedInstance t
    | _ => isType t
 | _ => isType t

/-- Return `true` when `e1 := ¬ ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool :=
  Expr.withApp e1 fun f as =>
    match f, as with
    | Expr.const ``Not _, #[op] => exprEq e2 op
    | _, _ => pure false

/-- Return `true` when `e1 := not ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isBoolNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool :=
  Expr.withApp e1 fun f as =>
    match f, as with
    | Expr.const ``not _, #[op] => exprEq e2 op
    | _, _ => pure false


/-- Determine if `e` is an Eq expression and return it's correponding arguments.
   Otherwise return `none`.
-/
def isEqExpr? (e: Expr) : Option (Expr × Array Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Eq _ => some (f, args)
      | _ => none
 | _ => none

/-- Determine if `e` is an BEq.beq expression and return it's correponding arguments.
   Otherwise return `none`.
-/
def isBEqExpr? (e: Expr) : Option (Expr × Array Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``BEq.beq _ => some (f, args)
      | _ => none
 | _ => none

/-- Return `true` when one of the following conditions is satisfied:
    - `e1 := true = c` ∧ `e2 := false = c`; or
    - `e1 := false = c` ∧ `e2 := true = c`; or
-/
def isNegBoolEqOf (e1: Expr) (e2: Expr) : MetaM Bool := do
 match isEqExpr? e1, isEqExpr? e2 with
 | some eq1, some eq2 =>
     let eq1_ops := eq1.2
     let eq2_ops := eq2.2
     match eq1_ops[1]!, eq2_ops[1]! with
     | Expr.const ``true _, Expr.const ``false _ |
       Expr.const ``false _, Expr.const ``true _ => exprEq eq1_ops[2]! eq2_ops[2]!
     | _, _ => return false
 | _, _ => return false

/-- Return `true` if the given expression is of the form `const ``Bool`.
-/
def isBoolType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Bool _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Nat`.
-/
def isNatType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Nat _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Int`.
-/
def isIntType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Int _ => true
  | _ => false

/-- Determine if `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
    and return `some n` as result. Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
def isNatValue? (e : Expr) : Option Nat :=
  match e with
  | Expr.lit (Literal.natVal n) => some n
  | _ => none

/-- Return `true` if `e := Nat.add e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.add expression.
-/
def isNatAddExpr (e : Expr) : Bool :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Nat.add _ => args.size == 2
      | _ => false
 | _ => false

/-- Determine if `e` is a Nat.add expression and return it's correponding arguments.
   Otherwise return `none`.
-/
def toNatAddExpr? (e: Expr) : Option (Expr × Array Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Nat.add _ => some (f, args)
      | _ => none
 | _ => none

/-- Return `true` if `e := Nat.sub e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.sub expression.
-/
def isNatSubExpr (e: Expr) : Bool :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Nat.sub _ => args.size == 2
      | _ => false
 | _ => false

/-- Determine if `e` is a Nat.sub expression and return it's correponding arguments.
   Otherwise return `none`.
-/
def toNatSubExpr? (e: Expr) : Option (Expr × Array Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Nat.sub _ => some (f, args)
      | _ => none
 | _ => none

/-- Determine if `e` is a Nat.mul expression and return it's correponding arguments.
    Otherwise return `none`.
-/
def toNatMulExpr? (e: Expr) : Option (Expr × Array Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Nat.mul _ => some (f, args)
      | _ => none
 | _ => none

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

    Return `none` when e is not a full applied Nat binary operator.
    Assume that operands have already been reordered for commutative operators.
-/
def toNatCstOpExpr? (e: Expr) : Option NatCstOpInfo :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      if args.size == 2 then
        let op1 := args[0]!
        let op2 := args[1]!
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
      else none
 | _ => none


/-- Apply the following normalization rules on a `Const` expression:
     - mkConst ``Nat.zero _ ===> Expr.lit (Literal.natVal 0)
-/
def normConst (n : Name) (l : List Level) : TranslateEnvT Expr := do
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ => return (mkConst n l)

/-- Return `true` when `e1 := -ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isIntNegExprOf (e1: Expr) (e2 : Expr) : MetaM Bool :=
  Expr.withApp e1 fun f as =>
    match f, as with
    | Expr.const ``Int.neg _, #[op] => exprEq e2 op
    | _, _ => pure false

/-- Determine if `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
    Return either `some (Int.ofNat n)` or `some (Int.negSucc n)` as result.
    Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
def isIntValue? (e : Expr) : Option Int :=
  match e with
  | Expr.app .. =>
     Expr.withApp e fun f args =>
       if args.size == 1 then
         let op := args[0]!
         match isNatValue? op with
         | some n =>
             match f with
             | Expr.const ``Int.ofNat _ => Int.ofNat n
             | Expr.const ``Int.negSucc _ => Int.negSucc n
             | _ => none
         | none => none
       else none
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
  /-- Int.div N e info. -/
  | IntDivLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.div e N info. -/
  | IntDivRightExpr (e : Expr) (n : Int) : IntCstOpInfo
  /-- Int.mod N e info. -/
  | IntModLeftExpr (n : Int) (e : Expr) : IntCstOpInfo
  /-- Int.mod e N info. -/
  | IntModRightExpr (e : Expr) (n : Int) : IntCstOpInfo
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
    - IntDivLeftExpr N n (if e := Int.div N n)
    - IntDivLeftExpr n N (if e := Int.div n N)
    - IntModLeftExpr N n (if e := Int.mod N n)
    - IntModRightExpr n N (if e := Int.mod n N)
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
partial def toIntCstOpExpr? (e: Expr) : Option IntCstOpInfo :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      if args.size == 1 then
         match f, (toIntCstOpExpr? args[0]!) with
          | Expr.const ``Int.neg _, IntCstOpInfo.IntAddExpr n op2 =>
              some (IntCstOpInfo.IntNegAddExpr n op2)
          | _, _ => none
      else if args.size == 2 then
           let op1 := args[0]!
           let op2 := args[1]!
           match f, (isIntValue? op1), (isIntValue? op2) with
           | Expr.const ``Int.add _, some n, _ => some (IntCstOpInfo.IntAddExpr n op2)
           | Expr.const ``Int.mul _, some n, _ => some (IntCstOpInfo.IntMulExpr n op2)
           | Expr.const ``Int.div _, some n, _ => some (IntCstOpInfo.IntDivLeftExpr n op2)
           | Expr.const ``Int.div _, _, some n => some (IntCstOpInfo.IntDivRightExpr op1 n)
           | Expr.const ``Int.mod _, some n, _ => some (IntCstOpInfo.IntModLeftExpr n op2)
           | Expr.const ``Int.mod _, _, some n => some (IntCstOpInfo.IntModRightExpr op1 n)
           | Expr.const ``Int.ediv _, some n, _ => some (IntCstOpInfo.IntEDivLeftExpr n op2)
           | Expr.const ``Int.ediv _, _, some n => some (IntCstOpInfo.IntEDivRightExpr op1 n)
           | Expr.const ``Int.emod _, some n, _ => some (IntCstOpInfo.IntEModLeftExpr n op2)
           | Expr.const ``Int.emod _, _, some n => some (IntCstOpInfo.IntEModRightExpr op1 n)
           | Expr.const ``Int.fdiv _, some n, _ => some (IntCstOpInfo.IntFDivLeftExpr n op2)
           | Expr.const ``Int.fdiv _, _, some n => some (IntCstOpInfo.IntFDivRightExpr op1 n)
           | Expr.const ``Int.fmod _, some n, _ => some (IntCstOpInfo.IntFModLeftExpr n op2)
           | Expr.const ``Int.fmod _, _, some n => some (IntCstOpInfo.IntFModRightExpr op1 n)
           | _, _, _ => none
      else none
 | _ => none

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
     - #[e1, e2] ===> #[e2, e1] (if e2 < e1)
     - #[e1, e2] ===> args

    An error is triggered when args.size ≠ 2.
    NOTE: Precedence is applied according to the order in which the rules have been specified.
-/
def reorderArgs (args : Array Expr) : MetaM (Array Expr) := do
 if args.size == 2 then
   let e1 := args[0]!
   let e2 := args[1]!
   match e1, e2 with
   | Expr.const ``False _, _ => pure args
   | _, Expr.const ``False _ => pure (args.swap! 0 1)
   | Expr.const ``True _, _ => pure args
   | _, Expr.const ``True _ => pure (args.swap! 0 1)
   | Expr.lit _, _ => pure args
   | _, Expr.lit _ => pure (args.swap! 0 1)
   | _, _ =>
     match (← isConstructor e1), (← isConstructor e2) with
     | true, true =>
        match hasVars e1, hasVars e2 with
        | false, false | true, true => pure (swapOnCond (e2.lt e1))
        | false, true => pure args
        | true, false => pure (args.swap! 0 1)
     | false, true => pure (args.swap! 0 1)
     | true, false => pure args
     | false, false =>
        match e1, e2 with
        | Expr.bvar n1, Expr.bvar n2 => pure (swapOnCond (n2 <= n1))
        | Expr.fvar id1, Expr.fvar id2 => pure (swapOnCond (id2.name.lt id1.name))
        | Expr.mvar id1, Expr.mvar id2 => pure (swapOnCond (id2.name.lt id1.name))
        | Expr.bvar _, _ => pure args
        | _, Expr.bvar _ => pure (args.swap! 0 1)
        | Expr.fvar _, _ => pure args
        | _, Expr.fvar _ => pure (args.swap! 0 1)
        | Expr.mvar _, _ => pure args
        | _, Expr.mvar _ => pure (args.swap! 0 1)
        | _, _ => pure (swapOnCond (e2.lt e1))
 else throwError "reorderArgs: two arguments expected"

 where
   swapOnCond (cond : Bool) : Array Expr :=
    if cond then args.swap! 0 1 else args


/-- call `reorderArgs` but consider the following additional rule:
     - #[not e, e] ===> #[e, not e]
-/
def reorderBoolOp (args: Array Expr) : MetaM (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isBoolNotExprOf e1 e2)
  then pure (args'.swap! 0 1)
  else pure args'

/-- call `reorderBoolOp` but consider the following additional rule:
     - #[¬ e, e] ===> #[e, ¬ e]
-/
def reorderPropOp (args: Array Expr) : MetaM (Array Expr) := do
  let args' ← reorderBoolOp args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isNotExprOf e1 e2)
  then pure (args'.swap! 0 1)
  else pure args'

/-- call `reorderArgs` but consider the following additional rule:
    - #[(Nat.sub x y), (Nat.add p q)] ===> #[Nat.add p q, Nat.sub x y]
-/
def reorderNatOp (args: Array Expr) : MetaM (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (isNatSubExpr e1 && isNatAddExpr e2)
  then pure (args'.swap! 0 1)
  else pure args'

/-- call `reorderArgs` but consider the following additional rule:
    - #[Int.neg x, x] ===> #[x, Int.neg x]
-/
def reorderIntOp (args: Array Expr) : MetaM (Array Expr) := do
  let args' ← reorderArgs args
  let e1 := args'[0]!
  let e2 := args'[1]!
  if (← isIntNegExprOf e1 e2)
  then pure (args'.swap! 0 1)
  else pure args'


/-- Return true if `n` corresponds to a matcher expression name. -/
def isMatchExpr (n : Name) : MetaM Bool := Option.isSome <$> getMatcherInfo? n

/-- Unfold fuction `f` w.r.t. the effective parameters `args` only when:
     - f is not a constructor
     - f is not tagged as an opaque definition
     - f is not a recursive function
     - f is not an undefined type class function
     - f is not a match application
-/
partial def getUnfoldFunDef? (f: Expr) (args: Array Expr) : MetaM (Option Expr) := do
 match f with
 | Expr.const n l =>
   if (isOpaqueFun n args) || (← isRecursiveFun n) || (← isMatchExpr n)
   then return none
   else match (← getConstInfo n) with
        | cInfo@(ConstantInfo.defnInfo _) =>
            let auxApp ← instantiateValueLevelParams cInfo l
            let reduced := Expr.beta auxApp args
            if (← isUndefinedClassFunApp reduced)
            then pure none
            else pure reduced
        | _ => pure none
 | Expr.proj .. =>
    -- case when f is function defined in a class instance
   match (← reduceProj? f) with
   | some re => pure (Expr.beta re args)
   | none => pure none
 | _ => pure none

 where
   /-- Return `true` if `e` corresponds to an undefined type class function application, i.e.,
       - `e := app (Expr.proj c _ _) ...`; and
       - `c` is the name of a type class in the given environment; and
       - `Expr.proj c _ _` cannot be reduced.
   -/
   isUndefinedClassFunApp (e : Expr) : MetaM Bool := do
     match e.getAppFn with
     | p@(Expr.proj c _ _) =>
        pure ((← reduceProj? p).isNone && (isClass (← getEnv) c))
     | _ => pure false

end Solver.Optimize
