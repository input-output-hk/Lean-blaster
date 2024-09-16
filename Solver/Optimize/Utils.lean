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
    ``Int.add,
    ``Int.sub,
    ``Int.neg,
    ``Int.mul,
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
    ``LE.le, -- GE.ge a b abbrev for LE.le b a
    ``LT.lt, -- Gt.gt a b abbrev for LT.lt b a
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
  if f == `BEq.beq && args.size == 4
  then
    match args[0]! with
    | Expr.const n _ => beqCompatibleTypes.contains n
    | _ => false
  else false

/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : Bool :=
  opaqueFuns.contains f || isOpaqueBeq f args

/-- Return `true` if c corresponds to a constructor. -/
def isCtorName (c : Name) : MetaM Bool := do
  pure (← getConstInfo c).isCtor

/-- Return `true` if e corresponds to a constructor expression. -/
def isCtorExpr (e : Expr) : MetaM Bool := do
  match e with
  | Expr.const n _ => pure (← getConstInfo n).isCtor
  | _ => pure false

/-- Return `true` if e corresponds to an enumerator constructor (i.e., constructor without any parameters).
-/
def isEnumConst (e : Expr) : MetaM Bool := do
 match e with
 | Expr.const n _ =>
     match (← getConstInfo n) with
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
          match (← getConstInfo n) with
          | ConstantInfo.ctorInfo info =>
             -- should be fully applied
             -- numFields corresponds to the constructor parameters
             -- numParams corresponds to the Inductive type parameters
             pure (as.size == info.numFields + info.numParams && !info.type.isProp)
          | _ => pure false
       | _ => pure false
 | _ => pure false

/-- Return `true` if e corresponds to a constructor (i.e., constant value). -/
def isConstructor (e : Expr) : MetaM Bool := isEnumConst e <||> (pure e.isLit) <||> isFullyAppliedConst e

/-- Return `true` if e corresponds to an implication, i.e., a → b,
    with Type(a) = Prop and Type(b) = Prop.
-/
def isImplies (e : Expr) : MetaM Bool :=
 match e with
 | Expr.forallE _ t b _ =>
     if !b.hasLooseBVars
     then  isProp t <&&> isProp b
     else return false
 | _ => return true

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

/-- Determine if `e` is a nat literal expression `Expr.lit (Literal.natVal n)`
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
    TODO: consider additional normalization rules.
    This function also updates the definition dependency graph.
-/
def normConst (n : Name) (l : List Level) : TranslateEnvT Expr := do
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ => updateConstGraph n l

  where
   -- TODO: add only function and inductive types
   updateConstGraph (n : Name) (l : List Level) : TranslateEnvT Expr := do
      addConstant n
      mkExpr (mkConst n l)


/-- Reorders operands `args` for commutative operator to normalize expression, such that:
     - #[``False, _] ===> args
     - #[e,``False] ===> #[``False, e]
     - #[True, _] ===> args
     - #[e ``True] ===> #[``True, e]
     - #[Expr.lit _, _] ===> args
     - #[e, Expr.lit l] ===> #[Expr.lit l, e]
     - #[e1, e2] ===> #[e2, e1] (if isConstructor e1 ∧ isConstructor e2 ∧ e2.hash < e1.hash)
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
     - #[e1, e2] ===> #[e2, e1] (if e2.hash < e1.hash)
     - #[e1, e2] ===> args

    NOTE: Precedence is applied according to the order in which the rules have been specified.

    Throws an error if size of args is not equal to two. -/
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
     | true, true => pure (swapOnCond (e2.hash < e1.hash))
     | false, true => pure (args.swap! 0 1)
     | true, false => pure args
     | false, false =>
        match e1, e2 with
        | Expr.bvar n1, Expr.bvar n2 => pure (swapOnCond (n2 < n1))
        | Expr.fvar id1, Expr.fvar id2 => pure (swapOnCond (id2.name.lt id1.name))
        | Expr.mvar id1, Expr.mvar id2 => pure (swapOnCond (id2.name.lt id1.name))
        | Expr.bvar _, _ => pure args
        | _, Expr.bvar _ => pure (args.swap! 0 1)
        | Expr.fvar _, _ => pure args
        | _, Expr.fvar _ => pure (args.swap! 0 1)
        | Expr.mvar _, _ => pure args
        | _, Expr.mvar _ => pure (args.swap! 0 1)
        | _, _ => pure (swapOnCond (e2.hash < e1.hash))
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

-- TO GET REC DEFINITION
-- IF let some (.defnInfo info) := (← getEnv).find? f then
-- match (← getUnfoldEqnFor? f) with
-- | none => throwError "getUnfoldFunDef?: equation theorem expected for {f}"
-- | some eqnThm =>
--    forallTelescopeReducing ((← getConstInfo eqnThm).type) fun eq_args eqn => do
--      let some (_, _, e) := eqn.eq? | throwError "getUnfoldFunDef: expecting equality got {eqn}"
--      if isRecFun f e
--      then pure none
--      else pure (Expr.beta (← mkLambdaFVars eq_args e) args)


/-- Unfold fuction `f` w.r.t. the effective parameters `args` only when:
     - f is not a constructor
     - f is not tagged as an opaque definition
     - f is not a recursive function
-/
partial def getUnfoldFunDef? (f: Expr) (args: Array Expr) : MetaM (Option Expr) := do
 match f with
 | Expr.const n l =>
   if (isOpaqueFun n args) || (← isRecursiveDefinition n)
   then return none
   else
    match (← getConstInfo n) with
    | ConstantInfo.defnInfo info =>
        let reduced := Expr.beta info.value args
        if (← isUndefinedClassFunApp reduced)
        then pure none
        else normConstLevel n l reduced
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
     match e with
     | Expr.app .. =>
        match (Expr.getAppFn e) with
        | p@(Expr.proj c _ _) =>
           pure ((← reduceProj? p).isNone && (isClass (← getEnv) c))
        | _ => pure false
     | _ => pure false

   /-- Given `n`, `us` and `be` apply following normalization rules on `be`:
     - app (const ``Not l1) (app (const ``Eq l2) e1 e2) ===> app (const ``Not l1) (app (const ``Eq us) e1 e2) (if n = ``Ne)
     - app (const ``not l1) (app (const ``BEq.beq l2) e1 e2) ===> app (const ``not l1) (app (const ``BEq.beq us) e1 e2) (if n = ``bne)
     - app (const ``LT.lt l) e1 e2 ==> app (const ``Lt.lt us) e1 e2 (if n = ``GT.gt)
     - app (const ``LE.le l) e1 e2 ==> app (const ``Lt.lt us) e1 e2 (if n = ``GE.ge)
     Return `be` when the above normalization rules cannot be applied.
   -/
   normConstLevel (n : Name) (us : List Level) (be : Expr) : MetaM Expr :=
    match be with
    | Expr.app .. =>
        Expr.withApp be fun f args =>
         match f, n with
         | Expr.const ``Not _, ``Ne =>
            match isEqExpr? args[0]! with
            | some (eq, eq_ops) => pure (mkApp f (mkAppN (Expr.updateConst! eq us) eq_ops))
            | none => pure be
         | Expr.const ``not _, ``bne =>
            match isBEqExpr? args[0]! with
            | some (beq, beq_ops) => pure (mkApp f (mkAppN (Expr.updateConst! beq us) beq_ops))
            | none => pure be
         | Expr.const ``LT.lt _, ``GT.gt
         | Expr.const ``LE.le _, ``GE.ge => pure (mkAppN (Expr.updateConst! f us) args)
         | _, _ => pure be
    | _ => pure be

end Solver.Optimize
