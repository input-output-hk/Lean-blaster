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
    ``LE.le,
    ``LT.lt,
    ``GE.ge,
    ``GT.gt,
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
    ``Nat.blt
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

/-- Return `true if e correponds to a fully applied parametric constructor.
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

/-- Return `true if e corresponds to a constructor (i.e., constant value). -/
def isConstructor (e : Expr) : MetaM Bool := isEnumConst e <||> (pure e.isLit) <||> isFullyAppliedConst e

/-- Return `true` when `e1 = ¬ ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool :=
  Expr.withApp e1 fun f as =>
    match f, as with
    | Expr.const ``Not _, #[op] => exprEq e2 op
    | _, _ => pure false

/-- Return `true` when `e1 = not ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
def isBoolNotExprOf (e1: Expr) (e2 : Expr) : MetaM Bool :=
  Expr.withApp e1 fun f as =>
    match f, as with
    | Expr.const ``not _, #[op] => exprEq e2 op
    | _, _ => pure false


/-- Determine if `e` is an Eq expression and return it's correponding operands.
   Otherwise return `none`.
-/
def isEqExpr? (e: Expr) : Option (Expr × Expr) :=
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args =>
      match f with
      | Expr.const ``Eq _ => some (args[1]!, args[2]!)
      | _ => none
 | _ => none


/-- Reorders operands for commutative operator to normalize expression.
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
        | Expr.fvar id1, Expr.fvar id2 => pure (swapOnCond (id2.name.hash < id1.name.hash))
        | Expr.mvar id1, Expr.mvar id2 => pure (swapOnCond (id2.name.hash < id1.name.hash))
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
 | Expr.const n _ =>
   if (isOpaqueFun n args) || (← isRecursiveDefinition n)
   then return none
   else
    match (← getConstInfo n) with
    | ConstantInfo.defnInfo info => pure (Expr.beta info.value args)
    | _ => pure none
 | Expr.proj .. =>
    -- case when f is function defined in a class instance
   match (← reduceProj? f) with
   | some re => pure (Expr.beta re args)
   | none => pure none
 | _ => pure none

end Solver.Optimize
