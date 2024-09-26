import Lean
import Solver.Optimize.OptimizeBool
import Solver.Optimize.OptimizeForAll
import Solver.Optimize.OptimizeProp
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta Elab
namespace Solver.Optimize


/-- Given `#[s c d t e]` corresponding to the arguments of an `ite` or `dite`, such that:
      - s is the sort parameter
      - c is the `cond` operand
      - d is the current decidable instance the ite cond
      - t is the `then` operand
      - e is the `else` operand
    This function returns `#[s c d' t e] such that `d'` correponds to the synthesize instance
    obtained for `[Decidable c]`.
    This function needs to be called for each ITE as `c` may have been modified
    due to simplification/normalization rules.
-/
def updateITEDecidable (args : Array Expr) : TranslateEnvT (Array Expr) := do
  pure (args.set! 2 (← synthDecidableInstance! args[1]!))

/-- Given `#[s c d t e]` corresponding to the arguments of an `ite` or `dite`, such that:
      - s is the sort parameter
      - c is the `cond` operand
      - d is the current decidable instance the ite cond
      - t is the `then` operand
      - e is the `else` operand
    This function returns `#[[s c d' e t]` such that `d'` corresponds to the synthesize instance
    obtained for `[Decidable c]`. As can be seen, the `then` and `else` operands are also swapped.
-/
def swapITEAndUpdateDecidable (args : Array Expr) : TranslateEnvT (Array Expr) := do
  -- synthesize decidable instance for cond operand and check if instance is in cache
  let args ← updateITEDecidable args
  -- swap then and else expression
  pure (args.swap! 3 4)


/-- Return the normalization/simplification result for `(! c' || t) && (c' || e)` only
    when the following conditions are satisfied:
     - c := true = c'; and
     - Type(t) = Bool
-/
def iteToBoolExpr? (iteType: Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  if (isBoolType iteType)
  then
    match isEqExpr? c with
    | some eq_args =>
      let op_args := eq_args.2
      match op_args[1]! with
      | Expr.const ``true _ =>
          let c' := op_args[2]!
          let orOp ← mkBoolOrOp
          let notExpr ← optimizeBoolNot (← mkBoolNotOp) #[c']
          let leftAnd ← optimizeBoolOr orOp #[notExpr, t]
          let rightAnd ← optimizeBoolOr orOp #[c', e]
          some <$> optimizeBoolAnd (← mkBoolAndOp) #[leftAnd, rightAnd]
      | _ => return none
    | none => return none
  else return none

/-- Return the normalization/simplification result for `(c → t) ∧ (¬ c → e)`
    only when Type(t) = Prop.
-/
def iteToPropExpr? (iteType: Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  if iteType.isProp
  then
    let leftAnd ← mkImpliesExpr c t
    let notExpr ← optimizeNot (← mkPropNotOp) #[c]
    let rightAnd ← mkImpliesExpr notExpr e
    some <$> optimizeAnd (← mkPropAndOp) #[leftAnd, rightAnd]
  else return none


/-- Return `some (true = c')` only when `c := false = c'`.
    This function also checks if `true = c'` is already in cache.
    Otherwise `none`.
-/
def isITEBoolSwap? (c : Expr) : TranslateEnvT (Option Expr) :=
  match isEqExpr? c with
  | some eq_args =>
     let op_args := eq_args.2
     match op_args[1]! with
     | Expr.const ``false _ => do
        some <$> mkAppExpr eq_args.1 (op_args.set! 1 (← mkBoolTrue))
     | _ => return none
  | none => return none

/-- Apply the following simplification/normalization rules on `ite` :
     - if c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - if True then e1 else e2 ==> e1
     - if False then e1 else e2 ==> e2
     - if c then e1 else e2 ==> if c' then e2 else e1 (if c := ¬ c')
     - if c then e1 else e2 ==> if true = c' then e2 else e1 (if c := false = c')
     - if c then e1 else e2 ==> (! c' || e1) && (c' || e2) (if Type(e1) = Bool ∧ c := true = c')
     - if c then e1 else e2 ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)
    Some advanced ITE simplification rules to be considered:
     - if c then e1 = e2 else e1 = e3 ===> e1 = if c then e2 else e3 (TODO)

   Assume that f = Expr.const ``ite
   An error is triggered if args.size ≠ 5.
   TODO: consider additional simplification rules.
-/
partial def optimizeITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 5 then
   -- args[0] is sort parmeter
   -- args[1] is cond operand
   -- args[2] is decidable instance parameter on cond
   -- args[3] is then operand
   -- args[4] is else operand
   let iteType := args[0]!
   let c := args[1]!
   let t := args[3]!
   let e := args[4]!
   if (← exprEq t e)
   then pure t
   else
     match c with
     | Expr.const ``True _ => pure t
     | Expr.const ``False _ => pure e
     | Expr.app (Expr.const ``Not _) ne =>
          optimizeITE f (← swapITEAndUpdateDecidable (args.set! 1 ne))
     | _ =>
        match (← isITEBoolSwap? c) with
        | some c' => optimizeITE f (← swapITEAndUpdateDecidable (args.set! 1 c'))
        | none =>
           match (← iteToBoolExpr? iteType c t e) with
           | some r => pure r
           | none =>
               match (← iteToPropExpr? iteType c t e) with
               | some r => pure r
               | none => mkAppExpr f (← updateITEDecidable args)
 else throwError "optimizeITE: five arguments for ITE"


/-- Given an expression of the form `fun h : c => e` return `e` as result.
   An error is triggered when:
     - the provided expression is not a `then` or `else` dependent ite expression,
       i.e., not a lambda expression of the form `fun h : c => e`; or
-/
def extractDependentITEExpr (e : Expr) : MetaM Expr :=
  match e with
  | Expr.lam _n _t b _bi => pure b
  | _ => throwError f!"extractDependentITEExpr: lambda expression expected but got {reprStr e}"

/-- Apply simplification/normalization rules on `dite`.
    Note that dependent ite is written with notation `if h : c then t else e`, which
    is the syntactic sugar for `dite c (fun h : c => t) (fun h : ¬ c => e)`.

    The simplifcation/normalization rules applied are:
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> e1 (if e1 =ₚₜᵣ e2)
     - `dite True (fun h : True => e1) (fun h : False => e2)` ==> e1
     - `dite False (fun h : True => e1) (fun h : False => e2)` ==> e2
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (! c' || e1) && (c' || e2) (if Type(e1) = Bool ∧ c := true = c')
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)

    Some advanced ITE simplification rules to be considered:
     - if c then e1 = e2 else e1 = e3 ===> e1 = if c then e2 else e3 (TODO)

    Assume that f = Expr.const ``dite
    An error is triggered if args.size ≠ 5.
    TODO: consider additional simplification rules.
-/
partial def optimizeDITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 5 then
   -- args[0] is sort parmeter
   -- args[1] is cond operand
   -- args[2] is decidable instance parameter on cond
   -- args[3] is then operand
   -- args[4] is else operand
   let iteType := args[0]!
   let c := args[1]!
   let t := args[3]!
   let e := args[4]!
   let thenExpr ← extractDependentITEExpr t
   let elseExpr ← extractDependentITEExpr e
   if (← exprEq thenExpr elseExpr)
   then pure thenExpr
   else
     match c with
     | Expr.const ``True _ => pure thenExpr
     | Expr.const ``False _ => pure elseExpr
     | Expr.app (Expr.const ``Not _) ne =>
         optimizeDITE f (← swapITEAndUpdateDecidable (args.set! 1 ne))
     | _ =>
        match (← isITEBoolSwap? c) with
        | some c' => optimizeDITE f (← swapITEAndUpdateDecidable (args.set! 1 c'))
        | none =>
           match (← iteToBoolExpr? iteType c thenExpr elseExpr) with
           | some r => pure r
           | none =>
               match (← iteToPropExpr? iteType c thenExpr elseExpr) with
               | some r => pure r
               | none => mkAppExpr f (← updateITEDecidable args)
 else throwError "optimizeDITE: five arguments for DITE"


/-- Apply simplification/normalization rules of if then else expressions. -/
def optimizeIfThenElse? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
  | Expr.const n _ =>
     match n with
     | ``ite => some <$> optimizeITE f args
     | ``dite => some <$> optimizeDITE f args
     | _ => pure none
  | _ => pure none

end Solver.Optimize
