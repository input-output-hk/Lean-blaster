import Lean
import Solver.Optimize.Rewriting.OptimizeDecideBoolBinary
import Solver.Optimize.Rewriting.OptimizeBoolNot
import Solver.Optimize.Rewriting.OptimizeForAll
import Solver.Optimize.Rewriting.OptimizePropNot
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta Elab
namespace Solver.Optimize


/-- Given `#[s c d t e]` corresponding to the arguments of an `ite` or `dite`, such that:
      - s is the sort parameter
      - c is the `cond` operand
      - d is the current decidable instance for the ite cond
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
      - d is the current decidable instance for the ite cond
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


/-- Return the normalization/simplification result for
    `(!(decide c) || t) && (decide c || e)` only when `Type(t) = Bool`.
-/
def iteToBoolExpr? (iteType: Expr) (decInst : Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  if !(isBoolType iteType) then return none
  let decExpr ← optimizeDecideCore (← mkDecideConst) #[c, decInst]
  let orOp ← mkBoolOrOp
  let notExpr ← optimizeBoolNot (← mkBoolNotOp) #[decExpr]
  let leftAnd ← optimizeDecideBoolOr orOp #[notExpr, t]
  let rightAnd ← optimizeDecideBoolOr orOp #[decExpr, e]
  some <$> optimizeDecideBoolAnd (← mkBoolAndOp) #[leftAnd, rightAnd]

/-- Return the normalization/simplification result for `(c → t) ∧ (¬ c → e)`
    only when Type(t) = Prop.
-/
def iteToPropExpr? (iteType: Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  if !iteType.isProp then return none
  let leftAnd ← mkImpliesExpr c t
  let notExpr ← optimizeNot (← mkPropNotOp) #[c]
  let rightAnd ← mkImpliesExpr notExpr e
  some <$> optimizeBoolPropAnd (← mkPropAndOp) #[leftAnd, rightAnd]


/-- Return `some (true = c')` only when `c := false = c'`.
    This function also checks if `true = c'` is already in cache.
    Otherwise `none`.
-/
def isITEBoolSwap? (c : Expr) : TranslateEnvT (Option Expr) := do
  match c.eq? with
  | some (eq_sort, Expr.const ``false _, op2) =>
       some <$> mkExpr (mkApp3 c.getAppFn eq_sort (← mkBoolTrue) op2)
  | _ => return none

/-- Apply the following simplification/normalization rules on `ite` :
     - if c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - if True then e1 else e2 ==> e1
     - if False then e1 else e2 ==> e2
     - if c then e1 else e2 ==> if c' then e2 else e1 (if c := ¬ c')
     - if c then e1 else e2 ==> if true = c' then e2 else e1 (if c := false = c')
     - if c then e1 else e2 ==> (!(decide c) || e1) && (decide c || e2) (if Type(e1) = Bool)
     - if c then e1 else e2 ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)
    Some advanced ITE simplification rules to be considered:
     - if c then e1 = e2 else e1 = e3 ===> e1 = if c then e2 else e3 (TODO)

   Assume that f = Expr.const ``ite
   An error is triggered if args.size ≠ 5.
   TODO: consider additional simplification rules.
-/
partial def optimizeITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 5 then throwError "optimizeITE: five arguments for ITE"
 -- args[0] is sort parmeter
 -- args[1] is cond operand
 -- args[2] is decidable instance parameter on cond
 -- args[3] is then operand
 -- args[4] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let decInst := args[2]!
 let t := args[3]!
 let e := args[4]!
 if (← exprEq t e) then return t
 if let Expr.const ``True _ := c then return t
 if let Expr.const ``False _ := c then return e
 if let Expr.app (Expr.const ``Not _) ne := c then return (← optimizeITE f (← swapITEAndUpdateDecidable (args.set! 1 ne)))
 if let some c' ← (isITEBoolSwap? c) then return (← optimizeITE f (← swapITEAndUpdateDecidable (args.set! 1 c')))
 if let some r ← iteToBoolExpr? iteType decInst c t e then return r
 if let some r ← iteToPropExpr? iteType c t e then return r
 mkAppExpr f (← updateITEDecidable args)


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
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (!decide c || e1) && (decide c || e2) (if Type(e1) = Bool)
     - `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)

    Some advanced ITE simplification rules to be considered:
     - if c then e1 = e2 else e1 = e3 ===> e1 = if c then e2 else e3 (TODO)

    Assume that f = Expr.const ``dite
    An error is triggered if args.size ≠ 5.
    TODO: consider additional simplification rules.
-/
partial def optimizeDITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 5 then throwError "optimizeDITE: five arguments for DITE"
 -- args[0] is sort parmeter
 -- args[1] is cond operand
 -- args[2] is decidable instance parameter on cond
 -- args[3] is then operand
 -- args[4] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let decInst := args[2]!
 let t := args[3]!
 let e := args[4]!
 let thenExpr ← extractDependentITEExpr t
 let elseExpr ← extractDependentITEExpr e
 if (← exprEq thenExpr elseExpr) then return thenExpr
 if let Expr.const ``True _ := c then return thenExpr
 if let Expr.const ``False _ := c then return elseExpr
 if let Expr.app (Expr.const ``Not _) ne := c then return (← optimizeDITE f (← swapITEAndUpdateDecidable (args.set! 1 ne)))
 if let some c' ← isITEBoolSwap? c then return (← optimizeDITE f (← swapITEAndUpdateDecidable (args.set! 1 c')))
 if let some r ← iteToBoolExpr? iteType decInst c thenExpr elseExpr then return r
 if let some r ← iteToPropExpr? iteType c thenExpr elseExpr then return r
 mkAppExpr f (← updateITEDecidable args)


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
