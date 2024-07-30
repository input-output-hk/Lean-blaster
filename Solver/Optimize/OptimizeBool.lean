import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false
     - true && e ==> e
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e && not e ==> false
     - not e ∧ e ==> false
     - e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``and.
   An error is triggered if args.size ≠ 2.
   TODO: consider additional simplification rules
-/
def optimizeBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let opArgs ← reorderArgs args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match op1, op2 with
 | Expr.const ``false _, _ => pure op1
 | Expr.const ``true _, _ => pure op2
 | _, _ => do
   if (← (isBoolNotExprOf op1 op2) <||> (isBoolNotExprOf op2 op1))
   then pure (mkConst ``false)
   else if (← exprEq op1 op2)
        then pure op1
        else pure (mkAppN f opArgs)

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e
     - true || e ==> true
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e || not e ==> true
     - not e || e ==> true
     - e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``or.
   An error is triggered if args.size ≠ 2.
   TODO: consider additional simplification rules
-/
def optimizeBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let opArgs ← reorderArgs args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match op1, op2 with
 | Expr.const ``false _, _ => pure op2
 | Expr.const ``true _, _ => pure op1
 | _, _ => do
   if (← (isBoolNotExprOf op1 op2) <||> (isBoolNotExprOf op2 op1))
   then pure (mkConst ``true)
   else if (← exprEq op1 op2)
        then pure op1
        else pure (mkAppN f opArgs)

/-- Return `some e` if `c := not e`. Otherwise `none`.
-/
def toBoolNotExpr (c : Expr) : Option Expr :=
 if c.isApp then
   Expr.withApp c fun k as =>
   match k, as with
   | Expr.const ``not _, #[op] => some op
   | _, _ => none
 else none

/-- Apply the following simplification/normalization rules on `not` :
     - ! false ==> true
     - ! true ==> false
     - ! (! e) ==> e
   Assume that f = Expr.const ``not.
   An error is triggered if args.size ≠ 1.
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match args[0]! with
   | Expr.const ``false _ => pure (mkConst ``true)
   | Expr.const ``true _ => pure (mkConst ``false)
   | e =>
       match (toBoolNotExpr e) with
       | some op => pure op
       | none => pure (mkAppN f args)
 else throwError "optimizeBoolNot: only one argument expected"

/-- Apply simplification/normalization rules on Boolean operators.
-/
def optimizeBool (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
    match n with
    | ``and => some <$> optimizeBoolAnd f args
    | ``or => some <$> optimizeBoolOr f args
    | ``not => some <$> optimizeBoolNot f args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
