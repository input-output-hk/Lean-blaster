import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false
     - true && e ==> e
     - e && not e ==> false
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``and.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: consider additional simplification rules
-/
def optimizeBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``false _, _ => pure op1
   | Expr.const ``true _, _ => pure op2
   | _, _ => do
     if (← isBoolNotExprOf op2 op1)
     then mkBoolFalse
     else if (← exprEq op1 op2)
          then pure op1
          else mkAppExpr f opArgs
 else mkAppExpr f args

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e
     - true || e ==> true
     - e || not e ==> true
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``or.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: consider additional simplification rules
-/
def optimizeBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``false _, _ => pure op2
   | Expr.const ``true _, _ => pure op1
   | _, _ => do
     if (← isBoolNotExprOf op2 op1)
     then mkBoolTrue
     else if (← exprEq op1 op2)
          then pure op1
          else mkAppExpr f opArgs
 else mkAppExpr f args

/-- Return `some e` if `c := not e`. Otherwise `none`.
-/
def toBoolNotExpr? (c : Expr) : Option Expr :=
 if c.isApp then
   Expr.withApp c fun k as =>
   match k, as with
   | Expr.const ``not _, #[op] => some op
   | _, _ => none
 else none

/-- Apply the following simplification/normalization rules on `not` :
     - ! (! e) ==> e
   Assume that f = Expr.const ``not.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: `not` on constant values are handled via `reduceApp`.
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match args[0]! with
   | Expr.const ``false _ => mkBoolTrue
   | Expr.const ``true _ => mkBoolFalse
   | e =>
       match (toBoolNotExpr? e) with
       | some op => pure op
       | none => mkAppExpr f args
 else mkAppExpr f args

/-- Apply simplification/normalization rules on Boolean operators.
-/
def optimizeBool? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
    match n with
    | ``and => some <$> optimizeBoolAnd f args
    | ``or => some <$> optimizeBoolOr f args
    | ``not => some <$> optimizeBoolNot f args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
