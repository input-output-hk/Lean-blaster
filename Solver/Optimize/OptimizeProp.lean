import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e ∧ ¬ e ==> False
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: The `reduceApp` rule will not reduce `And` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``False _, _ => pure op1
   | Expr.const ``True _, _ => pure op2
   | _, _ => do
     if (← isNotExprOf op2 op1)
     then mkPropFalse
     else if (← exprEq op1 op2)
          then pure op1
          else mkAppExpr f opArgs
 else mkAppExpr f args

/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e ∨ ¬ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: The `reduceApp` rule will not reduce `Or` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match op1, op2 with
   | Expr.const ``False _, _ => pure op2
   | Expr.const ``True _, _ => pure op1
   | _, _ => do
     if (← isNotExprOf op2 op1)
     then mkPropTrue
     else if (← exprEq op1 op2)
          then pure op1
          else mkAppExpr f opArgs
 else mkAppExpr f args

/-- Return `some e` if `c := ¬ e`. Otherwise `none`.
-/
def toNotExpr? (c : Expr) : Option Expr :=
 if c.isApp then
   Expr.withApp c fun k as =>
   match k, as with
   | Expr.const ``Not _, #[op] => some op
   | _, _ => none
 else none

/-- Return `some (true = e)` when `ne := false = e` or `some (false = e)` when `ne := true = e`.
    Otherwise `none`.
-/
def notEqSimp? (ne : Expr) : TranslateEnvT (Option Expr) := do
  match (isEqExpr? ne) with
  | some eq_args =>
     let eq_ops := eq_args.2
     match eq_ops[1]! with
     | Expr.const ``false _ =>
         some <$> mkAppExpr eq_args.1 (eq_ops.set! 1 (← mkBoolTrue))
     | Expr.const ``true _ =>
         some <$> mkAppExpr eq_args.1 (eq_ops.set! 1 (← mkBoolFalse))
     | _ => return none
  | none => return none

/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True
     - ¬ True ==> False
     - ¬ (¬ e) ==> e (classical)
     - ¬ (false = e) ==> true = e
     - ¬ (true = e) ==> false = e
   Assume that f = Expr.const ``Not.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: The `reduceApp` rule will not reduce `Not` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match args[0]! with
   | Expr.const ``False _ => mkPropTrue
   | Expr.const ``True _ => mkPropFalse
   | e =>
       match (toNotExpr? e) with
       | some op => pure op
       | none =>
          match (← notEqSimp? e) with
          | some r => pure r
          | none => mkAppExpr f args
 else mkAppExpr f args

/-- Apply simplification and normalization rules on proposition formulae.
-/
def optimizeProp? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const n _ =>
     match n with
     | ``And => some <$> optimizeAnd f args
     | ``Or => some <$> optimizeOr f args
     | ``Not => some <$> optimizeNot f args
     | _ => pure none
  | _ => pure none


end Solver.Optimize
