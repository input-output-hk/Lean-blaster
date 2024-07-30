import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∧ ¬ e ==> False
     - ¬ e ∧ e ==> False
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   An error is triggered if args.size ≠ 2.
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let opArgs ← reorderArgs args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match op1, op2 with
 | Expr.const ``False _, _ => pure op1
 | Expr.const ``True _, _ => pure op2
 | _, _ => do
   if (← (isNotExprOf op1 op2) <||> (isNotExprOf op2 op1))
   then pure (mkConst ``False)
   else if (← exprEq op1 op2)
        then pure op1
        else pure (mkAppN f opArgs)

/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∨ ¬ e ==> True
     - ¬ e ∨ e ==> True
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   An error is triggered if args.size ≠ 2.
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let opArgs ← reorderArgs args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match op1, op2 with
 | Expr.const ``False _, _ => pure op2
 | Expr.const ``True _, _ => pure op1
 | _, _ => do
   if (← (isNotExprOf op1 op2) <||> (isNotExprOf op2 op1))
   then pure (mkConst ``True)
   else if (← exprEq op1 op2)
        then pure op1
        else pure (mkAppN f opArgs)

/-- Return `some e` if `c := ¬ e`. Otherwise `none`.
-/
def toNotExpr (c : Expr) : Option Expr :=
 if c.isApp then
   Expr.withApp c fun k as =>
   match k, as with
   | Expr.const ``Not _, #[op] => some op
   | _, _ => none
 else none

/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True
     - ¬ True ==> False
     - ¬ (¬ e) ==> e
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1.
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match args[0]! with
   | Expr.const ``False _ => pure (mkConst ``True)
   | Expr.const ``True _ => pure (mkConst ``False)
   | e =>
       match (toNotExpr e) with
       | some op => pure op
       | none => pure (mkAppN f args)
 else throwError "optimizeNot: only one argument expected"

/-- Apply simplification and normalization rules on proposition formulae.
-/
def optimizeProp (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const n _ =>
     match n with
     | ``And => some <$> optimizeAnd f args
     | ``Or => some <$> optimizeOr f args
     | ``Not => some <$> optimizeNot f args
     | _ => pure none
  | _ => pure none


end Solver.Optimize
