import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize


/-- Return `some (true = e)` when `ne := false = e` or `some (false = e)` when `ne := true = e`.
    Otherwise `none`.
-/
def notEqSimp? (ne : Expr) : TranslateEnvT (Option Expr) := do
  match ne.eq? with
  | some (eq_sort, op1, op2) =>
     match op1 with
     | Expr.const ``false _ =>
         some <$> mkExpr (mkApp3 ne.getAppFn eq_sort (← mkBoolTrue) op2)
     | Expr.const ``true _ =>
         some <$> mkExpr (mkApp3 ne.getAppFn eq_sort (← mkBoolFalse) op2)
     | _ => return none
  | none => return none

/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True
     - ¬ True ==> False
     - ¬ (¬ e) ==> e (classical)
     - ¬ (false = e) ==> true = e
     - ¬ (true = e) ==> false = e
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1.
   NOTE: The `reduceApp` rule will not reduce `Not` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwError "optimizeNot: only one argument expected"
 let e := args[0]!
 if let Expr.const ``False _ := e then return (← mkPropTrue)
 if let Expr.const ``True _ := e then return (← mkPropFalse)
 if let some op := propNot? e then return op
 if let some r ← notEqSimp? e then return r
 mkAppExpr f args

/-- Apply simplification and normalization rules on proposition `Not` formulae.
-/
def optimizePropNot? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Not _ => some <$> optimizeNot f args
  | _ => pure none


end Solver.Optimize
