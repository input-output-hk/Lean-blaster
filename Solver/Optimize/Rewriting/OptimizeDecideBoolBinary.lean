import Lean
import Solver.Optimize.Rewriting.OptimizeBoolBinary


open Lean Meta
namespace Solver.Optimize


/-- Given `op1` and `op2` corresponding to the operands for a Boolean binary operator:
    - return `some (decide' (mkOpExpr #[e1, e2]))` when `op1 := decide' e1 ∧ op2 := decide' e2`
    - return `some (decide' (mkOpExpr #[e1, true = e2]))` when `op1 := decide' e1 ∧ op2 := e2`
    - return `some (decide' (mkOpExpr #[e1, true = e2]))` when `op1 := e2 ∧ op2 := decide' e1`
    Otherwise `none`.
-/
def decideOpDecide?
  (op1 : Expr) (op2 : Expr)
  (mkOpExpr : Expr → Expr → Expr) : TranslateEnvT (Option Expr) := do
  match decide'? op1, decide'? op2 with
  | some e1, some e2 =>
      setRestart
      return mkApp (← mkSolverDecideConst) (mkOpExpr e1 e2)
  | some e1, _ =>
      setRestart
      return mkApp (← mkSolverDecideConst) (mkOpExpr e1 (mkApp3 (← mkEqOp) (← mkBoolType) (← mkBoolTrue) op2))
  | _, some e1 =>
      setRestart
      return mkApp (← mkSolverDecideConst) (mkOpExpr e1 (mkApp3 (← mkEqOp) (← mkBoolType) (← mkBoolTrue) op1))
  | _, _ => return none


/-- Call `optimizeBoolAnd f args` and apply the following `decide` simplification/normalization
    rules on the resulting `and` expression (if any):
     - decide' e1 && decide' e2 ==> decide' (e1 ∧ e2)
     - decide' e1 && e2 | e2 && decide' e1 ==> decide' (e1 ∧ true = e2)

   Assume that f = Expr.const ``and.

   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
-/
def optimizeDecideBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolAnd f args
 let some (op1, op2) := boolAnd? e | return e
 if let some r ← decideOpDecide? op1 op2 (mkApp2 (← mkPropAndOp)) then return r
 return e

/-- Call `optimizeBoolOr f args` and apply the following `decide` simplification/normalization
    rules on the resulting `or` expression (if any):
     - decide' e1 || decide' e2 ==> decide' (e1 ∨ e2)
     - decide' e1 || e2 | e2 || decide' e1 ==> decide' (e1 ∨ true = e2)

   Assume that f = Expr.const ``or.

   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: reordering on list of `||` must be performed to regroup all `decide' e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeDecideBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolOr f args
 let some (op1, op2) := boolOr? e | return e
 if let some r ← decideOpDecide? op1 op2 (mkApp2 (← mkPropOrOp)) then return r
 return e


/-- Apply simplification/normalization rules on Boolean binary operators.
-/
def optimizeBoolBinary? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
 | ``and => optimizeDecideBoolAnd f args
 | ``or => optimizeDecideBoolOr f args
 | _=> return none

end Solver.Optimize
