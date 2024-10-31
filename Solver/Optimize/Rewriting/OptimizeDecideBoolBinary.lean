import Lean
import Solver.Optimize.Rewriting.OptimizeBoolPropBinary
import Solver.Optimize.Rewriting.OptimizeDecide
import Solver.Optimize.Rewriting.OptimizeEq


open Lean Meta
namespace Solver.Optimize


/-- Given `op1` and `op2` corresponding to the operands for a Boolean binary operator:
    - return `some (decide (mkOpExpr #[e1, e2]))` when `op1 := decide e1 ∧ op2 := decide e2`
    - return `some (decide (mkOpExpr #[e1, true = e2]))` when `op1 := decide e1 ∧ op2 := e2`
    - return `some (decide (mkOpExpr #[e1, true = e2]))` when `op1 := e2 ∧ op2 := decide e1`
    Otherwise `none`.
-/
def decideOpDecide?
  (op1 : Expr) (op2 : Expr)
  (mkOpExpr : Array Expr → TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  match decide? op1, decide? op2 with
  | some (e1, d), some (e2, _) =>
      -- NOTE: the decidable instance for `decide` is updated in `optimizeDecideCore`
      some <$> optimizeDecideCore (← mkDecideConst) #[← mkOpExpr #[e1, e2], d]
  | some (e1, d), _ =>
      some <$> optimizeDecideCore (← mkDecideConst) #[← mkOpExpr #[e1, ← mkEqBool op2 true], d]
  | _, some (e1, d) =>
      some <$> optimizeDecideCore (← mkDecideConst) #[← mkOpExpr #[e1, ← mkEqBool op1 true], d]
  | _, _ => return none


/-- Call `optimizeBoolAnd f args` and apply the following `decide` simplification/normalization
    rules on the resulting `and` expression (if any):
     - decide e1 && decide e2 ===> decide (e1 ∧ e2)
     - decide e1 && e2 | e2 && decide e1 ===> decide (e1 ∧ true = e2)

   Assume that f = Expr.const ``and.

   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
-/
def optimizeDecideBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolAnd f args (cacheResult := false)
 let some (op1, op2) := boolAnd? e | return e
 if let some r ← decideOpDecide? op1 op2 (optimizeBoolPropAnd (← mkPropAndOp)) then return r
 mkExpr e

/-- Call `optimizeBoolOr f args` and apply the following `decide` simplification/normalization
    rules on the resulting `or` expression (if any):
     - decide e1 || decide e2 ===> decide (e1 ∨ e2)
     - decide e1 || e2 | e2 || decide e1 ===> decide (e1 ∨ true = e2)

   Assume that f = Expr.const ``or.

   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: reordering on list of `||` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeDecideBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolOr f args (cacheResult := false)
 let some (op1, op2) := boolOr? e | return e
 if let some r ← decideOpDecide? op1 op2 (optimizeBoolPropOr (← mkPropOrOp)) then return r
 mkExpr e


/-- Apply simplification/normalization rules on Boolean binary operators.
-/
def optimizeBoolBinary? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
    match n with
    | ``and => some <$> optimizeDecideBoolAnd f args
    | ``or => some <$> optimizeDecideBoolOr f args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
