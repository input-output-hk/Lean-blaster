import Lean
import Solver.Optimize.OptimizeBool
import Solver.Optimize.OptimizeEq
import Solver.Optimize.OptimizeITE
import Solver.Optimize.OptimizeProp
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Determine if all explicit parameters of a function are constructors (i.e., constant values).
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : MetaM Bool := do
  let stop := args.size
  let fInfo ← getFunInfoNArgs f stop
  let rec loop (i : Nat) : MetaM Bool := do
    if i < stop then
      let aInfo := fInfo.paramInfo[i]!
      let e := args[i]!
      if aInfo.isExplicit
      then if (← isConstructor e)
           then loop (i+1)
           else pure false
      else loop (i+1)
    else pure true
  loop 0


/-- Try to reduce an application when all explicit parameters are constructors.
  The reduced expression is returned only when it's a constructor.
  Otherwise the initial application expression is return.
  NOTE: whnf will not perform any reduction on ``Eq application.
-/
def reduceApp (f : Expr) (args: Array Expr) : MetaM Expr := do
 let appExpr := (mkAppN f args)
 if (← allExplicitParamsAreCtor f args)
 then
   let re ← whnf appExpr
   if (← isConstructor re)
   then pure re
   else pure appExpr
 else pure appExpr

/-- Perform constant propagation and apply simplifcation and normalization rules on
an application expression.
  TODO: consider additional simplification rules
-/
def optimizeApp (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  match (← optimizeProp f args) with
  | some e => pure e
  | none =>
     match (← optimizeBool f args) with
     | some e => pure e
     | none =>
        match (← optimizeEquality f args) with
        | some e => pure e
        | none =>
           match (← optimizeIfThenElse f args) with
           | some e => pure e
           | none => pure (mkAppN f args)

end Solver.Optimize
