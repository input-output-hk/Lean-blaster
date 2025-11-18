import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `Solver.decide'`:
      - decide' False ==> false
      - decide' True ==> true
      - decide' (true = p) ==> p
      - decide' (false = p) ==> ! p
    An error is trigerred if args.size ≠ 2.
-/
def optimizeDecideCore (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "optimizeDecideCore: one argument expected but got {reprStr args}"
  -- args[0] proposition
  let p := args[0]!
  if let Expr.const ``False _ := p then return (← mkBoolFalse)
  if let Expr.const ``True _ := p then return (← mkBoolTrue)
  if let some r ← decideBoolEq? p then return r
  return mkApp f p

where
  /-- Return `some p` if `e := true = p`
      Return `some (! p)` if `e := false = p`
      Otherwise `none`.
  -/
  decideBoolEq? (e : Expr) : TranslateEnvT (Option Expr) := do
   match eq? e with
   | some (_, Expr.const ``true _, p) => return (some p)
   | some (_, Expr.const ``false _, p) => return (mkApp (← mkBoolNotOp) p)
   | _ => return none

/-- Apply simplification/normalization rules on `Solver.decide'`. -/
def optimizeDecide? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Solver.decide' _ => optimizeDecideCore f args
  | _ => pure none

end Solver.Optimize
