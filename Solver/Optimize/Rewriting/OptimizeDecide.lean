import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta Elab
namespace Solver.Optimize

/-- Given `#[p d]` corresponding to the arguments of `Decidable.decide`, such that:
      - p is a proposition
      - d the current decidable instance
    Return `#[p d']` such that `d'` corresponds to the synthesize instance obtained for `[Decidable p]`.

    NOTE: This function needs to be called for each `Decidable.decide` as `p` may have been
    modified due to simplification/normalization rules.
-/
def updateDecideInstance (args : Array Expr) : TranslateEnvT (Array Expr) := do
  pure (args.set! 1 (← synthDecidableWithNotFound! args[0]!))

/-- Apply the following simplification/normalization rules on `Decidable.decide`:
      - decide False ==> false
      - decide True ==> true
      - decide (true = p) ==> p
      - decide (false = p) ==> ! p
    An error is trigerred if args.size ≠ 2.
-/
partial def optimizeDecideCore (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 2 then throwEnvError f!"optimizeDecideCore: two arguments expected but got {reprStr args}"
  -- args[0] proposition
  -- args[1] decidable instance
  let p := args[0]!
  if let Expr.const ``False _ := p then return (← mkBoolFalse)
  if let Expr.const ``True _ := p then return (← mkBoolTrue)
  if let some r ← decideBoolEq? p then return r
  mkAppExpr f (← updateDecideInstance args)

where
  /-- Return `some p` if `e := true = p`
      Return `some (! p)` if `e := false = p`
      Otherwise `none`.
  -/
  decideBoolEq? (e : Expr) : TranslateEnvT (Option Expr) := do
   match e.eq? with
   | some (_, Expr.const ``true _, p) => return (some p)
   | some (_, Expr.const ``false _, p) => some <$> (mkExpr (mkApp (← mkBoolNotOp) p))
   | _ => return none

/-- Apply simplification/normalization rules on `Decidable.decide. -/
def optimizeDecide? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Decidable.decide _ => optimizeDecideCore f args
  | _ => pure none

end Solver.Optimize
