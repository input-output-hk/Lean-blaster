import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Lemmas.LemmasDecide

open Lean Meta Elab
namespace Blaster.Optimize

/-- Apply the following simplification/normalization rules on `Blaster.decide'`:
      - decide' False ==> false      [proof: Blaster.decide'_false_simp]
      - decide' True ==> true        [proof: Blaster.decide'_true_simp]
      - decide' (true = p) ==> p     [proof: Blaster.decide'_true_eq]
      - decide' (false = p) ==> ! p  [proof: Blaster.decide'_false_eq]
    An error is trigerred if args.size ≠ 2.
-/
def optimizeDecideCore (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "optimizeDecideCore: one argument expected but got {reprStr args}"
  -- args[0] proposition
  let p := args[0]!
  if let Expr.const ``False _ := p then
    pushProofStep (.rewrite (mkConst ``Blaster.decide'_false_simp))
    return (← mkBoolFalse)
  if let Expr.const ``True _ := p then
    pushProofStep (.rewrite (mkConst ``Blaster.decide'_true_simp))
    return (← mkBoolTrue)
  if let some r ← decideBoolEq? p then return r
  return mkApp f p

where
  /-- Return `some p` if `e := true = p`
      Return `some (! p)` if `e := false = p`
      Otherwise `none`.
  -/
  decideBoolEq? (e : Expr) : TranslateEnvT (Option Expr) := do
   match eq? e with
   | some (_, Expr.const ``true _, p) =>
    pushProofStep (.rewrite (mkConst ``Blaster.decide'_true_eq))
    return (some p)
   | some (_, Expr.const ``false _, p) =>
    pushProofStep (.rewrite (mkConst ``Blaster.decide'_false_eq))
    return (mkApp (← mkBoolNotOp) p)
   | _ => return none

/-- Apply simplification/normalization rules on `Blaster.decide'`. -/
def optimizeDecide? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Blaster.decide' _ => optimizeDecideCore f args
  | _ => pure none

end Blaster.Optimize
