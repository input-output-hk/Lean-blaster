import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize

/-- Normalize `String.mk (List.cons c₁ (.. (List.cons cₙ List.nil)))` to `Expr.lit (Literal.strVal s)`
    only when the list of chars are constant values.
    Otherwise return `mkExpr (mkApp f args[0]!)`.
    Assume that `f := Expr.const ``String.mk.
    An error is triggered when args.size ≠ 1.
-/
def normStringValue (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "normStringValue: only one argument expected"
  let op := args[0]!
  let some elms ← getListChars? op | return (← mkExpr (mkApp f op))
  mkExpr (mkStrLit (String.mk elms.toList))

  where
    getListChars? (e : Expr) : MetaM (Option (Array Char)) := do
      let mut e := e
      let mut chars := #[]
      while true do
        match_expr e with
        | List.nil _ => break
        | List.cons _ a as => do
            let some c := isCharValue? a | return none
            chars := chars.push c
            e := as
        | _ => return none
      return some chars


/-- Apply simplification/normalization rules on String operators. -/
def optimizeString? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const ``String.mk _ := f | return none
 normStringValue f args


end Solver.Optimize
