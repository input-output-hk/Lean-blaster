import Lean
import Blaster.Optimize.Expr
import Blaster.Optimize.Env

open Lean Meta

namespace Blaster.Optimize


/-- Determine if `e` is a list of expressions and return the concrete list representatin as result. -/
partial def isListCtor? (e : Expr) : Option (List Expr) :=
 let rec visit (e : Expr) (acc : List Expr) : Option (List Expr) :=
  match_expr e with
  | List.nil _ => some (List.reverse acc)
  | List.cons _ a as => visit as (a :: acc)
  | _ => none
 visit e []

/-- Apply the following simplification/normalization rules on `List.get?Internal` :
     - List.get?Internal [e₁, e₂, ..., eₙ] N ===> [e₁, e₂, ..., eₙ][N]?

   Assume that f = Expr.const ``List.get?Internal.
   TODO: Update spec
-/
def optimizeListGet? (args : Array Expr) : TranslateEnvT (Option Expr) := do
 if args.size != 3 then return none
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] index argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some n := isNatValue? op3 then
   if let some l := isListCtor? op2 then
     mkOptionExpr op1 l[n]?
   else return none
 else return none


/-- Apply the following simplification/normalization rules on `List.reverseAux` :
     - List.reverseAux [e₁, e₂, ..., eₙ] [x₁, x₂, ..., xₙ] N ===> `List.reverseAux` [e₁, e₂, ..., eₙ] [x₁, x₂, ..., xₙ]

   Assume that f = Expr.const ``List.reverseAux.
   TODO: Update spec
-/
def optimizeListReverseAux? (args : Array Expr) : TranslateEnvT (Option Expr) := do
 if args.size != 3 then return none
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some l1 := isListCtor? op2 then
   if let some l2 := isListCtor? op3 then
     listToExpr (List.reverseAux l1 l2) op1
   else return none
 else return none


/-- Apply simplification/normalization rules on `List` operators. -/
def optimizeList? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``List.get?Internal => optimizeListGet? args
  | ``List.reverseAux => optimizeListReverseAux? args
  | _ => return none

end Blaster.Optimize
