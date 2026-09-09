import Lean
import Blaster.Optimize.Expr
import Blaster.Optimize.Env

open Lean Meta

namespace Blaster.Optimize


/-- Determine if `e` is a list of expressions and return the concrete list representatin as result. -/
def isListCtor? (e : Expr) : Option (List Expr) :=
 let rec visit (e : Expr) (acc : List Expr) : Option (List Expr) :=
  match e with
  | Expr.app (Expr.const ``List.nil _) _sort => some (List.reverse acc)
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _sort) a) as => visit as (a :: acc)
  | _ => none
 visit e []

/-- Apply the following simplification/normalization rules on `List.get?Internal` :
     - List.get?Internal [e₁, e₂, ..., eₙ] N ===> [e₁, e₂, ..., eₙ][N]?

   Assume that f = Expr.const ``List.get?Internal.
   Optimizations are not applied when args.size ≠ 3 (e.g., List.get as HOF)
-/
def optimizeListGet (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] index argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some r ← cstListGet op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3

 where

   /-- Given `sort_type`, `op1` and `op2` corresponding to the operands for `List.get?Internal`
        `return some `[e₁, e₂, ..., eₙ][N]?` when `op1 := [e₁, e₂, ..., eₙ] ∧ op2 := N`
   -/
   @[always_inline, inline]
   cstListGet (sort_type : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
     if let some n := isNatValue? op2 then
       if let some l := isListCtor? op1 then
         mkOptionExpr sort_type u l[n]?
       else return none
     else return none

/-- Reduce append through its known constructor prefix, preserving the unknown
    tail and sharing the entire right operand. Also eliminate either empty side.
    Partially applied functions are left unchanged. -/
def optimizeListAppend (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 let sortType := args[0]!
 let xs := args[1]!
 let ys := args[2]!
 if ys.isAppOfArity ``List.nil 1 then return xs
 let mut tail := xs
 let mut heads : List Expr := []
 repeat
   match tail with
   | .app (.app (.app (.const ``List.cons _) _) head) rest =>
       heads := head :: heads
       tail := rest
   | _ => break
 let isNil := tail.isAppOfArity ``List.nil 1
 if heads.isEmpty then
   if isNil then return ys
   return ← mkApp3Expr f sortType xs ys
 let mut out := ys
 if !isNil then out ← mkApp3Expr f sortType tail ys
 let cons ← mkAppExpr (← mkExpr (mkConst ``List.cons u)) sortType
 for head in heads do
   out ← mkApp2Expr cons head out
 setRestart
 return out

/-- Apply the following simplification/normalization rules on `List.reverseAux` :
     - List.reverseAux [e₁, e₂, ..., eₙ] [x₁, x₂, ..., xₙ] ===> `List.reverseAux` [e₁, e₂, ..., eₙ] [x₁, x₂, ..., xₙ]

   Assume that f = Expr.const ``List.reverseAux.
   Optimization are not applied when args.size ≠ 3 (e.g., List.reverse as HOF)
-/
def optimizeListReverseAux (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some r ← cstListReverse op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3

where
   /-- Given `sort_type`, `op1` and `op2` corresponding to the operands for `List.reverseAux`
        `return some ``List.reverseAux` [e₁, e₂, ..., eₙ] [x₁, x₂, ..., xₙ]` when `op1 := [e₁, e₂, ..., eₙ] ∧ op2 := [x₁, x₂, ..., xₙ]`
   -/
   @[always_inline, inline]
   cstListReverse (sort_type : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
     if let some l1 := isListCtor? op1 then
       if let some l2 := isListCtor? op2 then
         listToExpr (List.reverseAux l1 l2) u sort_type
       else return none
     else return none


/-- Apply the following simplification/normalization rules on `List.length` :
     - List.length [e₁, e₂, ..., eₙ] ===> `List.length` [e₁, e₂, ..., eₙ]

   Assume that f = Expr.const ``List.length.
   Optimization are not applied when args.size ≠ 3 (e.g., List.length as HOF)
-/
def optimizeListLength (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← cstListLength op2 then return r
 mkApp2Expr f op1 op2

where
   /-- Given `xs` corresponding to the operands for `List.length`
        `return some ``List.length` [e₁, e₂, ..., eₙ]` when `xs := [e₁, e₂, ..., eₙ]`
   -/
   @[always_inline, inline]
   cstListLength (xs : Expr) : TranslateEnvT (Option Expr) :=
     if let some l1 := isListCtor? xs
     then mkNatLitExpr (List.length l1)
     else return none

/-- Apply the following simplification/normalization rules on `List.take` :
     - List.take N [e₁, e₂, ..., eₙ] ===> `List.take` N [e₁, e₂, ..., eₙ]

   Assume that f = Expr.const ``List.take.
   Optimization are not applied when args.size ≠ 3 (e.g., List.take as HOF)
-/
def optimizeListTake (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] index argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some r ← cstListTake op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3

where
   /-- Given `sort_type`, `op1` and `op2` corresponding to the operands for `List.reverseAux`
        `return some ``List.take` N [e₁, e₂, ..., eₙ]` when `op1 := N ∧ op2 := [e₁, e₂, ..., eₙ]`
   -/
   @[always_inline, inline]
   cstListTake (sort_type : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
     if let some n := isNatValue? op1 then
       if let some l := isListCtor? op2 then
         listToExpr (List.take n l) u sort_type
       else return none
     else return none

/-- Drop a literal number of constructors, visiting at most that many nodes.
    Once the known prefix ends, retain a residual drop over its symbolic tail.
    Dropping from nil is nil even for a symbolic index. -/
def optimizeListDrop (f : Expr) (_u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 let sortType := args[0]!
 let index := args[1]!
 let xs := args[2]!
 if xs.isAppOfArity ``List.nil 1 then return xs
 let some n := isNatValue? index | return ← mkApp3Expr f sortType index xs
 let mut remaining := n
 let mut tail := xs
 while remaining > 0 do
   match tail with
   | .app (.const ``List.nil _) _ => return tail
   | .app (.app (.app (.const ``List.cons _) _) _) rest =>
       remaining := remaining - 1
       tail := rest
   | _ =>
       if remaining == n then return ← mkApp3Expr f sortType index xs
       setRestart
       return ← mkApp3Expr f sortType (← mkNatLitExpr remaining) tail
 return tail

/-- Apply the following simplification/normalization rules on `List.replicate` :
     - List.replicate N e ===> `List.replicate N e`

   Assume that f = Expr.const ``List.replicate.
   Optimizations are not applied when args.size ≠ 3 (e.g., List.replicate as HOF)
-/
def optimizeListReplicate (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] Number of copies
 -- args[2] element
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some r ← cstListReplicate op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3

 where

   /-- Given `sort_type`, `op1` and `op2` corresponding to the operands for `List.replicate`
        `return some `List.replicate N e` when `op1 := N`
   -/
   @[always_inline, inline]
   cstListReplicate (sort_type : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
     if let some n := isNatValue? op1
     then listToExpr (List.replicate n op2) u sort_type
     else return none


/-- Apply simplification/normalization rules on `List` operators. -/
def optimizeList? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n u := f | return none
  match n with
  | ``List.append => optimizeListAppend f u args
  | ``List.get?Internal => optimizeListGet f u args
  | ``List.reverseAux => optimizeListReverseAux f u args
  | ``List.length => optimizeListLength f args
  | ``List.take => optimizeListTake f u args
  | ``List.drop => optimizeListDrop f u args
  | ``List.replicate => optimizeListReplicate f u args
  | _ => return none

end Blaster.Optimize
