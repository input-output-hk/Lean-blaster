import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize

/-- Return `true` when `e` corresponds to the null string literal. -/
def isNullString (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.strVal "") => true
  | _ => false

/-- Normalize `String.mk (List.cons c₁ (.. (List.cons cₙ List.nil)))` to `Expr.lit (Literal.strVal s)`
    only when the list of chars are constant values.
    Otherwise return `(mkApp f args[0]!)`.
    Assume that `f := Expr.const ``String.mk.
    An error is triggered when args.size ≠ 1.
-/
def normStringValue (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "normStringValue: only one argument expected"
  let op := args[0]!
  let some elms ← getListChars? op | return (mkApp f op)
  return (mkStrLit (String.mk elms.toList))

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


/-- Apply the following simplification/normalization rules on `String.append` :
     - S1 ++ S2 ==> S1 "++" S2
     - "" ++ e | e ++ "" ==> e
   Assume that f = Expr.const ``String.append.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `String.append` expected at this stage)
-/
def optimizeStrAppend (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeStrAppend: exactly two arguments expected"
 -- args[0] left operand
 -- args[1] right operand
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← cstStrAppend? op1 op2 then return r
 if let some r ← appendNull? op1 op2 then return r
 return (mkApp2 f op1 op2)

 where
   /-- Given `op1` and `op2` corresponding to the operands for `String.append`
       return `some (S1 "++" S2)` when `op1 := S1 ∧ op2 := S2`.
       Otherwise `none`.
   -/
   cstStrAppend? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
    match op1, op2 with
    | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => mkStrLitExpr (s1 ++ s2)
    | _, _ => return none

   /-- Given `op1` and `op2` corresponding to the operands for `String.append`,
        - return `some op2` when op1 := ""`.
       - return `some op1` when op2 := ""`
       Otherwise `none`.
   -/
   appendNull? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     if isNullString op1 then return op2
     if isNullString op2 then return op1
     return none

/-- Apply the following simplification/normalization rules on `String.length` :
     - String.length S ==> "String.length" S
   Assume that f = Expr.const ``String.length.
   An error is triggered when args.size ≠ 1 (i.e., only fully applied `String.length` expected at this stage)
-/
def optimizeStrLength (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeStrLength: exactly one arguments expected"
 let op := args[0]!
 if let some r ← cstStrLength? op then return r
 return (mkApp f op)

 where
   /-- Given `op` corresponding to the operand for `String.length`
       return `some ("String.length" S)` when `op := S`.
       Otherwise `none`.
   -/
   cstStrLength? (op : Expr) : TranslateEnvT (Option Expr) := do
    match op with
    | Expr.lit (Literal.strVal s) => mkNatLitExpr (String.length s)
    | _ => return none

/-- Apply the following simplification/normalization rules on `String.replace` :
     - String.replace e1 e2 e3 ==> e1 (if e2 =ₚₜᵣ e3)
     - String.replace S1 S2 S3 ==> "String.replace" S1 S2 S3
     - String.replace "" e2 e3 ==> ""
   Assume that f = Expr.const ``String.replace.
   An error is triggered when args.size ≠ 3 (i.e., only fully applied `String.replace` expected at this stage)
-/
def optimizeStrReplace (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeStrReplace: exactly three arguments expected"
 -- args[0] string to which replace is applied
 -- args[1] pattern argument for replacement
 -- args[2] replacement argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[3]!
 if exprEq op2 op3 then return op1
 if let some r ← cstStrReplace? op1 op2 op3 then return r
 if isNullString op1 then return op1
 return (mkApp3 f op1 op2 op3)

 where

   /-- Given `op1`, `op2` and `op3` corresponding to the operands for `String.replace`
       return `some ("String.replace" S1 S2 S3)` when `op1 := S1 ∧ op2 := S2 ∧ op3 := S3`.
       Otherwise `none`.
   -/
   cstStrReplace? (op1 : Expr) (op2 : Expr) (op3 : Expr) : TranslateEnvT (Option Expr) :=
    match op1, op2, op3 with
    | Expr.lit (Literal.strVal s1),
      Expr.lit (Literal.strVal s2),
      Expr.lit (Literal.strVal s3) => mkStrLitExpr (String.replace s1 s2 s3)
    | _, _, _  => return none


/-- Apply simplification/normalization rules on `String` operators. -/
def optimizeString? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
 | ``String.mk => normStringValue f args
 | ``String.append => optimizeStrAppend f args
 | ``String.length => optimizeStrLength f args
 | ``String.replace => optimizeStrReplace f args
 | _ => return none

end Solver.Optimize
