import Lean
import Solver.Optimize.OptimizeEq
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize

/-- Return `some e` if `n := -e`. Otherwise `none`.
-/
def toIntNegExpr? (n : Expr) : Option Expr :=
 if n.isApp then
   Expr.withApp n fun k as =>
   match k, as with
   | Expr.const ``Int.neg _, #[op] => some op
   | _, _ => none
 else none

/-- Apply the following simplification/normalization rules on `Int.neg` :
     - - (- n) ==> n
   Assume that f = Expr.const ``Int.neg.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: `Int.neg` on constant values are handled via `reduceApp`.
   TODO: consider additional simplification rules
-/
def optimizeIntNeg (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match (toIntNegExpr? args[0]!) with
   | some op => pure op
   | none => mkAppExpr f args
 else mkAppExpr f args

/-- Apply the following simplification/normalization rules on `Int.add` :
     - 0 + n ==> n
     - N1 + (N2 + n) ==> (N1 "+" N2) + n
     - N1 + -(N2 + n) ==> (N1 "-" N2) + -n
     - n1 + (-n2) ==> 0 if (if n1 =ₚₜᵣ n2)
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Int.add.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Int.add` on constant values are handled via `reduceApp`.
-/
partial def optimizeIntAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderIntOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match (isIntValue? op1) with
   | some (Int.ofNat 0) => pure op2
   | some n1 =>
       match (toIntCstOpExpr? op2) with
       | some (IntCstOpInfo.IntAddExpr n2 e2) => mkAppExpr f #[(← evalBinIntOp Int.add n1 n2), e2]
       | some (IntCstOpInfo.IntNegAddExpr n2 e2) =>
          mkAppExpr f #[(← evalBinIntOp Int.sub n1 n2), (← optimizeIntNeg (← mkIntNegOp) #[e2])]
       | some _ | none => mkAppExpr f opArgs
   | none =>
      if (← isIntNegExprOf op2 op1)
      then mkIntLitExpr (Int.ofNat 0)
      else mkAppExpr f opArgs
 else mkAppExpr f args


/-- Apply the following simplification/normalization rules on `Int.mul` :
     - 0 * n ==> 0
     - 1 * n ==> n
     - -1 * n ==> -n
     - N1 * (N2 * n) ==> (N1 "*" N2) * n
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Int.mul.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Int.mul` on constant values are handled via `reduceApp`.
-/
def optimizeIntMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderIntOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match (isIntValue? op1) with
   | some (Int.ofNat 0) => return op1
   | some (Int.ofNat 1) => return op2
   | some (Int.negSucc 0) => optimizeIntNeg (← mkIntNegOp) #[op2]
   | some n1 =>
       match (toIntCstOpExpr? op2) with
       | some (IntCstOpInfo.IntMulExpr n2 e2) => mkAppExpr f #[(← evalBinIntOp Int.mul n1 n2), e2]
       | some _ | none => mkAppExpr f opArgs
   | none => mkAppExpr f opArgs
 else mkAppExpr f args


/-- Normalize `Int.negSucc n` to `-(n + 1)` only when `n` is not a constant value.
    An error is triggered if args.size ≠ 1.
    Assume that f = Expr.const ``Int.negSucc.
    NOTE: `Int.negSucc` on constant values are handled via `reduceApp`.
-/
def optimizeIntNegSucc (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1
 then
   let op := args[0]!
   match (isNatValue? op) with
   | none =>
       let addExpr ← optimizeIntAdd (← mkIntAddOp) #[← mkIntLitExpr (Int.ofNat 1), args[0]!]
       optimizeIntNeg (← mkIntNegOp) #[addExpr]
   | some _ => mkAppExpr f args
 else throwError "optimizeIntNegSucc: only one argument expected"


/-- Apply simplification/normalization rules on Int operators.
-/
def optimizeInt? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
    match n with
    | ``Int.add => some <$> optimizeIntAdd f args
    | ``Int.mul => some <$> optimizeIntMul f args
    | ``Int.neg => some <$> optimizeIntNeg f args
    | ``Int.negSucc => some <$> optimizeIntNegSucc f args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
