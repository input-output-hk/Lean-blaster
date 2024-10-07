import Lean
import Solver.Optimize.OptimizeEq
import Solver.Optimize.OptimizeNat
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `Int.neg` :
     - - (- n) ==> n
   Assume that f = Expr.const ``Int.neg.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: `Int.neg` on constant values are handled via `reduceApp`.
   TODO: consider additional simplification rules
-/
def optimizeIntNeg (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   match (args[0]!.app1? ``Int.neg) with
   | some e => pure e
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
       | some (IntCstOpInfo.IntAddExpr n2 e2) => optimizeIntAdd f #[(← evalBinIntOp Int.add n1 n2), e2]
       | some (IntCstOpInfo.IntNegAddExpr n2 e2) =>
          optimizeIntAdd f #[(← evalBinIntOp Int.sub n1 n2), (← optimizeIntNeg (← mkIntNegOp) #[e2])]
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


/-- Return `some e` if `n := Int.neg (Int.ofNat e)`. Otherwise return `none`. -/
def intNegOfNat? (n : Expr) : Option Expr :=
  match n.app1? ``Int.neg with
  | some e => e.app1? ``Int.ofNat
  | none => none

/-- Apply the following simplification rules on `Int.toNat` :
     - Int.toNat (Int.ofNat e) ===> e
     - Int.toNat (Int.neg (Int.ofNat e)) ===> 0
   Assume that f = Expr.const ``Int.toNat.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: `Int.toNat` on constant values are handled via `reduceApp`.
-/
def optimizeIntToNat (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1 then
   let op := args[0]!
   match op.app1? ``Int.ofNat with
   | some e => return e
   | none =>
      match intNegOfNat? op with
      | none => mkAppExpr f args
      | some .. => mkNatLitExpr 0
 else mkAppExpr f args

/-- Normalize `Int.negSucc n` to `Int.neg (Int.ofNat (Nat.add 1 n))` only when `n` is not a constant value.
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
       let addExpr ← optimizeNatAdd (← mkNatAddOp) #[← mkNatLitExpr 1, args[0]!]
       let intExpr ← mkAppExpr (← mkIntOfNat) #[addExpr]
       optimizeIntNeg (← mkIntNegOp) #[intExpr]
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
    | ``Int.toNat => some <$> optimizeIntToNat f args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
