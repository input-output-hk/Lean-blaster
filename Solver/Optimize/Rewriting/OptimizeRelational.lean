import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta
namespace Solver.Optimize


/-- Return `true` when `e` corresponds to the zero nat literal. -/
def isZeroNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 0 => true
  | _ => false

/-- Apply the following simplification/normalization rules on `LE.le` :
     - e1 ≤ e2 ==> True (if e1 =ₚₜᵣ e2)
     - 0 ≤ e ==> True (if Type(e) = Nat)
     - C1 ≤ C2 ==> C1 "≤" C2 (if Type(C1) = Nat ∨ Type(C1) = Int)
   The simplifications are only applied when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LE.le.
   Do nothing if operator is partially applied (i.e., args.size < 4)
   NOTE: There is currently no LE instance for String.
-/
def optimizeLE (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (← mkAppExpr f args)
 if args.size != 4 then return (← mkAppExpr f args)
 -- args[0] is sort parameter
 -- args[1] Le instance
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if (← exprEq op1 op2) then return (← mkPropTrue)
 if (isZeroNat op1) then return (← mkPropTrue)
 if let some r ← cstLEProp op1 op2 then return r
 mkAppExpr f args

 where
   /-- Given `op1` and `op2` corresponding to the operands for `LE.le`:
         - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
         - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
       NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
       Otheriwse `none`.
   -/
   cstLEProp (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
    match op1, op2 with
    | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) => mkPropLit (Nat.ble n1 n2)
    | _, _ =>
      match isIntValue? op1, isIntValue? op2 with
      | some n1, some n2 => mkPropLit (n1 ≤ n2)
      | _, _ => return none

/-- Apply the following simplification/normalization rules on `LT.lt` :
     - e1 < e2 ==> False (if e1 =ₚₜᵣ e2)
     - e < 0 ==> False (if Type(e) = Nat)
     - C1 < C2 ==> C1 "<" C2
   The simplifications are only applied when isOpaqqueRelational predicate is satisfied
   Assume that f = Expr.const ``LT.lt.
   Do nothing if operator is partially applied (i.e., args.size < 4)
-/
def optimizeLT (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (← mkAppExpr f args)
 if args.size != 4 then return (← mkAppExpr f args)
 -- args[0] is sort parameter
 -- args[1] Le instance
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if (← exprEq op1 op2) then return (← mkPropFalse)
 if (isZeroNat op2) then return (← mkPropFalse)
 if let some r ← cstLTProp op1 op2 then return r
 mkAppExpr f args

 where
   /-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
         - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
         - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
         - return `some (S1 "<" S2)` when `op1 := S1 ∧ op2 := S2 ∧ Type(op1) = String`
       NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
       Otheriwse `none`.
   -/
   cstLTProp (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
    match op1, op2 with
    | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) => mkPropLit (Nat.blt n1 n2)
    | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => mkPropLit (s1 < s2)
    | _, _ =>
      match isIntValue? op1, isIntValue? op2 with
      | some n1, some n2 => mkPropLit (n1 < n2)
      | _, _ => return none

/-- Apply simplification and normalization rules on `LE.le` and `LT.lt` :
-/
def optimizeRelational? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 match f with
 | Expr.const n _ =>
     match n with
      | ``LE.le => some <$> optimizeLE f args
      | ``LT.lt => some <$> optimizeLT f args
      | _ => pure none
 | _ => pure none


end Solver.Optimize
