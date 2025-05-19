import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta
namespace Solver.Optimize


/-- Return `true` when `e` corresponds to the zero nat literal. -/
def isZeroNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 0 => true
  | _ => false

/-- Return `true` when `e` corresponds to the one nat literal. -/
def isOneNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 1 => true
  | _ => false

/-- Given `op1` and `op2` corresponding to the operands for `LE.le`:
      - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
      - return `some (N1 "≤" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
    NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
    Otheriwse `none`.
-/
def cstLEProp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
 match op1, op2 with
 | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) => mkPropLit (Nat.ble n1 n2)
 | _, _ =>
   match isIntValue? op1, isIntValue? op2 with
   | some n1, some n2 => mkPropLit (n1 ≤ n2)
   | _, _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` or `LT.lt`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N > 0 ∧ Type(N) = Int`
      - return `some True` when `op1 := N + e ∧ op2 := e ∧ N < 0 ∧ Type(N) = Int`
    Otherwise `none`.
-/
def intRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 let some n := isIntValue? e1 | return none
 if n == 0 then return none
 if !(← exprEq e2 op2) then return none
 if n > 0
 then return ← mkPropFalse
 else return ← mkPropTrue

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` or `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := e ∧ op2 := N + e ∧ N < 0 ∧ Type(N) = Int`
    Otherwise `none`.
-/
def intRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some n := isIntValue? e1 | return none
 if n == 0 then return none
 if !(← exprEq e2 op1) then return none
 if n > 0
 then return ← mkPropTrue
 else return ← mkPropFalse

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` or `LT.lt`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N > 0 ∧ Type(N) = Nat`
    Otherwise `none`.
-/
def natRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 let Expr.lit (Literal.natVal n) := e1 | return none
 if !(← exprEq e2 op2) then return none
 if n > 0
 then return ← mkPropFalse
 else return none

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` or `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Nat`
    Otherwise `none`.
-/
def natRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let Expr.lit (Literal.natVal n) := e1 | return none
 if !(← exprEq e2 op1) then return none
 if n > 0
 then return ← mkPropTrue
 else return none

/-- Given `op1` and `op2` corresponding to the operands for `LE.le`:
      - return `some N "-" 1 < e` when `op1 := N ∧ Type(N) = Int`
      - return `some e < N "+" 1` when `op2 := N ∧ Type(N) = Int`
      - return `some a < op2` when `op1 := 1 + a ∧ Type(N) = Int`
    Otherwise `none`.
-/
def intLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 if let some n := isIntValue? op1 then
   return (← mkIntLtExpr (← evalBinIntOp Int.sub n (Int.ofNat 1)) op2)
 if let some n := isIntValue? op2 then
   return (← mkIntLtExpr op1 (← evalBinIntOp Int.add n (Int.ofNat 1)))
 let some (e1, e2) := intAdd? op1 | return none
 let some 1 := isIntValue? e1 | return none
 mkIntLtExpr e2 op2

/-- Given `op1` and `op2` corresponding to the operands for `LE.le`:
     - return `some `N "-" 1 < e` when `op1 := N ∧ N > 0 ∧ Type(N) = Nat`
     - return `some e < N "+" 1` when `op2 := N ∧ Type(N) = Nat`
     - return `some a < op2` when `op1 := 1 + a ∧ Type(N) = Nat`
    Otherwise `none`.
-/
def natLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 if let some n := isNatValue? op1 then
    if n > 0 then return (← mkNatLtExpr (← evalBinNatOp Nat.sub n 1) op2)
 if let some n := isNatValue? op2 then
    return (← mkNatLtExpr op1 (← evalBinNatOp Nat.add n 1))
 let some (e1, e2) := natAdd? op1 | return none
 let some 1 := isNatValue? e1 | return none
 mkNatLtExpr e2 op2


/-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Nat`:
       - return `some False` when `N2 < N1`
       - return `some a < (N2 "-" N1) "+" 1` when `N2 > N1`
       - return `some 0 = a` when `N2 = N1`
    Otherwise `none`.
-/
def addNatLeftLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 let some n2 := isNatValue? op2 | return none
 let some n1 := isNatValue? e1 | return none
 if n2 < n1 then return ← mkPropFalse
 if n2 > n1
 then return ← mkNatLtExpr e2 (← evalBinNatOp Nat.add (n2 - n1) 1)
 else return ← mkNatEqExpr (← mkNatLitExpr 0) e2

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Nat`:
       - return `some True` when `N1 ≤ N2`
       - return `some (N1 "-" N2) - 1 < a` when `N1 > N2`
    Otherwise `none`.
-/
def addNatRightLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some n1 := isNatValue? op1 | return none
 let some n2 := isNatValue? e1 | return none
 if n1 ≤ n2 then return ← mkPropTrue
 else return ← mkNatLtExpr (← evalBinNatOp Nat.sub (n1 - n2) 1) e2


/-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Int`:
       - return `some a < (N2 "-" N1) "+" 1`
    Otherwise `none`.
-/
def addIntLeftLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 let some n2 := isIntValue? op2 | return none
 let some n1 := isIntValue? e1 | return none
 mkIntLtExpr e2 (← evalBinIntOp Int.add (n2 - n1) 1)

/-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Int`:
       - return `some N1 "-" N2 - 1 < a`
    Otherwise `none`.
-/
def addIntRightLeToLt? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some n1 := isIntValue? op1 | return none
 let some n2 := isIntValue? e1 | return none
 mkIntLtExpr (← evalBinIntOp Int.sub (n1 - n2) 1) e2


/-- Apply the following simplification/normalization rules on `LE.le` :
     - e1 ≤ e2 ==> True (if e1 =ₚₜᵣ e2)
     - 0 ≤ e ==> True (if Type(e) = Nat)
     - N1 ≤ N2 ==> N1 "≤" N2
     - e ≤ 0 ==> 0 = e (if Type(e) = Nat)
     - N + e ≤ e ==> False (if N > 0 ∧ Type(N) ∈ [Nat, Int])
     - N + e ≤ e ==> True (if N < 0 ∧ Type(N) = Int)
     - e ≤ N + e ==> True (if N > 0 ∧ Type(N) ∈ [Nat, Int])
     - e ≤ N + e ==> False (if N < 0 ∧ Type(N) = Int)
     - N1 + a ≤ N2 ==> False (if Type(a) = Nat ∧ N2 < N1)
     - N1 + a ≤ N2 ==> a < (N2 "-" N1) "+" 1 (if Type(a) = Nat ∧ N2 > N1)
     - N1 + a ≤ N2 ==> 0 = a (if Type(a) = Nat ∧ N2 = N1)
     - N1 + a ≤ N2 ==> a < (N2 "-" N1) "+" 1 (if Type(a) = Int)
     - N1 ≤ N2 + a ==> True (if Type(a) = Nat ∧ N1 ≤ N2)
     - N1 ≤ N2 + a ==> (N1 "-" N2) - 1 < a (if Type(a) = Nat ∧ N1 > N2)
     - N1 ≤ N2 + a ==> (N1 "-" N2) - 1 < a (if Type(a) = Int)
     - N1 + a ≤ N2 + b ==> N1 "-" min(N1, N2) + a ≤ N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])
     - N ≤ e ==> N "-" 1 < e (if N > 0 ∧ Type(N) = Nat)
     - N ≤ e ==> N "-" 1 < e (if Type(N) = Int)
     - e ≤ N ==> e < N "+" 1 (if Type(N) ∈ [Nat, Int])
     - 1 + a ≤ b ==> a < b (if Type(a) ∈ [Nat, Int])
   The simplifications are only applied when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LE.le.
   Do nothing if operator is partially applied (i.e., args.size < 4)
   NOTE: There is currently no LE instance for String.
-/
partial def optimizeLE (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
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
 if let some r ← cstLEProp? op1 op2 then return r
 if (isZeroNat op2) then return (← mkNatEqExpr op2 op1)
 if let some r ← intRelLeftReduce? op1 op2 then return r
 if let some r ← intRelRightReduce? op1 op2 then return r
 if let some r ← natRelLeftReduce? op1 op2 then return r
 if let some r ← natRelRightReduce? op1 op2 then return r
 if let some r ← addNatLeftLeToLt? op1 op2 then return r
 if let some r ← addNatRightLeToLt? op1 op2 then return r
 if let some r ← addIntLeftLeToLt? op1 op2 then return r
 if let some r ← addIntRightLeToLt? op1 op2 then return r
 if let some r ← addNatLeReduce? op1 op2 then return r
 if let some r ← addIntLeReduce? op1 op2 then return r
 if let some r ← intLeToLt? op1 op2 then return r
 if let some r ← natLeToLt? op1 op2 then return r
 mkAppExpr f args

 where
   /-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Nat`:
       - return `some N1 "-" min(N1, N2) + a ≤ N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addNatLeReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := natAdd? op1 | return none
     let some (e3, e4) := natAdd? op2 | return none
     let some n1 := isNatValue? e1 | return none
     let some n2 := isNatValue? e3 | return none
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' ← if leftValue = 0 then pure e2 else mkExpr (mkApp2 (← mkNatAddOp) (← mkNatLitExpr leftValue) e2)
     let op2' ← if rightValue = 0 then pure e4 else mkExpr (mkApp2 (← mkNatAddOp) (← mkNatLitExpr rightValue) e4)
     optimizeLE f #[args[0]!, args[1]!, op1', op2']

   /-- Given `op1` and `op2` corresponding to the operands for `LE.le` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Int`:
       - return `some N1 "-" min(N1, N2) + a ≤ N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addIntLeReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := intAdd? op1 | return none
     let some (e3, e4) := intAdd? op2 | return none
     let some n1 := isIntValue? e1 | return none
     let some n2 := isIntValue? e3 | return none
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' ← if leftValue = 0 then pure e2 else mkExpr (mkApp2 (← mkIntAddOp) (← mkIntLitExpr leftValue) e2)
     let op2' ← if rightValue = 0 then pure e4 else mkExpr (mkApp2 (← mkIntAddOp) (← mkIntLitExpr rightValue) e4)
     optimizeLE f #[args[0]!, args[1]!, op1', op2']



/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Nat`
      - return `some (N1 "<" N2)` when `op1 := N1 ∧ op2 := N2 ∧ Type(op1) = Int`
      - return `some (S1 "<" S2)` when `op1 := S1 ∧ op2 := S2 ∧ Type(op1) = String`
    NOTE: This function need to be updated each time we are opacifying other Lean inductive types.
    Otheriwse `none`.
-/
def cstLTProp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) :=
 match op1, op2 with
 | Expr.lit (Literal.natVal n1), Expr.lit (Literal.natVal n2) => mkPropLit (Nat.blt n1 n2)
 | Expr.lit (Literal.strVal s1), Expr.lit (Literal.strVal s2) => mkPropLit (s1 < s2)
 | _, _ =>
   match isIntValue? op1, isIntValue? op2 with
   | some n1, some n2 => mkPropLit (n1 < n2)
   | _, _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some op1 ≤ b` when `op2 := 1 + b ∧ Type(a) = Int`
    Otherwise `none`.
-/
def intLtToLe? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some 1 := isIntValue? e1 | return none
 mkIntLeExpr op1 e2


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some op1 ≤ b` when `op2 := 1 + b ∧ Type(a) = Nat`
    Otherwise `none`.
-/
def natLtToLe? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some 1 := isNatValue? e1 | return none
 mkNatLeExpr op1 e2


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Nat`:
       - return `some False` when `N2 ≤ N1`
       - return `some a < N2 "-" N1` when `N2 > N1`
    Otherwise `none`.
-/
def addNatLeftLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 let some n2 := isNatValue? op2 | return none
 let some n1 := isNatValue? e1 | return none
 if n2 ≤ n1 then return ← mkPropFalse
 else return ← mkNatLtExpr e2 (← evalBinNatOp Nat.sub n2 n1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Nat`:
       - return `some True` when `N1 < N2`
       - return `some N1 "-" N2 < a` when `N1 ≥ N2`
    Otherwise `none`.
-/
def addNatRightLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some n1 := isNatValue? op1 | return none
 let some n2 := isNatValue? e1 | return none
 if n1 < n2 then return ← mkPropTrue
 else return ← mkNatLtExpr (← evalBinNatOp Nat.sub n1 n2) e2


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Int`:
       - return `some a < N2 "-" N1`
    Otherwise `none`.
-/
def addIntLeftLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 let some n2 := isIntValue? op2 | return none
 let some n1 := isIntValue? e1 | return none
 mkIntLtExpr e2 (← evalBinIntOp Int.sub n2 n1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1`, `op2 := N2 + a` and Type(a) = Int`:
       - return `some N1 "-" N2 < a`
    Otherwise `none`.
-/
def addIntRightLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some n1 := isIntValue? op1 | return none
 let some n2 := isIntValue? e1 | return none
 mkIntLtExpr (← evalBinIntOp Int.sub n1 n2) e2

/-- Apply the following simplification/normalization rules on `LT.lt` :
     - e1 < e2 ==> False (if e1 =ₚₜᵣ e2)
     - e < 0 ==> False (if Type(e) = Nat)
     - N1 < N2 ==> N1 "<" N2
     - e < 1 ==> 0 = e (if Type(e) = Nat)
     - N + e < e ==> False (if N > 0 ∧ Type(e) ∈ [Nat, Int])
     - N + e < e ==> True (if N < 0 ∧ Type(e) = Int)
     - e < N + e ==> True (if N > 0 ∧ Type(N) ∈ [Nat, Int])
     - e < N + e ==> False (if N < 0 ∧ Type(N) = Int)
     - N1 + a < N2 ==> False (if Type(a) = Nat ∧ N2 ≤ N1)
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Nat ∧ N2 > N1)
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Int)
     - N1 < N2 + a ==> True (if Type(a) = Nat ∧ N1 < N2)
     - N1 < N2 + a ==> N1 "-" N2 < a (if Type(a) = Nat ∧ N1 ≥ N2)
     - N1 < N2 + a ==> N1 "-" N2 < a  (if Type(a) = Int)
     - N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])
     - a < 1 + b ==> a ≤ b (if Type(a) ∈ [Nat, Int])
   The simplifications are only applied when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LT.lt.
   Do nothing if operator is partially applied (i.e., args.size < 4)
-/
partial def optimizeLT (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (← mkAppExpr f args)
 if args.size != 4 then return (← mkAppExpr f args)
 -- args[0] is sort parameter
 -- args[1] LT instance
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if (← exprEq op1 op2) then return (← mkPropFalse)
 if (isZeroNat op2) then return (← mkPropFalse)
 if let some r ← cstLTProp? op1 op2 then return r
 if (isOneNat op2) then return (← mkNatEqExpr (← mkNatLitExpr 0) op1)
 if let some r ← intRelLeftReduce? op1 op2 then return r
 if let some r ← intRelRightReduce? op1 op2 then return r
 if let some r ← natRelLeftReduce? op1 op2 then return r
 if let some r ← natRelRightReduce? op1 op2 then return r
 if let some r ← addNatLeftLtReduce? op1 op2 then return r
 if let some r ← addNatRightLtReduce? op1 op2 then return r
 if let some r ← addIntLeftLtReduce? op1 op2 then return r
 if let some r ← addIntRightLtReduce? op1 op2 then return r
 if let some r ← intLtToLe? op1 op2 then return r
 if let some r ← natLtToLe? op1 op2 then return r
 mkAppExpr f args

 where
   /-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Nat`:
       - return `some N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addNatBothReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := natAdd? op1 | return none
     let some (e3, e4) := natAdd? op2 | return none
     let some n1 := isNatValue? e1 | return none
     let some n2 := isNatValue? e3 | return none
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' ← if leftValue = 0 then pure e2 else mkExpr (mkApp2 (← mkNatAddOp) (← mkNatLitExpr leftValue) e2)
     let op2' ← if rightValue = 0 then pure e4 else mkExpr (mkApp2 (← mkNatAddOp) (← mkNatLitExpr rightValue) e4)
     optimizeLT f #[args[0]!, args[1]!, op1', op2']

   /-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2 + b` and Type(a) = Int`:
       - return `some N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`
      Otherwise `none`
   -/
   addIntBothReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, e2) := intAdd? op1 | return none
     let some (e3, e4) := intAdd? op2 | return none
     let some n1 := isIntValue? e1 | return none
     let some n2 := isIntValue? e3 | return none
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' ← if leftValue = 0 then pure e2 else mkExpr (mkApp2 (← mkIntAddOp) (← mkIntLitExpr leftValue) e2)
     let op2' ← if rightValue = 0 then pure e4 else mkExpr (mkApp2 (← mkIntAddOp) (← mkIntLitExpr rightValue) e4)
     optimizeLT f #[args[0]!, args[1]!, op1', op2']


/-- Apply simplification and normalization rules on `LE.le` and `LT.lt` :
-/
def optimizeRelational? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
  | ``LE.le => optimizeLE f args
  | ``LT.lt => optimizeLT f args
  | _ => return none


end Solver.Optimize
