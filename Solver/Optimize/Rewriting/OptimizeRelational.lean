import Lean
import Solver.Optimize.Hypotheses

open Lean Meta
namespace Solver.Optimize

/-- Return `true` when `e` corresponds to the one nat literal. -/
def isOneNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 1 => true
  | _ => false

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N > 0 ∧ Type(N) = Int`
      - return `some True` when `op1 := N + e ∧ op2 := e ∧ N < 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(N) = Int ∧ geqZeroIntInHyps b`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(N) = Int ∧ geqZeroIntInHyps b`
      - return `some True` when `op1 := a + b ∧ op2 := a ∧ Type(N) = Int ∧ ltZeroIntInHyps b`
      - return `some True` when `op1 := b + a ∧ op2 := a ∧ Type(N) = Int ∧ ltZeroIntInHyps b`
    Otherwise `none`.
-/
def intRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 match isIntValue? e1 with
 | some n =>
    if !(exprEq e2 op2) then return none
    if n > 0
    then return ← mkPropFalse
    else return ← mkPropTrue
 | none =>
     if exprEq e1 op2 then
       if ← geqZeroIntInHyps e2 then return ← mkPropFalse
       if ← ltZeroIntInHyps e2 then return ← mkPropTrue
     if exprEq e2 op2 then
       if ← geqZeroIntInHyps e1 then return ← mkPropFalse
       if ← ltZeroIntInHyps e1 then return ← mkPropTrue
     return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := e ∧ op2 := N + e ∧ N < 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Int ∧ leqZeroIntInHyps b`
      - return `some False` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Int ∧ leqZeroIntInHyps b`
      - return `some True` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Int ∧ gtZeroIntInHyps b`
      - return `some True` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Int ∧ gtZeroIntInHyps b`
    Otherwise `none`.
-/
def intRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 match (isIntValue? e1) with
 | some n =>
      if !(exprEq e2 op1) then return none
      if n > 0
      then return ← mkPropTrue
      else return ← mkPropFalse
 | none =>
      if exprEq e1 op1 then
        if ← leqZeroIntInHyps e2 then return ← mkPropFalse
        if ← gtZeroIntInHyps e2 then return ← mkPropTrue
      if exprEq e2 op1 then
        if ← leqZeroIntInHyps e1 then return ← mkPropFalse
        if ← gtZeroIntInHyps e1 then return ← mkPropTrue
      return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(a) = Nat`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(a) = Nat`
    Otherwise `none`.
-/
def natRelLeftReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 if (exprEq e1 op2) then return ← mkPropFalse
 if (exprEq e2 op2) then return ← mkPropFalse
 return none

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some True` when `op1 := e ∧ op2 := N + e ∧ N > 0 ∧ Type(N) = Nat`
      - return `some False` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Nat ∧ eqZeroNatInHyps b`
      - return `some False` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Nat ∧ eqZeroNatInHyps b`
      - return `some True` when `op1 := a ∧ op2 := a + b ∧ Type(a) = Nat ∧ gtZeroNatInHyps b`
      - return `some True` when `op1 := a ∧ op2 := b + a ∧ Type(a) = Nat ∧ gtZeroNatInHyps b`
    Otherwise `none`.
-/
def natRelRightReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 match isNatValue? e1 with
 | some n =>
      if (exprEq e2 op1) then if n > 0 then return ← mkPropTrue
      return none
 | none =>
      if (exprEq e1 op1) then
        if ← eqZeroNatInHyps e2 then return ← mkPropFalse
        if ← gtZeroNatInHyps e2 then return ← mkPropTrue
      if (exprEq e2 op1) then
        if ← eqZeroNatInHyps e1 then return ← mkPropFalse
        if ← gtZeroNatInHyps e1 then return ← mkPropTrue
      return none

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
      - return `some ¬ (b < op1)` when `op2 := 1 + b ∧ Type(op1) = Int`
    Otherwise `none`.
-/
def intLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some 1 := isIntValue? e1 | return none
 setRestart
 return mkApp (← mkPropNotOp) (← mkIntLtExpr e2 op1)

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some b < 0` when `op1 := 0` ∧ op2 := -b ∧ Type(op1) = Int`
    Otherwise `none`.
-/
def intZeroLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some 0 := isIntValue? op1 | return none
 let some op2' := intNeg? op2 | return none
 setRestart
 mkIntLtExpr op2' op1


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`:
      - return `some ¬ (b < op1)` when `op2 := 1 + b ∧ Type(a) = Nat`
    Otherwise `none`.
-/
def natLtNorm? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some 1 := isNatValue? e1 | return none
 setRestart
 return (mkApp (← mkPropNotOp) (← mkNatLtExpr e2 op1))


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
 if n2 ≤ n1 then mkPropFalse
 else
   setRestart -- restart necessary to cache new expression
   mkNatLtExpr e2 (← evalBinNatOp Nat.sub n2 n1)

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
 if n1 < n2 then mkPropTrue
 else
   setRestart -- restart necessary to cache new expression
   mkNatLtExpr (← evalBinNatOp Nat.sub n1 n2) e2


/-- Given `op1` and `op2` corresponding to the operands for `LT.lt` such that,
     `op1 := N1 + a`, `op2 := N2` and Type(a) = Int`:
       - return `some a < N2 "-" N1`
    Otherwise `none`.
-/
def addIntLeftLtReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 let some n2 := isIntValue? op2 | return none
 let some n1 := isIntValue? e1 | return none
 setRestart -- restart necessary to cache new expression
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
 setRestart -- restart necessary to cache new expression
 mkIntLtExpr (← evalBinIntOp Int.sub n1 n2) e2

/-- Given `op1` and `op2` corresponding to the operands for `LT.lt`,
    return `true` only when the following conditions are satisfied
      - `op1 := N` ∧
      - ¬ (N - 1 < op2) _ ∈ hypothesisContext.hypothesisMap ∧
      - Type(op2) ∈ [Nat, Int]
-/
def predCstLTInHyp (op1 : Expr) (op2 : Expr) : TranslateEnvT Bool := do
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 match isNatValue? op1 with
 | some n =>
      let pred_n ← evalBinNatOp Nat.sub n 1
      return hyps.contains (mkApp (← mkPropNotOp) (← mkNatLtExpr pred_n op2))
 | none =>
    let some n := isIntValue? op1 | return false
    let pred_n ← evalBinIntOp Int.sub n 1
    return hyps.contains (mkApp (← mkPropNotOp) (← mkIntLtExpr pred_n op2))

/-- Apply the following simplification/normalization rules on `LT.lt` :
     - e1 < e2 ==> False (if e1 =ₚₜᵣ e2)
     - e < 0 ==> False (if Type(e) = Nat)
     - 0 < -e ==> e < 0 (if Type(e) = Int)
     - N1 < N2 ==> N1 "<" N2
     - N < e ==> False (if ¬ (N - 1 < e) := _ ∈ hypothesisContext.hypothesisMap ∧ Type(e) ∈ [Nat, Int])
     - e < 1 ==> 0 = e (if Type(e) = Nat)
     - a + b < a | b + a < a ==> False (if Type(a) = Nat)
     - N + e < e ==> False (if N > 0 ∧ Type(e) = Int)
     - N + e < e ==> True (if N < 0 ∧ Type(e) = Int)
     - a + b < a | b + a < a ==> False (if Type(a) = Int ∧ geqZeroIntInHyps b)
     - a + b < a | b + a < a ==> True (if Type(a) = Int ∧ ltZeroIntInHyps b)
     - e < N + e ==> True (if N > 0 ∧ Type(N) ∈ [Nat, Int])
     - e < N + e ==> False (if N < 0 ∧ Type(N) = Int)
     - a < a + b | a < b + a ==> False (if Type(a) = Nat ∧ eqZeroNatInHyps b)
     - a < a + b | a < b + a ==> True (if Type(a) = Nat ∧ gtZeroNatInHyps b)
     - a < a + b | a < b + a ==> False (if Type(a) = Int ∧ leqZeroIntInHyps b)
     - a < a + b | a < b + a ==> True (if Type(a) = Int ∧ gtZeroIntInHyps b)
     - N1 + a < N2 ==> False (if Type(a) = Nat ∧ N2 ≤ N1)
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Nat ∧ N2 > N1)
     - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Int)
     - N1 < N2 + a ==> True (if Type(a) = Nat ∧ N1 < N2)
     - N1 < N2 + a ==> N1 "-" N2 < a (if Type(a) = Nat ∧ N1 ≥ N2)
     - N1 < N2 + a ==> N1 "-" N2 < a  (if Type(a) = Int)
     - N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])
     - a < 1 + b ==> ¬ (b < a) (if Type(a) ∈ [Nat, Int])
   The simplifications are only applied when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LT.lt.
   Do nothing if operator is partially applied (i.e., args.size < 4)
-/
def optimizeLT (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (mkAppN f args)
 if args.size != 4 then return (mkAppN f args)
 -- args[0] is sort parameter
 -- args[1] LT instance
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if (exprEq op1 op2) then return (← mkPropFalse)
 if (isZeroNat op2) then return (← mkPropFalse)
 if let some r ← intZeroLtNorm? op1 op2 then return r
 if let some r ← cstLTProp? op1 op2 then return r
 if ← predCstLTInHyp op1 op2 then return (← mkPropFalse)
 if (isOneNat op2) then return (← mkNatEqExpr (← mkNatLitExpr 0) op1)
 if let some r ← intRelLeftReduce? op1 op2 then return r
 if let some r ← intRelRightReduce? op1 op2 then return r
 if let some r ← natRelLeftReduce? op1 op2 then return r
 if let some r ← natRelRightReduce? op1 op2 then return r
 if let some r ← addNatLeftLtReduce? op1 op2 then return r
 if let some r ← addNatRightLtReduce? op1 op2 then return r
 if let some r ← addIntLeftLtReduce? op1 op2 then return r
 if let some r ← addIntRightLtReduce? op1 op2 then return r
 if let some r ← addNatBothReduce? op1 op2 then return r
 if let some r ← addIntBothReduce? op1 op2 then return r
 if let some r ← intLtNorm? op1 op2 then return r
 if let some r ← natLtNorm? op1 op2 then return r
 return mkAppN f args

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
     setRestart
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' := mkApp2 (← mkNatAddOp) (← mkNatLitExpr leftValue) e2
     let op2' := mkApp2 (← mkNatAddOp) (← mkNatLitExpr rightValue) e4
     return mkApp4 f args[0]! args[1]! op1' op2'

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
     setRestart
     let minValue := min n1 n2
     let leftValue := n1 - minValue
     let rightValue := n2 - minValue
     let op1' := mkApp2 (← mkIntAddOp) (← mkIntLitExpr leftValue) e2
     let op2' := mkApp2 (← mkIntAddOp) (← mkIntLitExpr rightValue) e4
     return mkApp4 f args[0]! args[1]! op1' op2'


/-- Apply the following snormalization rule on `LE.le` :
     - e1 ≤ e2 ==> ¬ (e2 < e1)

   This normalization rule is applied only when isOpaqueRelational predicate is satisfied
   Assume that f = Expr.const ``LE.le.
-/
def optimizeLE (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return (mkAppN f args)
 if args.size == 4 then
   -- args[0] is sort parameter
   -- args[1] Le instance
   -- args[2] left operand
   -- args[3] right operand
   let le_type := args[0]!
   let op1 := args[2]!
   let op2 := args[3]!
   setRestart
   mkNotLtExpr le_type op2 op1
 else if args.size == 2 then
   setRestart
   -- we need to return a lambda term here, i.e.,
   -- λ e1 e2 => ¬ (e2 < e1)
   let le_type := args[0]!
   let body ← mkNotLtExpr le_type (mkBVar 0) (mkBVar 1)
   let lam1 := mkLambda `y BinderInfo.default le_type body
   return mkLambda `x BinderInfo.default le_type lam1
 else throwEnvError "optimizeLE: at least 2 arguments expected but got {reprStr args}"

 where
   mkNotLtExpr (t : Expr) (op1 : Expr) (op2 : Expr) : TranslateEnvT Expr := do
     let ltInst ← findLtInstance t
     let ltExpr := mkApp4 (← mkLtOp) t ltInst op1 op2
     return mkApp (← mkPropNotOp) ltExpr

   findLtInstance (t : Expr) : TranslateEnvT Expr := do
     let some ltInst ← trySynthConstraintInstance? (mkApp (← mkLTConst) t)
       | throwEnvError "optimizeLE: synthesize instance for [LT {reprStr t} cannot be found"
     return ltInst

/-- Apply simplification and normalization rules on `LE.le` and `LT.lt` :
-/
def optimizeRelational? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
  | ``LE.le => optimizeLE f args
  | ``LT.lt => optimizeLT f args
  | _ => return none


end Solver.Optimize
