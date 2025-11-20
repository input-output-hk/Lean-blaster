import Lean
import Solver.Optimize.Rewriting.OptimizeEq
import Solver.Optimize.Rewriting.OptimizeRelational
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `Nat.add` :
     - 0 + n ==> n
     - N1 + N2 ===> N1 "+" N2
     - N1 + (N2 + n) ==> (N1 "+" N2) + n
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Nat.add.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.add` expected at this stage)
-/
def optimizeNatAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatAdd: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ =>  return op2
 | some n1, some n2 => evalBinNatOp Nat.add n1 n2
 | nv1,  _ =>
    if let some r ← cstAddProp? nv1 op2 then return r
    return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "+" N2) + n)` when
      `mv1 := some N1 ∧ op2 := N2 + n`.
      Otherwise `none`
   -/
   cstAddProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, (NatCstOpInfo.NatAddExpr n2 e2) => return (mkApp2 f (← evalBinNatOp Nat.add n1 n2) e2)
    | _, _ => return none


/-- Apply the following simplification/normalization rules on `Nat.sub` :
     - n1 - n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - 0 - n ==> 0
     - n - 0 ==> n
     - N1 - N2 ==> N1 "-" N2
     - N1 - (N2 + n) ==> (N1 "-" N2) - n
     - (N1 - n) - N2 ==> (N1 "-" N2) - n
     - (n - N1) - N2 ==> n - (N1 "+" N2)
     - (N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)
   Assume that f = Expr.const ``Nat.sub.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.sub` expected at this stage)
-/
def optimizeNatSub (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatSub: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if exprEq op1 op2 then return (← mkNatLitExpr 0)
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _
 | _, some 0 => return op1
 | some n1, some n2 => evalBinNatOp Nat.sub n1 n2
 | nv1, nv2 =>
   if let some r ← cstSubPropRight? nv1 op2 then return r
   if let some r ← cstSubPropLeft? op1 nv2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2` return `some ((N1 "-" N2) - n)` when
      `mv1 := some N1 ∧ op2 := (N2 + n)`. Otherwise `none`.
   -/
   cstSubPropRight? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, NatCstOpInfo.NatAddExpr n2 e2 =>
        setRestart
        return mkApp2 f (← evalBinNatOp Nat.sub n1 n2) e2
    | _, _ => return none

   /- Given `op1` and `mv2`,
       - return `some ((N1 "-" N2) - n)` when `op1 := (N1 - n) ∧ mv2 := some N2`
       - return `some (n - (N1 "+" N2))` when `op1 := (n - N1) ∧ mv2 := some N2`
       - return `some ((N1 "-" N2) + n)` when `op1 := N1 + n ∧ mv2 := some N2 ∧ N1 ≥ N2`
      Otherwise `none`
   -/
   cstSubPropLeft? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
     match mv2 with
     | some n2 =>
          match toNatCstOpExpr? op1 with
          | some (NatCstOpInfo.NatSubLeftExpr n1 e1) =>
              setRestart
              return mkApp2 f (← evalBinNatOp Nat.sub n1 n2) e1
          | some (NatCstOpInfo.NatSubRightExpr e1 n1) =>
              -- no need to restart here
              return (mkApp2 f e1 (← evalBinNatOp Nat.add n1 n2))
          | some (NatCstOpInfo.NatAddExpr n1 e1) =>
              if Nat.ble n2 n1 then
                setRestart
                return mkApp2 (← mkNatAddOp) (← evalBinNatOp Nat.sub n1 n2) e1
              else return none
          | _ => return none
     | _ => return none

-- /-- TODO: Apply the following advanced constant propagation rules on `Nat.add` and `Nat.sub`:
--      - (N1 + n1) + (N2 + n2) ==> (N1 "+" N2) + (n1 + n2) (TODO)
--      - (N1 - n1) - (N2 - n2) ==> (N1 "-" N2) + (n2 - n1) (TODO)
--      - (N1 - n1) - (n2 - N2) ==> (N1 "+" N2) - (n1 + n2) (TODO)
--      - (n1 - N1) - (N2 - n2) ==> (n1 + n2) - ("N1 "+" N2) (TODO)
--      - (n1 - N1) - (n2 - N2) ==> ("N2 "-" N1) + (n1 - n2) (TODO)
--    NOTE: `(x - y) + (p + q)` is normalized as `(p + q) + (x - y)` via `reorderArgs`
-- -/

/-- Apply the following simplification/normalization rules on `Nat.pow` :
     - n ^ 0 ==> 1
     - n ^ 1 ==> n
     - 0 ^ n ==> 0 (if ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap)
     - 0 ^ n ==> 1 (if n = 0 := _ ∈ hypothesisContext.hypothesisMap)
     - 1 ^ n ==> 1
     - N1 ^ N2 ==> N1 "^" N2
     - (n ^ N1) ^ N2 ==> n ^ (N1 * N2)
     - (N1 ^ m1) * (N1 ^ m2) ==> n ^ (m1 + m2)
   Assume that f = Expr.const ``Nat.pow.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.pow` expected at this stage)
-/
def optimizeNatPow (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatPow: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
  -- n ^ 0 ==> 1
 | _, some 0 => return (← mkNatLitExpr 1)
  -- n ^ 1 ==> n
 | _, some 1 => return op1
 | some 0, some n2 =>
    -- 0 ^ 0 ==> 1
     if n2 = 0 then return (← mkNatLitExpr 1)
     -- 0 ^ N2 ==> 0 (N2 ≠ 0 from first match case)
     else return (← mkNatLitExpr 0)
  -- 1 ^ N2 ==> 1
 | some 1, _ => return (← mkNatLitExpr 1)
 -- N1 ^ N2 ==> N1 "^" N2
 | some n1, some n2 => evalBinNatOp Nat.pow n1 n2
 | _, _ =>
   if let some r ← powOfPowerReduceExpr? op1 op2 then return r
   if let some r ← zeroPowerReduceExpr? op1 op2 then return r
   if let some r ← sameBaseReduceExpr? op1 op2 then return r
   if let some r ← onePowerReduceExpr? op1 op2 then return r
   return (mkApp2 f op1 op2)

 where
   /-- Given `e1` and `e2` corresponding to the operands for `Nat.pow`,
       return `some e1'^(m1*m2)` only when `e1 := e1' ^ m1` and `e2 := m2`
   -/
   powOfPowerReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e1 with
    | some (base, exp) =>
       setRestart
       let mulExpr := mkApp2 (← mkNatMulOp) exp e2
       return mkApp2 (← mkNatPowOp) base mulExpr
    | none => return none

   /-- Given `e1` and `e2` corresponding to the first and second operands respectively,
       return some e1^(m1+m2) only if `e1 := base ^ m1` and `e2 := base ^ m2`
   -/
   sameBaseReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e1, natPow? e2 with
    | some (base1, exp1), some (base2, exp2) =>
       if exprEq base1 base2 then
         setRestart
         let addExpr := mkApp2 (← mkNatAddOp) exp1 exp2
         return mkApp2 (← mkNatPowOp) base1 addExpr
       return none
    | _, _ => return none

   /-- Given `e1` (base) and `e2` (exponent), return `some 0` when `e1 := 0` and `e2 ≠ 0`.
       This handles the rule `0 ^ n ==> 0` for non-constant exponents (when n ≠ 0).
       Also return `some 1` when `e1 := 0` and `e2 = 0` in hypotheses.
       This handles the rule `0 ^ n ==> 1` for non-constant exponents (when n = 0).
   -/
   zeroPowerReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match isNatValue? e1 with
    | some 0 =>
        if (← zeroEqNatInHyps e2) then return (← mkNatLitExpr 1)
        else if (← nonZeroNatInHyps e2) then return (← mkNatLitExpr 0)
        else return none
    | _ => return none

   /-- Given `e1` (base) and `e2` (exponent), return `some 1` when `e1 := 1`.
       This handles the rule `1 ^ n ==> 1` for non-constant exponents.
   -/
   onePowerReduceExpr? (e1 : Expr) (_e2 : Expr) : TranslateEnvT (Option Expr) := do
    match isNatValue? e1 with
    | some 1 => return (← mkNatLitExpr 1)
    | _ => return none

/-- Apply the following simplification/normalization rules on `Nat.mul` :
     - 0 * n ==> 0
     - 1 * n ==> n
     - N1 + N2 ==> N1 "*" N2
     - N1 * (N2 * n) ==> (N1 "*" N2) * n
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)
     - (a ^ n) * (b ^ n) ==> (a * b) ^ n
     - n * n^m ===> n ^ (m + 1)
   Assume that f = Expr.const ``Nat.mul.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.mul` expected at this stage)
-/
def optimizeNatMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatMul: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ => return op1
 | some 1, _ => return op2
 | some n1, some n2 => evalBinNatOp Nat.mul n1 n2
 | nv1, _ =>
   if let some r ← cstMulProp? nv1 op2 then return r
   if let some r ← samePowBaseReduceExpr? op1 op2 then return r
   if let some r ← samePowExpReduceExpr? op1 op2 then return r
   if let some r ← mulPowReduceExpr? op1 op2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "*" N2) * n)`
      when `mv1 := some N1 ∧ op2 := (N2 * n)`
      Otherwise `none`.
   -/
   cstMulProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match mv1, toNatCstOpExpr? op2 with
     | some n1, some (NatCstOpInfo.NatMulExpr n2 e2) =>
         return (mkApp2 f (← evalBinNatOp Nat.mul n1 n2) e2)
     | _, _ => return none

   /-- Given `e1` and `e2` corresponding to the operands for `Nat.mul`,
       return some e1^(m + 1) only when `e2 := e1 ^ m`
   -/
   mulPowReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e2 with
    | some (op1, op2) =>
       if exprEq e1 op1 then
         setRestart
         let addExpr := mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) op2
         return mkApp2 (← mkNatPowOp) e1 addExpr
       return none
    | none => return none

   /-- Given `e1` and `e2` corresponding to the operands for `Nat.mul`,
       return some base^(m + n) only when `e1 := base ^ m` and `e2 := base ^ n`
       where base is the same in both expressions.
   -/
   samePowBaseReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e1, natPow? e2 with
    | some (base1, exp1), some (base2, exp2) =>
       if exprEq base1 base2 then
         setRestart
         let addExpr := mkApp2 (← mkNatAddOp) exp1 exp2
         return mkApp2 (← mkNatPowOp) base1 addExpr
       return none
    | _, _ => return none

   /-- Given `e1` and `e2` corresponding to the operands for `Nat.mul`,
       return some (base1 * base2)^n only when `e1 := base1 ^ n` and `e2 := base2 ^ n`
       where the exponent is the same in both expressions.
   -/
   samePowExpReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e1, natPow? e2 with
    | some (base1, exp1), some (base2, exp2) =>
       if exprEq exp1 exp2 then
         setRestart
         let mulExpr := mkApp2 (← mkNatMulOp) base1 base2
         return mkApp2 (← mkNatPowOp) mulExpr exp1
       return none
    | _, _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m ∧
        (0 < m := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap); or
     - `e1 := n * m` ∧ e2 = m ∧
        (0 < m := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap);
    Otherwise, return none.
-/
def mulNatDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match natMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 then if (← nonZeroNatInHyps e2) then return some op2
     if exprEq op2 e2 then if (← nonZeroNatInHyps e2) then return some op1
     return none
  | none => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some 1` only when the following conditions are satisfied:
      - e1 =ₚₜᵣ e2 ∧
      - 0 < e1 := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = e1) := _ ∈ hypothesisContext.hypothesisMap
    Otherwise, return none.
-/
def natDivSelfReduce? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if !(exprEq e1 e2) then return none
  if (← nonZeroNatInHyps e1)
  then return ← mkNatLitExpr 1
  else return none

/-- Apply the following simplification/normalization rules on `Nat.div` :
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - (n / N1) / N2 ==> n / (N1 "*" N2)
     - (N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0 ∧ Nat.gcd N1 N2 ≠ 1)
     - n / n ==> 1 (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
                       ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap)
     - (m * n) / m | (n * m) / m ==> n (if 0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
                                           ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap)

   Assume that f = Expr.const ``Nat.div.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.div` expected at this stage)

-/
def optimizeNatDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | _, some 0 => return op2
 | _, some 1
 | some 0, _ => return op1
 | some n1, some n2 => evalBinNatOp Nat.div n1 n2
 | _, nv2 =>
   if let some r ← cstDivProp? op1 nv2 then return r
   if let some r ← natDivSelfReduce? op1 op2 then return r
   if let some r ← mulNatDivReduceExpr? op1 op2 then return r
   return (mkApp2 f op1 op2)

 where

   /- Given `op1` and `mv2`,
        - return `some (n / (N1 "*" N2))` when `op1 := (n / N1) ∧ mv2 := some N2`
        - return `some (((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2))`
          when `op1 := (N1 * n) ∧ mv2 := some N2`
      Otherwise `none`.
      Assumes that N2 > 0
   -/
   cstDivProp? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
     match mv2 with
     | some n2 =>
         match toNatCstOpExpr? op1 with
         | some (NatCstOpInfo.NatDivRightExpr e1 n1) =>
             -- no need to restart here
             return (mkApp2 f e1 (← evalBinNatOp Nat.mul n1 n2))
         | some (NatCstOpInfo.NatMulExpr n1 e1) =>
             let gcd := if n1 < n2 then Nat.gcd n1 n2 else Nat.gcd n2 n1
             if gcd == 1 then return none
             setRestart
             let mulExpr := mkApp2 (← mkNatMulOp) (← evalBinNatOp Nat.div n1 gcd) e1
             return mkApp2 f mulExpr (← evalBinNatOp Nat.div n2 gcd)
         | _ => return none
     | _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.mod` (i.e., `e1 % e2`),
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def natModToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if exprEq e1 e2 then return (some (← mkNatLitExpr 0))
  match natMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 || exprEq op2 e2 then return (← mkNatLitExpr 0)
     return none
  | none => return none

/-- Apply the following simplification/normalization rules on `Nat.mod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Nat.mod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.mod` expected at this stage)
-/

def optimizeNatMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | _, some 0 => return op1
 | _, some 1 => mkNatLitExpr 0
 | some 0, _ => return op1
 | some n1, some n2 => evalBinNatOp Nat.mod n1 n2
 | _, nv2 =>
   if let some r ← cstModProp? op1 nv2 then return r
   if let some r ← natModToZeroExpr? op1 op2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `op1` and `mv2`, return `some 0`
      when `op1 := N1 * n ∧ mv2 := N2 ∧ N1 % N2 = 0`
      Otherwise `none`.
      Assumes that N2 > 0
   -/
   cstModProp? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
    match toNatCstOpExpr? op1, mv2 with
    | some (NatCstOpInfo.NatMulExpr n1 _e1), some n2 =>
        if Nat.mod n1 n2 == 0
        then some <$> mkNatLitExpr 0
        else return none
    | _, _ => return none

/-- Normalize `Nat.beq x y` to `x == y` only when option normalizeFunCall is set to `true`.
    Assume that f = Expr.const ``Nat.beq
    NOTE: This normalization rule is still required here mainly
    to properly handle the case where another rec function is equivalent to `Nat.beq`
--/
def optimizeNatBeq (f : Expr) (b_args : Array Expr) : TranslateEnvT Expr := do
  if !(← isOptimizeRecCall) then return mkAppN f b_args
  setRestart
  return mkAppN (← mkNatBEqOp) b_args

/-- Normalize `Nat.ble x y` to `decide' (x ≤ y)` only when option normalizeFunCall is set to `true`.
    Assume that f = Expr.const ``Nat.ble
    NOTE: This normalization rule is still required here mainly
    to properly handle the case where another rec function is equivalent to `Nat.beq`
-/
def optimizeNatble (f : Expr) (b_args : Array Expr) : TranslateEnvT Expr := do
  if !(← isOptimizeRecCall) then return mkAppN f b_args
  setRestart
  let leExpr := mkAppN (← mkNatLeOp) b_args
  return mkApp (← mkSolverDecideConst) leExpr

/-- Apply simplification/normalization rules on `Nat` operators. -/
@[always_inline, inline]
def optimizeNat? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``Nat.add => optimizeNatAdd f args
  | ``Nat.sub => optimizeNatSub f args
  | ``Nat.mul => optimizeNatMul f args
  | ``Nat.div => optimizeNatDiv f args
  | ``Nat.mod => optimizeNatMod f args
  | ``Nat.beq => optimizeNatBeq f args
  | ``Nat.ble => optimizeNatble f args
  | ``Nat.pow => optimizeNatPow f args
  | _=> return none

end Solver.Optimize
