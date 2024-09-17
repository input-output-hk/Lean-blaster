import Lean
import Solver.Optimize.OptimizeEq
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `Nat.add` :
     - 0 + n ==> n
     - N1 + (N2 + n) ==> (N1 "+" N2) + n
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Nat.add.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.add` on constant values are handled via `reduceApp`.
-/
partial def optimizeNatAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderNatOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match (isNatValue? op1) with
   | some 0 => pure op2
   | some n1 =>
       match (toNatCstOpExpr? op2) with
       | some (NatCstOpInfo.NatAddExpr n2 e2) => mkAppExpr f #[(← evalBinNatOp Nat.add n1 n2), e2]
       | some _ | none => mkAppExpr f opArgs
   | none => mkAppExpr f opArgs
 else mkAppExpr f args


/-- Apply the following simplification/normalization rules on `Nat.sub` :
     - n1 - n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - 0 - n ==> 0
     - n - 0 ==> n
     - N1 - (N2 + n) ==> (N1 "-" N2) - n
     - (N1 - n) - N2 ==> (N1 "-" N2) - n
     - (n - N1) - N2 ==> n - (N1 "+" N2)
     - (N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)
   Assume that f = Expr.const ``Nat.sub.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.sub` on constant values are handled via `reduceApp`.
   TODO: consider additional simplification rules
-/
partial def optimizeNatSub (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2
 then
   let op1 := args[0]!
   let op2 := args[1]!
   if (← exprEq op1 op2)
   then mkNatLitExpr 0
   else
     match (isNatValue? op1), (isNatValue? op2) with
     | some 0, _ | _, some 0 => pure op1
     | some n1, _ =>
          match (toNatCstOpExpr? op2) with
          | some (NatCstOpInfo.NatAddExpr n2 e2) => optimizeNatSub f #[(← evalBinNatOp Nat.sub n1 n2), e2]
          | some _ | none => mkAppExpr f args
     | _, some n2 =>
          match (toNatCstOpExpr? op1) with
          | some (NatCstOpInfo.NatSubLeftExpr n1 e1) => optimizeNatSub f #[(← evalBinNatOp Nat.sub n1 n2), e1]
          | some (NatCstOpInfo.NatSubRightExpr e1 n1) => mkAppExpr f #[e1, (← evalBinNatOp Nat.add n1 n2)]
          | some (NatCstOpInfo.NatAddExpr n1 e1) =>
             if Nat.ble n2 n1
             then optimizeNatAdd (← mkNatAddOp) #[(← evalBinNatOp Nat.sub n1 n2), e1]
             else mkAppExpr f args
          | some _ | none => mkAppExpr f args
     | _, _ => mkAppExpr f args
  else mkAppExpr f args

-- /-- TODO: Apply the following advanced constant propagation rules on `Nat.add` and `Nat.sub`:
--      - (N1 + n1) + (N2 + n2) ==> (N1 "+" N2) + (n1 + n2) (TODO)
--      - (N1 - n1) - (N2 - n2) ==> (N1 "-" N2) + (n2 - n1) (TODO)
--      - (N1 - n1) - (n2 - N2) ==> (N1 "+" N2) - (n1 + n2) (TODO)
--      - (n1 - N1) - (N2 - n2) ==> (n1 + n2) - ("N1 "+" N2) (TODO)
--      - (n1 - N1) - (n2 - N2) ==> ("N2 "-" N1) + (n1 - n2) (TODO)
--    NOTE: `(x - y) + (p + q)` is normalized as `(p + q) + (x - y)` via `reorderArgs`
-- -/


/-- Apply the following simplification/normalization rules on `Nat.mul` :
     - 0 * n ==> 0
     - 1 * n ==> n
     - N1 * (N2 * n) ==> (N1 "*" N2) * n
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Nat.mul.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.mul` on constant values are handled via `reduceApp`.
-/
def optimizeNatMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let opArgs ← reorderNatOp args -- error triggered when args.size ≠ 2
   let op1 := opArgs[0]!
   let op2 := opArgs[1]!
   match (isNatValue? op1) with
   | some 0 => return op1
   | some 1 => return op2
   | some n1 =>
       match (toNatCstOpExpr? op2) with
       | some (NatCstOpInfo.NatMulExpr n2 e2) => mkAppExpr f #[(← evalBinNatOp Nat.mul n1 n2), e2]
       | some _ | none => mkAppExpr f opArgs
   | none => mkAppExpr f opArgs
 else mkAppExpr f args


/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def mulDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match toNatMulExpr? e1 with
  | some (_, mul_ops) =>
      let op1 := mul_ops[0]!
      let op2 := mul_ops[1]!
      if (← exprEq op1 e2)
      then return some op2
      else if (← exprEq op2 e2)
           then return some op1
           else return none
  | none => return none


/-- Apply the following simplification/normalization rules on `Nat.div` :
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - (n / N1) / N2 ==> n / (N1 "*" N2) (if N1 > 0 ∧ N2 > 0)
     - (N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0)
     - (m * n) / m | (n * m) / m ==> n

   Assume that f = Expr.const ``Nat.div.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.div` on constant values are handled via `reduceApp`.
-/
partial def optimizeNatDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let op1 := args[0]!
   let op2 := args[1]!
   match (isNatValue? op1), (isNatValue? op2) with
   | _, some 0 => return op2
   | _, some 1 | some 0, _ => return op1
   | _, some n2 =>
       match (toNatCstOpExpr? op1) with
       | some (NatCstOpInfo.NatDivRightExpr e1 n1) => mkAppExpr f #[e1, (← evalBinNatOp Nat.mul n1 n2)]
       | some (NatCstOpInfo.NatMulExpr n1 e1) =>
           let gcd := if n1 < n2 then Nat.gcd n1 n2 else Nat.gcd n2 n1
           if gcd != 1
           then
             let mulExpr ← optimizeNatMul (← mkNatMulOp) #[(← evalBinNatOp Nat.div n1 gcd), e1]
             optimizeNatDiv f #[mulExpr, (← evalBinNatOp Nat.div n2 gcd)]
           else mkAppExpr f args
       | some _ | none => mkAppExpr f args
   |_, _ =>
       match (← mulDivReduceExpr? op1 op2) with
       | some r => pure r
       | none => mkAppExpr f args
 else mkAppExpr f args



/-- Given `e1` and `e2` corresponding to the operands for `Nat.mod` (i.e., `e1 % e2`),
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def modToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if (← exprEq e1 e2)
  then some <$> (mkNatLitExpr 0)
  else
    match toNatMulExpr? e1 with
    | some (_, mul_ops) =>
        let op1 := mul_ops[0]!
        let op2 := mul_ops[1]!
        if (← exprEq op1 e2 <||> exprEq op2 e2)
        then some <$> (mkNatLitExpr 0)
        else return none
    | none => return none

/-- Apply the following simplification/normalization rules on `Nat.mod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0 ∧ N2 > 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Nat.mod.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.mod` on constant values are handled via `reduceApp`.
-/

def optimizeNatMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 2 then
   let op1 := args[0]!
   let op2 := args[1]!
   match (isNatValue? op1), (isNatValue? op2) with
   | _, some 0 => return op1
   | _, some 1 | some 0, _ => mkNatLitExpr 0
   | _, some n2 =>
       match (toNatCstOpExpr? op1) with
       | some (NatCstOpInfo.NatMulExpr n1 _e1) =>
          if Nat.mod n1 n2 == 0
          then mkNatLitExpr 0
          else mkAppExpr f args
       | some _ | none => mkAppExpr f args
   |_, _ =>
     match (← modToZeroExpr? op1 op2) with
     | some r => pure r
     | _ => mkAppExpr f args
 else mkAppExpr f args


/-- Normalize `Nat.succ n` to `1 + n`.
    An error is triggered if args.size ≠ 1.
    NOTE: `Nat.succ` on constant values are handled via `reduceApp`.
-/
def optimizeNatSucc (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1
 then optimizeNatAdd (← mkNatAddOp) #[← mkNatLitExpr 1, args[0]!]
 else throwError "optimizeNatSucc: only one argument expected"

/-- Normalize `Nat.pred n` to `n - 1`.
    Do nothing if operator is partially applied (i.e., args.size < 2)
    Assume that f = Expr.const ``Nat.pred.
    NOTE: `Nat.pred` on constant values are handled via `reduceApp`.
-/
def optimizeNatPred (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size == 1
 then optimizeNatSub (← mkNatSubOp) #[args[0]!, ← mkNatLitExpr 1]
 else mkAppExpr f args

/-- Normalize `Nat.beq ops` to `BEq.beq ops`.
-/
def optimizeNatBeq (b_args : Array Expr) : TranslateEnvT Expr := do
  Expr.withApp (← mkNatBeqOp) fun f i_args =>
    optimizeBEq f (i_args ++ b_args)

/-- Apply simplification/normalization rules on Nat operators.
-/
def optimizeNat? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const n _ =>
    match n with
    | ``Nat.add => some <$> optimizeNatAdd f args
    | ``Nat.sub => some <$> optimizeNatSub f args
    | ``Nat.mul => some <$> optimizeNatMul f args
    | ``Nat.div => some <$> optimizeNatDiv f args
    | ``Nat.mod => some <$> optimizeNatMod f args
    | ``Nat.succ => some <$> optimizeNatSucc args
    | ``Nat.pred => some <$> optimizeNatPred f args
    | ``Nat.beq => some <$> optimizeNatBeq args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
