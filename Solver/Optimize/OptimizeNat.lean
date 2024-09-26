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
       | some _ => mkAppExpr f opArgs
       | none => mkAppExpr f opArgs
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
          | some _ => mkAppExpr f args
          | none => mkAppExpr f args
     | _, some n2 =>
          match (toNatCstOpExpr? op1) with
          | some (NatCstOpInfo.NatSubLeftExpr n1 e1) => optimizeNatSub f #[(← evalBinNatOp Nat.sub n1 n2), e1]
          | some (NatCstOpInfo.NatSubRightExpr e1 n1) => mkAppExpr f #[e1, (← evalBinNatOp Nat.add n1 n2)]
          | some (NatCstOpInfo.NatAddExpr n1 e1) =>
             if Nat.ble n2 n1
             then optimizeNatAdd (← mkNatAddOp) #[(← evalBinNatOp Nat.sub n1 n2), e1]
             else mkAppExpr f args
          | some _ => mkAppExpr f args
          | none => mkAppExpr f args
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
    | ``Nat.succ => some <$> optimizeNatSucc args
    | ``Nat.pred => some <$> optimizeNatPred f args
    | ``Nat.beq => some <$> optimizeNatBeq args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
