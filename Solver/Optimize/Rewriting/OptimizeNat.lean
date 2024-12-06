import Lean
import Solver.Optimize.Rewriting.OptimizeEq
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

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
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderNatOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 let nv1 := isNatValue? op1
 if let some 0 := nv1 then return op2
 if let some r ← cstAddProp? nv1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "+" N2) + n)` when
      `mv1 := some N1 ∧ op2 := N2 + n`.
      Otherwise `none`
   -/
   cstAddProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, (NatCstOpInfo.NatAddExpr n2 e2) => some <$> mkExpr (mkApp2 f (← evalBinNatOp Nat.add n1 n2) e2)
    | _, _ => return none


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
 if args.size != 2 then return (← mkAppExpr f args)
 let op1 := args[0]!
 let op2 := args[1]!
 if (← exprEq op1 op2) then return (← mkNatLitExpr 0)
 let nv1 := isNatValue? op1
 let nv2 := isNatValue? op2
 if let some 0 := nv1 then return op1
 if let some 0 := nv2 then return op1
 if let some r ← cstSubPropRight? nv1 op2 then return r
 if let some r ← cstSubPropLeft? op1 nv2 then return r
 mkExpr (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2` return `some ((N1 "-" N2) - n)` when
      `mv1 := some N1 ∧ op2 := (N2 + n)`. Otherwise `none`.
   -/
   cstSubPropRight? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, NatCstOpInfo.NatAddExpr n2 e2 =>
        some <$> optimizeNatSub f #[(← evalBinNatOp Nat.sub n1 n2), e2]
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
              some <$> optimizeNatSub f #[(← evalBinNatOp Nat.sub n1 n2), e1]
          | some (NatCstOpInfo.NatSubRightExpr e1 n1) =>
              some <$> mkExpr (mkApp2 f e1 (← evalBinNatOp Nat.add n1 n2))
          | some (NatCstOpInfo.NatAddExpr n1 e1) =>
              if Nat.ble n2 n1 then
                some <$> optimizeNatAdd (← mkNatAddOp) #[(← evalBinNatOp Nat.sub n1 n2), e1]
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
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderNatOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 let nv1 := isNatValue? op1
 if let some 0 := nv1 then return op1
 if let some 1 := nv1 then return op2
 if let some r ← cstMulProp? nv1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "*" N2) * n)`
      when `mv1 := some N1 ∧ op2 := (N2 * n)`
      Otherwise `none`.
   -/
   cstMulProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match mv1, toNatCstOpExpr? op2 with
     | some n1, some (NatCstOpInfo.NatMulExpr n2 e2) =>
         some <$> mkExpr (mkApp2 f (← evalBinNatOp Nat.mul n1 n2) e2)
     | _, _ => return none


/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def mulDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match natMul? e1 with
  | some (op1, op2) =>
     if (← exprEq op1 e2) then return some op2
     if (← exprEq op2 e2) then return some op1
     return none
  | none => return none


/-- Apply the following simplification/normalization rules on `Nat.div` :
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - (n / N1) / N2 ==> n / (N1 "*" N2)
     - (N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0)
     - (m * n) / m | (n * m) / m ==> n

   Assume that f = Expr.const ``Nat.div.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: `Nat.div` on constant values are handled via `reduceApp`.
-/
partial def optimizeNatDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then return (← mkAppExpr f args)
 let op1 := args[0]!
 let op2 := args[1]!
 let nv1 := isNatValue? op1
 let nv2 := isNatValue? op2
 if let some 0 := nv2 then return op2
 if let some 1 := nv2 then return op1
 if let some 0 := nv1 then return op1
 if let some r ← cstDivProp? op1 nv2 then return r
 if let some r ← mulDivReduceExpr? op1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

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
             some <$> mkExpr (mkApp2 f e1 (← evalBinNatOp Nat.mul n1 n2))
         | some (NatCstOpInfo.NatMulExpr n1 e1) =>
             let gcd := if n1 < n2 then Nat.gcd n1 n2 else Nat.gcd n2 n1
             if gcd = 1 then return none
             let mulExpr ← optimizeNatMul (← mkNatMulOp) #[(← evalBinNatOp Nat.div n1 gcd), e1]
             some <$> optimizeNatDiv f #[mulExpr, (← evalBinNatOp Nat.div n2 gcd)]
         | _ => return none
     | _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.mod` (i.e., `e1 % e2`),
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def modToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if (← exprEq e1 e2) then return (some (← mkNatLitExpr 0))
  match natMul? e1 with
  | some (op1, op2) =>
     if (← exprEq op1 e2 <||> exprEq op2 e2) then return (← mkNatLitExpr 0)
     return none
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
 if args.size != 2 then return (← mkAppExpr f args)
 let op1 := args[0]!
 let op2 := args[1]!
 let nv1 := isNatValue? op1
 let nv2 := isNatValue? op2
 if let some 0 := nv2 then return op1
 if let some 1 := nv2 then return (← mkNatLitExpr 0)
 if let some 0 := nv1 then return (← mkNatLitExpr 0)
 if let some r ← cstModProp? op1 nv2 then return r
 if let some r ← modToZeroExpr? op1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

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

/-- Normalize `Nat.succ n` to `1 + n`.
    An error is triggered if args.size ≠ 1.
    NOTE: `Nat.succ` on constant values are handled via `reduceApp`.
-/
def optimizeNatSucc (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwError "optimizeNatSucc: only one argument expected"
 optimizeNatAdd (← mkNatAddOp) #[← mkNatLitExpr 1, args[0]!]

/-- Normalize `Nat.pred n` to `n - 1`.
    An error is triggered if args.size ≠ 1.
    Assume that f = Expr.const ``Nat.pred.
    NOTE: `Nat.pred` on constant values are handled via `reduceApp`.
-/
def optimizeNatPred (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwError "optimizeNatPred: only one argument expected"
 optimizeNatSub (← mkNatSubOp) #[args[0]!, ← mkNatLitExpr 1]


/-- Normalize `Nat.beq ops` to `BEq.beq ops`.
-/
def optimizeNatBeq (b_args : Array Expr) : TranslateEnvT Expr := do
  Expr.withApp (← mkNatEqOp) fun f i_args =>
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
    | ``Nat.pred => some <$> optimizeNatPred args
    | ``Nat.beq => some <$> optimizeNatBeq args
    | _=> pure none
 | _ => pure none

end Solver.Optimize
