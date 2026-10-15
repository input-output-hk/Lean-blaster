import Lean
import Blaster.Optimize.Expr
import Blaster.Optimize.Env

open Lean Meta

namespace Blaster.Optimize

/-- Apply the following simplification/normalization rules on `OfNat.ofNat` :
     - OfNat.ofNat Nat n ==> n
     - OfNat.ofNat Int n ==> Int.ofNat n
    An error is triggered when args.size ≠ 3 (i.e., only fully applied `OfNat.ofNat` expected at this stage)
    NOTE: we need to remove setRestart once the dedicated ofNat functions have been opacified via BitVec support.
-/
def optimizeOfNat? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const ``OfNat.ofNat _ := f | return none
  if args.size != 3 then throwEnvError "optimizeOfNat: exactly three arguments expected"
  -- args[0] OfNat sort
  -- args[1] OfNat argument
  -- args[2] OfNat instance
  let op1 := args[0]!
  let op2 := args[1]!
  match op1 with
  | Expr.const ``Nat _ => return op2
  | Expr.const ``Int _ => mkAppExpr (← mkIntOfNat) op2
  | Expr.const ``UInt8 _ => setRestart; mkAppExpr (← mkUInt8OfNat) op2
  | Expr.const ``UInt16 _ => setRestart; mkAppExpr (← mkUInt16OfNat) op2
  | Expr.const ``UInt32 _ => setRestart; mkAppExpr (← mkUInt32OfNat) op2
  | Expr.const ``UInt64 _ => setRestart; mkAppExpr (← mkUInt64OfNat) op2
  | Expr.const ``USize _ => setRestart; mkAppExpr (← mkUSizeOfNat) op2
  | Expr.const ``Int8 _ => setRestart; mkAppExpr (← mkInt8OfNat) op2
  | Expr.const ``Int16 _ => setRestart; mkAppExpr (← mkInt16OfNat) op2
  | Expr.const ``Int32 _ => setRestart; mkAppExpr (← mkInt32OfNat) op2
  | Expr.const ``Int64 _ => setRestart; mkAppExpr (← mkInt64OfNat) op2
  | Expr.const ``ISize _ => setRestart; mkAppExpr (← mkISizeOfNat) op2
  | Expr.app (Expr.const ``Fin _) n =>
        let neZeroInst := args[2]!.getAppArgs[1]!
        setRestart; mkApp3Expr (← mkFinOfNat) n neZeroInst op2
  | Expr.app (Expr.const ``BitVec _) n => setRestart; mkApp2Expr (← mkBitVecOfNat) n op2
  | _ => return none

end Blaster.Optimize
