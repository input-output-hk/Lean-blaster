import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta
namespace Blaster.Optimize

/-- Detect `List.any l (λ x => BEq.beq x k)` or `List.any l (λ x => BEq.beq k x)`
    and rewrite to `List.elem k l`.

    @List.any : {α : Type} → List α → (α → Bool) → Bool
    args[0] = α, args[1] = l, args[2] = f

    @BEq.beq : {α : Type} → [inst : BEq α] → α → α → Bool
    beqArgs[0] = α, beqArgs[1] = inst, beqArgs[2] = lhs, beqArgs[3] = rhs

    @List.elem : {α : Type} → [inst : BEq α] → α → List α → Bool

    Uses definitional equality checking to handle custom types with derived BEq
    instances, where the elaborator may expand (==) into primitive constructs.
-/

def optimizeListAny? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const ``List.any _ := f | return none
  if args.size != 3 then return none
  let α := args[0]!
  let l := args[1]!
  let lam := args[2]!
  let Expr.lam binderName binderType body binderInfo := lam | return none
  withLocalDecl binderName binderInfo binderType λ x => do
    let body := body.instantiate1 x
    let beqType := mkApp (mkConst ``BEq [levelZero]) α
    let inst ← try synthInstance beqType
      catch _ => do
      return none
    let kMVar ← mkFreshExprMVar α
    let rhs_candidate := mkAppN (mkConst ``BEq.beq [levelZero]) #[α, inst, x, kMVar]
    let rhs_matches ← isDefEq body rhs_candidate
    let k ← if rhs_matches then do
        let k ← instantiateMVars kMVar
        pure k
      else do
        let kMVar2 ← mkFreshExprMVar α
        let lhs_candidate := mkAppN (mkConst ``BEq.beq [levelZero]) #[α, inst, kMVar2, x]
        let lhs_matches ← isDefEq body lhs_candidate
        if lhs_matches then do
          let k ← instantiateMVars kMVar2
          pure k
        else do
          return none
    if k.hasLooseBVars then return none
    setRestart
    let u <- getLevel α
    let u' := u.normalize.dec.getD Lean.Level.zero
    return mkAppN (mkConst ``List.elem [u']) #[α, inst, k, l]

end Blaster.Optimize
