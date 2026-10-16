import Lean
import Blaster.Optimize.Env.HashConsing

open Lean Meta Blaster.Data.HashMap

namespace Blaster.Optimize

abbrev ReplaceEnvT := StateRefT (HashMap PtrExpr Expr) TranslateEnvT

@[always_inline, inline]
def saveReplace (key : PtrExpr) (r : Expr) : ReplaceEnvT Expr := do
  modify fun cache => cache.insert key r|>.insert r r
  return r

@[always_inline, inline]
private unsafe def replaceSharedAux (e : Expr) (fn : Expr → TranslateEnvT (Option Expr)) (resolveMVars := false) : ReplaceEnvT Expr := do
 let rec @[specialize] go (entry : Sum Expr Expr) (stk : Array HashConsStack) : ReplaceEnvT Expr := do
  match entry with
  | Sum.inr r =>
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a =>
             let stk := stk.uset topIdx (.WaitAppArg e r) lcProof
             go (Sum.inl a) stk
        | .WaitAppArg e f =>
             let r' ← saveReplace e (← e.updateAppExpr! f r)
             go (Sum.inr r') stk.pop
        | .WaitForallType e b =>
             let stk := stk.uset topIdx (.WaitForallBody e r) lcProof
             go (Sum.inl b) stk
        | .WaitForallBody e t =>
             let r' ← saveReplace e (← e.updateForallExpr! t r)
             go (Sum.inr r') stk.pop
        | .WaitLambdaType e b =>
             let stk := stk.uset topIdx (.WaitLambdaBody e r) lcProof
             go (Sum.inl b) stk
        | .WaitLambdaBody e t =>
             let r' ← saveReplace e (← e.updateLambdaExpr! t r)
             go (Sum.inr r') stk.pop
        | .WaitLetType e v b =>
             let stk := stk.uset topIdx (.WaitLetValue e r b) lcProof
             go (Sum.inl v) stk
        | .WaitLetValue e t b =>
             let stk := stk.uset topIdx (.WaitLetBody e t r) lcProof
             go (Sum.inl b) stk
        | .WaitLetBody e t v =>
             let r' ← saveReplace e (← e.updateLetExpr! t v r)
             go (Sum.inr r') stk.pop
        | .WaitMData e =>
             let r' ← saveReplace e (← e.updateMDataExpr! r)
             go (Sum.inr r') stk.pop
        | .WaitProjExpr e =>
             let r' ← saveReplace e (← e.updateProjExpr! r)
             go (Sum.inr r') stk.pop
      else return r
  | Sum.inl e =>
      match (← get).get? e with
      | some r => go (Sum.inr r) stk
      | none =>
          if let some r' ← fn e then
            go (Sum.inr (← saveReplace e r')) stk
          else
           match e with
           | .mvar .. =>
               if resolveMVars then
                 let r ← getMVarValue e
                 go (Sum.inl r) stk
               else go (Sum.inr e) stk
           | .bvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
                go (Sum.inr e) stk
           | .app f a =>
                let stk := stk.push (.WaitAppFun e a)
                go (Sum.inl f) stk
           | .letE _ t v b _ =>
                let stk := stk.push (.WaitLetType e v b)
                go (Sum.inl t) stk
           | .forallE _ t b _ =>
                let stk := stk.push (.WaitForallType e b)
                go (Sum.inl t) stk
           | .lam _ t b _ =>
                let stk := stk.push (.WaitLambdaType e b)
                go (Sum.inl t) stk
           | .mdata _ b =>
                let stk := stk.push (.WaitMData e)
                go (Sum.inl b) stk
           | .proj _ _ b =>
                let stk := stk.push (.WaitProjExpr e)
                go (Sum.inl b) stk
 go (Sum.inl e) (Array.emptyWithCapacity e.approxDepth.toNat)

/--
Similar to `replace` but assume the input is maximally shared and ensure that the result is also maximally shared.
When flag `resolveMVars` is set resolve mvars with their assignment.
-/
def replaceShared (e : Expr) (fn : Expr → TranslateEnvT (Option Expr)) (resolveMVars := false) : TranslateEnvT Expr :=
  unsafe replaceSharedAux e fn resolveMVars |>.run' (HashMap.emptyWithCapacity e.approxDepth.toNat)

end Blaster.Optimize
