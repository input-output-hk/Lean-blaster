import Lean
import Blaster.Optimize.Env.HashConsing

open Lean Meta Blaster.Data.HashMap

namespace Blaster.Optimize

abbrev ReplaceCache := HashMap PtrExpr Expr

@[always_inline, inline]
private unsafe def replaceSharedAux (re : Expr) (fn : Expr → TranslateEnvT (Option Expr)) (resolveMVars := false) : TranslateEnvT Expr := do
 let rec @[specialize] go (cur : Expr) (isResult : Bool) (stk : Array HashConsStack) (cache : ReplaceCache) : TranslateEnvT Expr := do
  if isResult then
    if stk.usize > 0 then
      let topIdx := stk.usize - 1
      let next := stk.uget topIdx lcProof
      match next with
      | .WaitAppFun e a =>
           let stk := stk.uset topIdx (.WaitAppArg e cur) lcProof
           go a false stk cache
      | .WaitAppArg e f =>
           let r' ← e.updateAppExpr! f cur
           go r' true stk.pop (cache.insert e r')
      | .WaitForallType e b =>
           let stk := stk.uset topIdx (.WaitForallBody e cur) lcProof
           go b false stk cache
      | .WaitForallBody e t =>
           let r' ← e.updateForallExpr! t cur
           go r' true stk.pop (cache.insert e r')
      | .WaitLambdaType e b =>
           let stk := stk.uset topIdx (.WaitLambdaBody e cur) lcProof
           go b false stk cache
      | .WaitLambdaBody e t =>
           let r' ← e.updateLambdaExpr! t cur
           go r' true stk.pop (cache.insert e r')
      | .WaitLetType e v b =>
           let stk := stk.uset topIdx (.WaitLetValue e cur b) lcProof
           go v false stk cache
      | .WaitLetValue e t b =>
           let stk := stk.uset topIdx (.WaitLetBody e t cur) lcProof
           go b false stk cache
      | .WaitLetBody e t v =>
           let r' ← e.updateLetExpr! t v cur
           go r' true stk.pop (cache.insert e r')
      | .WaitMData e =>
           let r' ← e.updateMDataExpr! cur
           go r' true stk.pop (cache.insert e r')
      | .WaitProjExpr e =>
           let r' ← e.updateProjExpr! cur
           go r' true stk.pop (cache.insert e r')
    else return cur
  else
    let cached := cache.getD cur instCacheMiss
    if !exprEq cached instCacheMiss then go cached true stk cache
    else
      if let some r' ← fn cur then
        go r' true stk (cache.insert cur r')
      else
       match cur with
       | .mvar .. =>
           if resolveMVars then
             let r ← getMVarValue cur
             go r false stk cache
           else go cur true stk cache
       | .bvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
            go cur true stk cache
       | .app f a =>
            let stk := stk.push (.WaitAppFun cur a)
            go f false stk cache
       | .letE _ t v b _ =>
            let stk := stk.push (.WaitLetType cur v b)
            go t false stk cache
       | .forallE _ t b _ =>
            let stk := stk.push (.WaitForallType cur b)
            go t false stk cache
       | .lam _ t b _ =>
            let stk := stk.push (.WaitLambdaType cur b)
            go t false stk cache
       | .mdata _ b =>
            let stk := stk.push (.WaitMData cur)
            go b false stk cache
       | .proj _ _ b =>
            let stk := stk.push (.WaitProjExpr cur)
            go b false stk cache
 go re false (Array.emptyWithCapacity re.approxDepth.toNat) (HashMap.emptyWithCapacity 64)

/--
Similar to `replace` but assume the input is maximally shared and ensure that the result is also maximally shared.
When flag `resolveMVars` is set resolve mvars with their assignment.
-/
def replaceShared (e : Expr) (fn : Expr → TranslateEnvT (Option Expr)) (resolveMVars := false) : TranslateEnvT Expr :=
  unsafe replaceSharedAux e fn resolveMVars

end Blaster.Optimize
