import Lean
import Blaster.Optimize.Env.HashConsing

open Lean Meta Blaster.Data.HashMap

namespace Blaster.Optimize

@[always_inline, inline]
private unsafe def saveInitMVarInto (cache : InstCache) (a : Expr) (b : Expr) : InstCache :=
  (cache.insert (mkInstKey a 0) b).insert (mkInstKey b 0) b

private unsafe def instantiateSharedMVarsAux (cur : Expr) (isResult : Bool) (stk : Array HashConsStack) (cache : InstCache) : TranslateEnvT Expr := do
  if isResult then
      let r := cur
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a =>
             let stk := stk.uset topIdx (.WaitAppArg e r) lcProof
             instantiateSharedMVarsAux a false stk cache
        | .WaitAppArg e f =>
             let r' ← e.updateAppExpr! f r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
        | .WaitForallType e b =>
             let stk := stk.uset topIdx (.WaitForallBody e r) lcProof
             instantiateSharedMVarsAux b false stk cache
        | .WaitForallBody e t =>
             let r' ← e.updateForallExpr! t r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
        | .WaitLambdaType e b =>
             let stk := stk.uset topIdx (.WaitLambdaBody e r) lcProof
             instantiateSharedMVarsAux b false stk cache
        | .WaitLambdaBody e t =>
             let r' ← e.updateLambdaExpr! t r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
        | .WaitLetType e v b =>
             let stk := stk.uset topIdx (.WaitLetValue e r b) lcProof
             instantiateSharedMVarsAux v false stk cache
        | .WaitLetValue e t b =>
             let stk := stk.uset topIdx (.WaitLetBody e t r) lcProof
             instantiateSharedMVarsAux b false stk cache
        | .WaitLetBody e t v =>
             let r' ← e.updateLetExpr! t v r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
        | .WaitMData e =>
             let r' ← e.updateMDataExpr! r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
        | .WaitProjExpr e =>
             let r' ← e.updateProjExpr! r
             instantiateSharedMVarsAux r' true stk.pop (saveInitMVarInto cache e r')
      else return r
  else
      let e := cur
      let cached := cache.getD (mkInstKey e 0) instCacheMiss
      if !exprEq cached instCacheMiss then instantiateSharedMVarsAux cached true stk cache
      else
          if e.hasExprMVar then
           match e with
           | .mvar _ =>
                let r ← getMVarValue e
                if r.hasMVar
                then instantiateSharedMVarsAux r false stk cache
                else instantiateSharedMVarsAux r true stk (saveInitMVarInto cache e r)
           | .bvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
                instantiateSharedMVarsAux e true stk (saveInitMVarInto cache e e)
           | .app f a =>
                let stk := stk.push (.WaitAppFun e a)
                instantiateSharedMVarsAux f false stk cache
           | .letE _ t v b _ =>
                let stk := stk.push (.WaitLetType e v b)
                instantiateSharedMVarsAux t false stk cache
           | .forallE _ t b _ =>
                let stk := stk.push (.WaitForallType e b)
                instantiateSharedMVarsAux t false stk cache
           | .lam _ t b _ =>
                let stk := stk.push (.WaitLambdaType e b)
                instantiateSharedMVarsAux t false stk cache
           | .mdata _ b =>
                let stk := stk.push (.WaitMData e)
                instantiateSharedMVarsAux b false stk cache
           | .proj _ _ b =>
                let stk := stk.push (.WaitProjExpr e)
                instantiateSharedMVarsAux b false stk cache
          else instantiateSharedMVarsAux e true stk (saveInitMVarInto cache e e)


/-- Instantiate MVars will guaranteeing maximum sharing.
    Assume that inputs are maximally shared.
-/
@[always_inline, inline]
def instantiateSharedMVars (e : Expr) : TranslateEnvT Expr :=
  unsafe instantiateSharedMVarsAux e false (Array.emptyWithCapacity e.approxDepth.toNat)
         (HashMap.emptyWithCapacity 64)


private unsafe def instantiateSharedMVarsAux' (cur : Expr) (isResult : Bool) (stk : Array HashConsStack) (cache : InstCache) (assign : MVarAssignments) : TranslateEnvT Expr := do
  if isResult then
      let r := cur
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a =>
             let stk := stk.uset topIdx (.WaitAppArg e r) lcProof
             instantiateSharedMVarsAux' a false stk cache assign
        | .WaitAppArg e f =>
             let r' ← e.updateAppExpr! f r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
        | .WaitForallType e b =>
             let stk := stk.uset topIdx (.WaitForallBody e r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign
        | .WaitForallBody e t =>
             let r' ← e.updateForallExpr! t r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
        | .WaitLambdaType e b =>
             let stk := stk.uset topIdx (.WaitLambdaBody e r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign
        | .WaitLambdaBody e t =>
             let r' ← e.updateLambdaExpr! t r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
        | .WaitLetType e v b =>
             let stk := stk.uset topIdx (.WaitLetValue e r b) lcProof
             instantiateSharedMVarsAux' v false stk cache assign
        | .WaitLetValue e t b =>
             let stk := stk.uset topIdx (.WaitLetBody e t r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign
        | .WaitLetBody e t v =>
             let r' ← e.updateLetExpr! t v r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
        | .WaitMData e =>
             let r' ← e.updateMDataExpr! r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
        | .WaitProjExpr e =>
             let r' ← e.updateProjExpr! r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign
      else return r
  else
      let e := cur
      let cached := cache.getD (mkInstKey e 0) instCacheMiss
      if !exprEq cached instCacheMiss then instantiateSharedMVarsAux' cached true stk cache assign
      else
          if e.hasExprMVar then
           match e with
           | .mvar _ =>
                -- Consult the `assign` snapshot first, then fall back to the metavar
                -- context like `getMVarValue` (the previous version delegated all
                -- recursive calls to the unprimed walker, so nested mvars already
                -- behaved this way; now the snapshot is used at every depth).
                let v := assign.getD e instCacheMiss
                let r ← if exprEq v instCacheMiss then getMVarAssignment! e else pure v
                if r.hasMVar
                then instantiateSharedMVarsAux' r false stk cache assign
                else instantiateSharedMVarsAux' r true stk (saveInitMVarInto cache e r) assign
           | .bvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
                instantiateSharedMVarsAux' e true stk (saveInitMVarInto cache e e) assign
           | .app f a =>
                let stk := stk.push (.WaitAppFun e a)
                instantiateSharedMVarsAux' f false stk cache assign
           | .letE _ t v b _ =>
                let stk := stk.push (.WaitLetType e v b)
                instantiateSharedMVarsAux' t false stk cache assign
           | .forallE _ t b _ =>
                let stk := stk.push (.WaitForallType e b)
                instantiateSharedMVarsAux' t false stk cache assign
           | .lam _ t b _ =>
                let stk := stk.push (.WaitLambdaType e b)
                instantiateSharedMVarsAux' t false stk cache assign
           | .mdata _ b =>
                let stk := stk.push (.WaitMData e)
                instantiateSharedMVarsAux' b false stk cache assign
           | .proj _ _ b =>
                let stk := stk.push (.WaitProjExpr e)
                instantiateSharedMVarsAux' b false stk cache assign
          else instantiateSharedMVarsAux' e true stk (saveInitMVarInto cache e e) assign


/-- Instantiate MVars will guaranteeing maximum sharing.
    Assume that inputs are maximally shared.
-/
@[always_inline, inline]
def instantiateSharedMVars' (e : Expr) (assign : MVarAssignments) : TranslateEnvT Expr :=
  unsafe instantiateSharedMVarsAux' e false (Array.emptyWithCapacity e.approxDepth.toNat)
         (HashMap.emptyWithCapacity 64) assign

end Blaster.Optimize
