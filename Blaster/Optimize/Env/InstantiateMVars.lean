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


private unsafe def instantiateSharedMVarsAux' (cur : Expr) (isResult : Bool) (stk : Array HashConsStack) (cache : InstCache) (assign : MVarAssignments) (allowUnassigned : Bool := false) : TranslateEnvT Expr := do
  if isResult then
      let r := cur
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a =>
             let stk := stk.uset topIdx (.WaitAppArg e r) lcProof
             instantiateSharedMVarsAux' a false stk cache assign allowUnassigned
        | .WaitAppArg e f =>
             let r' ← e.updateAppExpr! f r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
        | .WaitForallType e b =>
             let stk := stk.uset topIdx (.WaitForallBody e r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign allowUnassigned
        | .WaitForallBody e t =>
             let r' ← e.updateForallExpr! t r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
        | .WaitLambdaType e b =>
             let stk := stk.uset topIdx (.WaitLambdaBody e r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign allowUnassigned
        | .WaitLambdaBody e t =>
             let r' ← e.updateLambdaExpr! t r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
        | .WaitLetType e v b =>
             let stk := stk.uset topIdx (.WaitLetValue e r b) lcProof
             instantiateSharedMVarsAux' v false stk cache assign allowUnassigned
        | .WaitLetValue e t b =>
             let stk := stk.uset topIdx (.WaitLetBody e t r) lcProof
             instantiateSharedMVarsAux' b false stk cache assign allowUnassigned
        | .WaitLetBody e t v =>
             let r' ← e.updateLetExpr! t v r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
        | .WaitMData e =>
             let r' ← e.updateMDataExpr! r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
        | .WaitProjExpr e =>
             let r' ← e.updateProjExpr! r
             instantiateSharedMVarsAux' r' true stk.pop (saveInitMVarInto cache e r') assign allowUnassigned
      else return r
  else
      let e := cur
      let cached := cache.getD (mkInstKey e 0) instCacheMiss
      if !exprEq cached instCacheMiss then instantiateSharedMVarsAux' cached true stk cache assign allowUnassigned
      else
          if e.hasExprMVar then
           match e with
           | .mvar _ =>
                let v := assign.getD e instCacheMiss
                let r ←
                  if !exprEq v instCacheMiss then pure v
                  else if !allowUnassigned then getMVarAssignment! e
                  else
                    match ← getExprMVarAssignment? e.mvarId! with
                    | some value => hashcons value
                    | none => pure e
                if allowUnassigned && exprEq r e then
                  instantiateSharedMVarsAux' e true stk (saveInitMVarInto cache e e) assign allowUnassigned
                else if r.hasMVar
                then instantiateSharedMVarsAux' r false stk cache assign allowUnassigned
                else instantiateSharedMVarsAux' r true stk (saveInitMVarInto cache e r) assign allowUnassigned
           | .bvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
                instantiateSharedMVarsAux' e true stk (saveInitMVarInto cache e e) assign allowUnassigned
           | .app f a =>
                let stk := stk.push (.WaitAppFun e a)
                instantiateSharedMVarsAux' f false stk cache assign allowUnassigned
           | .letE _ t v b _ =>
                let stk := stk.push (.WaitLetType e v b)
                instantiateSharedMVarsAux' t false stk cache assign allowUnassigned
           | .forallE _ t b _ =>
                let stk := stk.push (.WaitForallType e b)
                instantiateSharedMVarsAux' t false stk cache assign allowUnassigned
           | .lam _ t b _ =>
                let stk := stk.push (.WaitLambdaType e b)
                instantiateSharedMVarsAux' t false stk cache assign allowUnassigned
           | .mdata _ b =>
                let stk := stk.push (.WaitMData e)
                instantiateSharedMVarsAux' b false stk cache assign allowUnassigned
           | .proj _ _ b =>
                let stk := stk.push (.WaitProjExpr e)
                instantiateSharedMVarsAux' b false stk cache assign allowUnassigned
          else instantiateSharedMVarsAux' e true stk (saveInitMVarInto cache e e) assign allowUnassigned


/-- Instantiate MVars will guaranteeing maximum sharing.
    Assume that inputs are maximally shared.
-/
@[always_inline, inline]
def instantiateSharedMVars' (e : Expr) (assign : MVarAssignments) : TranslateEnvT Expr :=
  unsafe instantiateSharedMVarsAux' e false (Array.emptyWithCapacity e.approxDepth.toNat)
         (HashMap.emptyWithCapacity 64) assign

/-- Resolve assigned metavariables under a fixed assignment snapshot, leaving
    unassigned pattern variables intact. Used before beta-cache rebinding. -/
@[always_inline, inline]
def snapshotSharedMVars (e : Expr) (assign : MVarAssignments) : TranslateEnvT Expr :=
  unsafe instantiateSharedMVarsAux' e false (Array.emptyWithCapacity e.approxDepth.toNat)
         (HashMap.emptyWithCapacity 64) assign true

end Blaster.Optimize
