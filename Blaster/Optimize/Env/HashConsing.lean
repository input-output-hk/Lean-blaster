import Lean
import Blaster.Optimize.Env.ExprBuilder

open Lean Meta Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

abbrev InstCache := HashMap InstKey Expr

inductive HashConsStack where
  | WaitAppFun (e a : Expr)
  | WaitAppArg (e f : Expr)
  | WaitForallType (e b : Expr)
  | WaitForallBody (e t : Expr)
  | WaitLambdaType (e b : Expr)
  | WaitLambdaBody (e t : Expr)
  | WaitLetType (e v b : Expr)
  | WaitLetValue (e t b : Expr)
  | WaitLetBody (e t v : Expr)
  | WaitMData (e : Expr)
  | WaitProjExpr (e : Expr)
deriving Repr

@[always_inline, inline]
def saveHashCons (old : Expr) (new : Expr) : TranslateEnvT Expr := do
  if exprEq old new then
    updateHashConsCache old
    return old
  else return new


private unsafe def hashconsAux (cur : Expr) (isResult : Bool) (stk : Array HashConsStack) : TranslateEnvT Expr := do
  if isResult then
    if stk.usize > 0 then
      let topIdx := stk.usize - 1
      let next := stk.uget topIdx lcProof
      match next with
      | .WaitAppFun e a =>
           let stk := stk.uset topIdx (.WaitAppArg e cur) lcProof
           hashconsAux a false stk
      | .WaitAppArg e f =>
           let r' ← saveHashCons e (← e.updateAppExpr! f cur)
           hashconsAux r' true stk.pop
      | .WaitForallType e b =>
           let stk := stk.uset topIdx (.WaitForallBody e cur) lcProof
           hashconsAux b false stk
      | .WaitForallBody e t =>
           let r' ← saveHashCons e (← e.updateForallExpr! t cur)
           hashconsAux r' true stk.pop
      | .WaitLambdaType e b =>
           let stk := stk.uset topIdx (.WaitLambdaBody e cur) lcProof
           hashconsAux b false stk
      | .WaitLambdaBody e t =>
           let r' ← saveHashCons e (← e.updateLambdaExpr! t cur)
           hashconsAux r' true stk.pop
      | .WaitLetType e v b =>
           let stk := stk.uset topIdx (.WaitLetValue e cur b) lcProof
           hashconsAux v false stk
      | .WaitLetValue e t b =>
           let stk := stk.uset topIdx (.WaitLetBody e t cur) lcProof
           hashconsAux b false stk
      | .WaitLetBody e t v =>
           let r' ← saveHashCons e (← e.updateLetExpr! t v cur)
           hashconsAux r' true stk.pop
      | .WaitMData e =>
           let r' ← saveHashCons e (← e.updateMDataExpr! cur)
           hashconsAux r' true stk.pop
      | .WaitProjExpr e =>
           let r' ← saveHashCons e (← e.updateProjExpr! cur)
           hashconsAux r' true stk.pop
    else return cur
  else
    let cached := (← get).optEnv.hashConsCache.getD cur instCacheMiss
    if !exprEq cached.expr instCacheMiss then hashconsAux cached.expr true stk
    else
       match cur with
       | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
           updateHashConsCache cur
           hashconsAux cur true stk
       | .app f a =>
            let stk := stk.push (.WaitAppFun cur a)
            hashconsAux f false stk
       | .letE _ t v b _ =>
            let stk := stk.push (.WaitLetType cur v b)
            hashconsAux t false stk
       | .forallE _ t b _ =>
            let stk := stk.push (.WaitForallType cur b)
            hashconsAux t false stk
       | .lam _ t b _ =>
            let stk := stk.push (.WaitLambdaType cur b)
            hashconsAux t false stk
       | .mdata _ b =>
            let stk := stk.push (.WaitMData cur)
            hashconsAux b false stk
       | .proj _ _ b =>
            let stk := stk.push (.WaitProjExpr cur)
            hashconsAux b false stk

/-- Apply hashconsing on an expression. -/
@[always_inline, inline]
def hashcons (e : Expr) : TranslateEnvT Expr :=
  unsafe hashconsAux e false (Array.emptyWithCapacity e.approxDepth.toNat)


private unsafe def cleanHashConsAux (stk : Array Expr) : TranslateEnvT Unit := do
  if stk.usize > 0 then
    let topIdx := stk.usize - 1
    let e := stk.uget topIdx lcProof
    removeFromHashConsCache e
    match e with
    | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
        cleanHashConsAux stk
    | .app f a =>
         let stk := stk.push f|>.push a
         cleanHashConsAux stk
    | .letE _ t v b _ =>
         let stk := stk.push t|>.push v|>.push b
         cleanHashConsAux stk
    | .forallE _ t b _
    | .lam _ t b _ =>
         let stk := stk.push t|>.push b
         cleanHashConsAux stk
    | .mdata _ b
    | .proj _ _ b =>
         let stk := stk.push b
         cleanHashConsAux stk
  else return ()

/-- Clean hash cons map with expression. -/
@[always_inline, inline]
def cleanHashCons (e : Expr) : TranslateEnvT Unit :=
  unsafe cleanHashConsAux ((Array.emptyWithCapacity e.approxDepth.toNat)|>.push e)

/-- Same as the default inferType in the Lean codebase but perform hashconsing and cache the result. -/
@[always_inline, inline]
def inferTypeEnv (e : Expr) : TranslateEnvT Expr := do
  let cached := (← get).optEnv.memCache.inferTypeCache.getD e instCacheMiss
  if !exprEq cached instCacheMiss then return cached
  else
    let t ← withLocalContext $ do
       IO.setNumHeartbeats 0
       let t ← inferType e
       if t.hasMVar then instantiateMVars t else pure t
    let t ← hashcons t
    updateInferTypeCache e t
    return t

@[always_inline, inline]
def getMVarAssignment! (mvar : Expr) : TranslateEnvT Expr := do
 match ← getExprMVarAssignment? mvar.mvarId! with
 | some v => hashcons v
 | none => throwEnvError "getMVarAssignment!: assignment expected for meta variable {reprStr mvar} !!!"

@[always_inline, inline]
def getMVarValue (mvar : Expr) : TranslateEnvT Expr := do
  let val := (← get).optEnv.mAssignments.getD mvar instCacheMiss
  if !exprEq val instCacheMiss then return val -- expr in mAssignments already hashcons
  else getMVarAssignment! mvar

@[always_inline, inline]
def getEnvMVarValue! (mvar : Expr) (mAssignments : MVarAssignments) : Expr :=
  let val := mAssignments.getD mvar instCacheMiss
  if !exprEq val instCacheMiss then val
  else panic! "getEnvMVarValue!: assignment expected for meta variable {reprStr mvar} !!!"

@[always_inline, inline]
def getEnvMVarValue' (mvar : Expr) (mAssignments : MVarAssignments) : Expr :=
  let val := mAssignments.getD mvar instCacheMiss
  if !exprEq val instCacheMiss then val -- expr in mAssignments already hashcons
  else mvar

@[always_inline, inline]
def getEnvMVarValue (mvar : Expr) : TranslateEnvT Expr :=
  return getEnvMVarValue' mvar (← get).optEnv.mAssignments

end Blaster.Optimize
