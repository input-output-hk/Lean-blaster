import Lean
import Solver.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab

namespace Solver.Optimize
/-- Given a projection `a.i` apply the following normalization rules:
     - When reduceProj? a.i := some re
         - return `some re`
     - Otherwise
         - When `a := if c then e1 else e2`
             - return `some if c then e1.i else e2.i`
         - When `a := dite c (fun h : c => t₁) (fun h : ¬ c => t₂)`
             - return `some dite c (fun h : c => t₁.i ) (fun h : ¬ c => t₂.i)`
         - when `a := match₁ e₁, ..., eₙ with
                  | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
                  ...
                  | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ`
             - return
                 `some match₁ e₁, ..., eₙ with
                       | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁.i
                       ...
                       | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ.i`
-/
def optimizeProjection? (e : Expr) : TranslateEnvT (Option Expr) := do
  let Expr.proj n idx s := e |
    throwEnvError "optimizeProjection: projection expression expected but got {reprStr e}"
  match (← reduceProj? e) with
  | some re => return re
  | none =>
      if let some re ← iteProj? n idx s then return re
      if let some re ← diteProj? n idx s then return re
      if let some re ← matchProj? n idx s then return re
      return none

  where
    iteProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let some (_psort, pcond, pdecide, e1, e2) := ite? struct | return none
      let retType ← inferTypeEnv e
      return mkApp5 (← mkIteOp) retType pcond pdecide (mkProj typeName idx e1) (mkProj typeName idx e2)

    updateDIteExprWithProj (typeName : Name) (idx : Nat) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi =>
           withLocalDecl n bi t fun x => do
            mkLambdaFVars #[x] (mkProj typeName idx (body.instantiate1 x))
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← inferTypeEnv ite_e).isForall then
           throwEnvError f!"pushCtorInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => (ite_e h).i`
           withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
             mkLambdaFVars #[x] (mkProj typeName idx (ite_e.beta #[x]))

    diteProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let some (_psort, pcond, pdecide, e1, e2) := dite? struct | return none
      let retType ← inferTypeEnv e
      let e1' ← updateDIteExprWithProj typeName idx pcond e1
      let e2' ← updateDIteExprWithProj typeName idx (← optimizeNot (← mkPropNotOp) #[pcond]) e2
      return mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2'

    updateRhsWithProj (typeName : Name) (idx : Nat) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
      let altArgsRes ← retrieveAltsArgs lhs
      let nbParams := altArgsRes.altArgs.size
      lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
        mkLambdaFVars params (mkProj typeName idx body)

    matchProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let some argInfo ← isMatcher? struct | return none
      let idxType := argInfo.mInfo.getFirstDiscrPos - 1
      let retType ← inferTypeEnv e
      withMatchAlts argInfo $ fun alts => do
        let mut pargs := argInfo.args
        for i in [argInfo.mInfo.getFirstAltPos : argInfo.mInfo.arity] do
          let altIdx := i - argInfo.mInfo.getFirstAltPos
          let lhs ← forallTelescope (← inferTypeEnv alts[altIdx]!) fun _ b => pure b.getAppArgs
          pargs ← pargs.modifyM i (updateRhsWithProj typeName idx lhs)
        -- update ret type for pulled over match
        pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
        return (mkAppN argInfo.nameExpr pargs)

end Solver.Optimize
