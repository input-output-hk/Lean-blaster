import Lean
import Blaster.Optimize.Rewriting.NormalizeMatch

open Lean Meta Elab

namespace Blaster.Optimize
/-- Given a projection `a.i` apply the following normalization rules:
     - When projectEnvCore? a i := some re
         - return `some re`
     - Otherwise
         - When `a := Blaster.dite' c (fun h : c => t₁) (fun h : ¬ c => t₂)`
             - return `some Blaster.dite' c (fun h : c => t₁.i ) (fun h : ¬ c => t₂.i)`
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
def optimizeProjection? (n : Name) (idx : Nat) (s : Expr) : TranslateEnvT (Option Expr) := do
  match (← projectEnvCore? s idx) with
  | some re => hashcons re
  | none =>
      if let some re ← diteProj? n idx s then return re
      if let some re ← matchProj? n idx s then return re
      return none

  where
    updateDIteExprWithProj (typeName : Name) (idx : Nat) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => mkLambdaExpr n bi t (← mkProjExpr typeName idx body)
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← isQuantifiedFun ite_e) then
           throwEnvError "updateDIteExprWithProj: lambda/function expression expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => (ite_e h).i`
           let auxApp ← mkProjExpr typeName idx (← mkAppExpr ite_e (← mkBVarExpr 0))
           mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default ite_cond auxApp

    diteProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let some ( _psort, pcond, e1, e2) := dite'? struct | return none
      let e1' ← updateDIteExprWithProj typeName idx pcond e1
      let e2' ← updateDIteExprWithProj typeName idx (← mkAppExpr (← mkPropNotOp) pcond) e2
      -- NOTE: we need to propagate the reuse context to the new then and else expressions
      propagateReuseContext e1 e1' 0
      propagateReuseContext e2 e2' 0
      let ptype ← inferTypeEnv (← mkProjExpr n idx s)
      mkApp4Expr (← mkBlasterDIteOp) ptype pcond e1' e2'

    updateRhsWithProj (typeName : Name) (idx : Nat) (nbParams : Nat) (rhs : Expr) : TranslateEnvT Expr := do
      applyOnLambdaBoundedBody rhs nbParams (fun body => mkProjExpr typeName idx body)

    matchProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      match struct with
      | .app _ (.lam ..) => -- hack to only consider match
        let (f, args) := getAppFnWithArgs struct
        let some argInfo ← isMatcher? f | return none
        let idxType := argInfo.getFirstDiscrPos - 1
        let alts ← getMatchAlts args argInfo
        let mut pargs := args
        for i in [argInfo.getFirstAltPos : argInfo.arity] do
          let altIdx := i - argInfo.getFirstAltPos
          -- NOTE: No need to propagate the reuse context as match name has not changed
          pargs ← pargs.modifyM i (updateRhsWithProj typeName idx alts[altIdx]!.getNumHeadForalls)
        -- update ret type for pulled over match
        let ptype ← inferTypeEnv (← mkProjExpr n idx s)
        pargs ← pargs.modifyM idxType (updateMatchReturnType ptype)
        mkAppNExpr argInfo.nameExpr pargs
      | _ => return none

end Blaster.Optimize
