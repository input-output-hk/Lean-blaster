import Lean
import Solver.Optimize.Rewriting.NormalizeMatch

open Lean Meta Elab

namespace Solver.Optimize
/-- Given a projection `a.i` apply the following normalization rules:
     - When projectCore? a i := some re
         - return `some re`
     - Otherwise
         - When `a := Solver.dite' c (fun h : c => t₁) (fun h : ¬ c => t₂)`
             - return `some Solver.dite' c (fun h : c => t₁.i ) (fun h : ¬ c => t₂.i)`
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
  withLocalContext $ do
    match (← projectCore? s idx) with
    | some re => return re
    | none =>
      if let some re ← diteProj? n idx s then return re
      if let some re ← matchProj? n idx s then return re
      return none

  where
    updateDIteExprWithProj (typeName : Name) (idx : Nat) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => return Expr.lam n t (mkProj typeName idx body) bi
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← isQuantifiedFun ite_e) then
           throwEnvError "updateDIteExprWithProj: lambda/function expression expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => (ite_e h).i`
           withLocalDecl' (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
             mkLambdaFVars #[x] (mkProj typeName idx (ite_e.beta #[x]))

    diteProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let some (_psort, pcond, e1, e2) := dite'? struct | return none
      let retType ← inferTypeEnv (mkProj n idx s)
      let e1' ← updateDIteExprWithProj typeName idx pcond e1
      let e2' ← updateDIteExprWithProj typeName idx (mkApp (← mkPropNotOp) pcond) e2
      return mkApp4 (← mkSolverDIteOp) retType pcond e1' e2'

    updateRhsWithProj (typeName : Name) (idx : Nat) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
      let altArgsRes ← retrieveAltsArgs lhs
      let nbParams := altArgsRes.altArgs.size
      applyOnLambdaBoundedBody rhs (max 1 nbParams) (fun body => return  mkProj typeName idx body)

    matchProj? (typeName : Name) (idx : Nat) (struct : Expr) : TranslateEnvT (Option Expr) := do
      let (f, args) := getAppFnWithArgs struct
      let some argInfo ← isMatcher? f | return none
      let idxType := argInfo.getFirstDiscrPos - 1
      let retType ← inferTypeEnv (mkProj n idx s)
      let alts := getMatchAlts args argInfo
      let mut pargs := args
      for i in [argInfo.getFirstAltPos : argInfo.arity] do
        let altIdx := i - argInfo.getFirstAltPos
        let lhs ← forallTelescope alts[altIdx]! fun _ b => pure b.getAppArgs
        pargs ← pargs.modifyM i (updateRhsWithProj typeName idx lhs)
      -- update ret type for pulled over match
      pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
      return (mkAppN argInfo.nameExpr pargs)

end Solver.Optimize
