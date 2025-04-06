import Lean
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following propagation rules only one fully applied constructor `C e₁ ... eₙ`:

    - When ∃ i ∈ [1..n],
            `eᵢ := if c then d₁ else d₂` ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `if c then C g₁ ... gₙ else C h₁ ... hₙ`

    - When ∃ i ∈ [1..n],
            `eᵢ := dite c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `dite c then (fun h : c => C g₁ ... gₙ) (fun h : ¬ c => C h₁ ... hₙ)`

    - When ∃ i ∈ [1..n],
             eᵢ := match₂ f₁, ..., fₚ with
                  | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => t₁
                   ...
                  | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => tₘ ∧
             ∀ k ∈ [1..m],
               ∀ j ∈ [1..n], (i ≠ j → g₍ₖ₎₍ⱼ₎ = eⱼ) ∧ (i = j → g₍ₖ₎₍ⱼ₎ = tₖ)
       Return
         `match₂ f₁, ..., fₚ with
          | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => C g₍₁₎₍₁₎, ..., g₍₁₎₍ₙ₎
          ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => C g₍ₘ₎₍₁₎, ..., g₍ₘ₎₍ₙ₎`

-/
def constCtorPropagation? (cf : Expr) (cargs : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := cf | return none
  let ConstantInfo.ctorInfo cInfo ← getConstInfo n | return none
  if cargs.size < cInfo.numParams + cInfo.numFields then return none
  for i in [cInfo.numParams : cInfo.numParams + cInfo.numFields] do
    if let some r ← iteCstProp? cf cargs i then return r
    if let some r ← diteCstProp? cf cargs i then return r
    if let some r ← matchCstProp? cf cargs i then return r
  return none

  where
    /-- Implements ite over ctor rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
     if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArgs]! then
       let e1' ← mkExpr (mkAppN f (args.set! idxArgs e1)) (cacheResult := false)
       let e2' ← mkExpr (mkAppN f (args.set! idxArgs e2)) (cacheResult := false)
       -- NOTE: we also need to set the sort type for the pulled ite to meet the ctor type
       let retType ← inferType (mkAppN f args)
       return ← mkExpr (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
     return none

    pushCtorInDIteExpr (f : Expr) (args : Array Expr) (idxField : Nat) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi =>
          withLocalDecl n bi t fun x => do
            let body' ← mkExpr (mkAppN f (args.set! idxField (body.instantiate1 x))) (cacheResult := false)
            mkExpr (← mkLambdaFVars #[x] body') (cacheResult := false)
      | _ => throwEnvError f!"pushCtorInDIteExpr: lambda expression expected but got {reprStr ite_e}"

    /-- Implements dite over ctor rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
     if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArgs]! then
       if !(e1.isLambda && e2.isLambda) then return none
       let e1' ← pushCtorInDIteExpr f args idxArgs e1
       let e2' ← pushCtorInDIteExpr f args idxArgs e2
       -- NOTE: we also need to set the sort type for the pulled dite to meet the ctor type
       let retType ← inferType (mkAppN f args)
       return ← mkExpr (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
     return none

    updateRhsWithCtor
      (f : Expr) (args : Array Expr) (idxField : Nat)
      (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
        let altArgsRes ← retrieveAltsArgs lhs
        let nbParams := altArgsRes.altArgs.size
        lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
          let body' ← mkExpr (mkAppN f (args.set! idxField body)) (cacheResult := false)
          mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    updateReturnType (pType : Expr) (eType : Expr) : TranslateEnvT Expr := do
      lambdaTelescope pType fun params _body => do
        mkExpr (← mkLambdaFVars params eType) (cacheResult := false)

    withMatchAlts (mInfo : MatchInfo) (f : Array Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
      if (isCasesOnRecursor (← getEnv) mInfo.name)
      then lambdaTelescope mInfo.instApp fun xs _t => f xs
      else forallTelescope (← inferType mInfo.instApp) fun xs _t => f xs

    /-- Implements match over ctor rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
     if let some argInfo ← isMatchArg? args[idxArgs]! then
       let mExpr ←
         withMatchAlts argInfo $ fun alts => do
           let mut pargs' := argInfo.args
           let idxPType := argInfo.mInfo.getFirstDiscrPos - 1
           for k in [argInfo.mInfo.getFirstAltPos : argInfo.mInfo.arity] do
             let altIdx := k - argInfo.mInfo.getFirstAltPos
             let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
             pargs' := pargs'.set! k (← updateRhsWithCtor f args idxArgs lhs argInfo.args[k]!)
             -- NOTE: we also need to set the return type for pulled over match to meet the ctor type
             let retType ← inferType (mkAppN f args)
             pargs' := pargs'.set! idxPType (← updateReturnType argInfo.args[idxPType]! retType)
           mkExpr (mkAppN argInfo.nameExpr pargs') (cacheResult := false)
       return mExpr
      return none

end Solver.Optimize
