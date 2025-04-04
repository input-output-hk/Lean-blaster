import Lean
import Solver.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following constant propagation rules only one fully applied constructor `C e₁ ... eₙ`:

    - When ∃ i ∈ [1..n],
            `eᵢ := if c then d₁ else d₂` ∧
             isCstMatchProp d₁ ∧
             isCstMatchProp d₂ ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `if c then C g₁ ... gₙ else C h₁ ... hₙ`

    - When ∃ i ∈ [1..n],
            `eᵢ := dite c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
             isCstMatchProp d₁ ∧
             isCstMatchProp d₂ ∧
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
               isCstMatchProp tₖ ∧
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
  if let some r ← iteCstProp? cf cargs cInfo then return r
  if let some r ← diteCstProp? cf cargs cInfo then return r
  if let some r ← matchCstProp? cf cargs cInfo then return r
  return none

  where
    /-- Implements ite over ctor rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (cInfo : ConstructorVal) : TranslateEnvT (Option Expr) := do
      for i in [cInfo.numParams : cInfo.numParams + cInfo.numFields] do
        let currArg := args[i]!
        if let some (_psort, pcond, pdecide, e1, e2) := ite? currArg then
          if !(← isCstMatchProp currArg) then return none
          let e1' ← mkExpr (mkAppN f (args.set! i e1)) (cacheResult := false)
          let e2' ← mkExpr (mkAppN f (args.set! i e2)) (cacheResult := false)
          -- NOTE: we also need to set the sort type for the pulled ite to meet
          -- the ctor type
          let retType ← inferType (mkAppN f args)
          return ← mkExpr (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
      return none

    pushCtorInDIteExpr (f : Expr) (args : Array Expr) (idxField : Nat) (ite_e : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `isCstMatchProp` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      lambdaTelescope ite_e fun params body => do
        let body' ← mkExpr (mkAppN f (args.set! idxField body)) (cacheResult := false)
        mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    /-- Implements dite over ctor rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (cInfo : ConstructorVal) : TranslateEnvT (Option Expr) := do
      for i in [cInfo.numParams : cInfo.numParams + cInfo.numFields] do
        let currArg := args[i]!
        if let some (_psort, pcond, pdecide, e1, e2) := dite? currArg then
          if !(← isCstMatchProp currArg) then return none
          let e1' ← pushCtorInDIteExpr f args i e1
          let e2' ← pushCtorInDIteExpr f args i e2
          -- NOTE: we also need to set the sort type for the pulled dite to meet
          -- the return type of the embedded match
          let retType ← inferType (mkAppN f args)
          return ← mkExpr (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
      return none

    updateRhsWithCtor (f : Expr) (args : Array Expr) (idxField : Nat) (rhs : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `isCstMatchProp` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      lambdaTelescope rhs fun params body => do
        let body' ← mkExpr (mkAppN f (args.set! idxField body)) (cacheResult := false)
        mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    updateReturnType (pType : Expr) (eType : Expr) : TranslateEnvT Expr := do
      lambdaTelescope pType fun params _body => do
        mkExpr (← mkLambdaFVars params eType) (cacheResult := false)

    /-- Implements match over ctor rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (cInfo : ConstructorVal) : TranslateEnvT (Option Expr) := do
      for i in [cInfo.numParams : cInfo.numParams + cInfo.numFields] do
        let currArg := args[i]!
        if let some (pm, pargs, minfo) ← isMatchArg? currArg then
          if !(← isCstMatchProp currArg) then return none
          let mut pargs' := pargs
          let idxPType := minfo.getFirstDiscrPos - 1
          for k in [minfo.getFirstAltPos : minfo.arity] do
            pargs' := pargs'.set! k (← updateRhsWithCtor f args i pargs[k]!)
            -- NOTE: we also need to set the return type for pulled over match
            -- to meet the return type of the embedded match.
            let retType ← inferType (mkAppN f args)
            pargs' := pargs'.set! idxPType (← updateReturnType pargs[idxPType]! retType)
          return ← mkExpr (mkAppN pm pargs') (cacheResult := false)
      return none

end Solver.Optimize
