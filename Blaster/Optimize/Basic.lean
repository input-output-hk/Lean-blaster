import Lean
import Lean.Util.MonadCache
import Blaster.Command.Options
import Blaster.Logging
import Blaster.Optimize.Rewriting.FunPropagation
import Blaster.Optimize.Rewriting.OptimizeApp
import Blaster.Optimize.Rewriting.OptimizeConst
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Elab Command Term Meta Blaster.Options

namespace Blaster.Optimize

-- TODO: update formalization with inference rule style notation.
partial def optimizeExprAux (stack : List OptimizeStack) (proof : Option Expr := none) :
    TranslateEnvT OptimizeResult := do
  match stack with
  | .InitOptimizeExpr e :: xs =>
      match (← isInOptimizeEnvCache e proof xs) with
      | Sum.inl i_stack =>
          -- trace[Optimize.expr] "optimizing {← ppExpr e}"
          match e with
          | Expr.fvar _ =>
              match (← normFVar e i_stack) with
              | Sum.inr e' => return e'
              -- TODO: compose proof certificates with Eq.trans
              --       when both proof and nextProof are present
              | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof

          | Expr.sort l =>
              -- sort is used for Type u, Prop, etc
              let s' ← mkExpr (Expr.sort (normLevel l))
              match (← stackContinuity i_stack s' proof) with
              | Sum.inr e' => return e'
              -- TODO: compose proof certificates with Eq.trans
              --       when both proof and nextProof are present
              | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof

          | Expr.lit .. => -- number or string literal
              match (← stackContinuity i_stack (← mkExpr e) proof) with
              | Sum.inr e' => return e'
              -- TODO: compose proof certificates with Eq.trans
              --       when both proof and nextProof are present
              | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof

          | Expr.const .. =>
              match (← normConst e i_stack) with
              | Sum.inr e' => return e'
              -- TODO: compose proof certificates with Eq.trans
              --       when both proof and nextProof are present
              | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof

          | Expr.forallE n t b bi =>
              optimizeExprAux (.InitOptimizeExpr t :: .ForallWaitForType n bi b :: i_stack) proof

          | Expr.app .. =>
             let (f, ras) := getAppFnWithArgs e
             -- check if f is a lambda term
             if f.isLambda then
               -- perform beta reduction and apply optimization
               optimizeExprAux (.InitOptimizeExpr (betaLambda f ras) :: i_stack) proof
             else
               -- set inFunApp flag before optimizing `f`
               setInFunApp true
               let i_stack' := .AppWaitForConst ras :: i_stack
               optimizeExprAux (.InitOptimizeExpr f :: i_stack') proof

          | Expr.lam n t b bi => optimizeExprAux (optimizeLambda n t b bi i_stack) proof

                                                      -- inline let expression
          | Expr.letE _n _t v b _ => optimizeExprAux (inlineLet v b i_stack) proof

          | Expr.mdata d me =>
              if (isTaggedRecursiveCall e) then
                setNormalizeFunCall false
                optimizeExprAux
                  (.InitOptimizeExpr me :: .MDataRecCallWaitForExpr d :: i_stack) proof
              else optimizeExprAux (.InitOptimizeExpr me :: i_stack) proof

          | Expr.proj n idx s =>
              let i_stack' := .ProjWaitForExpr n idx :: i_stack
              optimizeExprAux (.InitOptimizeExpr s :: i_stack') proof

          | Expr.mvar .. => throwEnvError "optimizeExpr: unexpected meta variable {e}"
          | Expr.bvar .. => throwEnvError "optimizeExpr: unexpected bound variable {e}"

      | Sum.inr (Sum.inr e') => return e'
        -- TODO: compose proof certificates with Eq.trans
        --       when both proof and nextProof are present
      | Sum.inr (Sum.inl (nextStack, nextProof)) => optimizeExprAux nextStack nextProof

  | s@(.InitOpaqueRecExpr ..) :: xs
  | s@(.RecFunDefStorage ..) :: xs =>
        match (← normOpaqueAndRecFun s xs proof) with
        | Sum.inr e => return e
        -- TODO: compose proof certificates with Eq.trans
        --       when both proof and nextProof are present
        | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof

  | .AppOptimizeImplicitArgs f args idx startIdx stopIdx pInfo :: xs =>
       if idx ≥ stopIdx then
         if isBlasterDiteConst f && args.size ≥ 2 then
           -- applying choice reduction to avoid optimizing unreachable arguments in Blaster.dite'
           let condOpt := .InitOptimizeExpr args[1]!
           optimizeExprAux (condOpt :: .DiteChoiceWaitForCond f args pInfo startIdx :: xs) proof
         else if let some mInfo ← isMatcher? f then
            -- try match reduction rule first to avoid unnecessary optimization on discriminators
            if let some r ← matchReduction? f args mInfo then
              optimizeExprAux (.InitOptimizeExpr r :: xs) proof
            else
              -- applying choice reduction and match constant propagation to
              -- avoid optimizing unreachable rhs in match
              -- only optimizing match discriminators first
              optimizeExprAux
                (.MatchChoiceOptimizeDiscrs
                  f args pInfo startIdx mInfo.getFirstDiscrPos mInfo :: xs)
                proof
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         else if let some r ← funPropagation? f args (reorderArgs := true) then
           optimizeExprAux (.InitOptimizeExpr r :: xs) proof
         -- apply optimization on remaining explicit parameters before reduction
         else
          optimizeExprAux
            (.AppOptimizeExplicitArgs f args startIdx args.size pInfo none :: xs)
            proof

       else if idx < pInfo.paramsInfo.size -- handle case when HOF is the returned type
            then if !pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack) proof
                 else
                  optimizeExprAux
                    (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo :: xs)
                    proof
            else
              optimizeExprAux
                (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo :: xs)
                proof

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo :: xs =>
       if idx ≥ stopIdx then
         -- normalizing ite/match function application
         if let some re ← normChoiceApplication? f args then
           -- trace[Optimize.normChoiceApp] "normalizing choice application {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (.InitOptimizeExpr re :: xs) proof
         -- apply match normalization rules
         else if let some argInfo := mInfo then
           match (← optimizeMatch f args argInfo xs) with
           | Sum.inr e' => return e'
            -- TODO: compose proof certificates with Eq.trans
            --       when both proof and nextProof are present
           | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof
         -- apply ite normalization rules only when fully applied
         else if isBlasterDiteConst f && args.size == 4 then
           match (← optimizeIfThenElse? f args xs) with
           | Sum.inr e' => return e'
            -- TODO: compose proof certificates with Eq.trans
            --       when both proof and nextProof are present
           | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof
         -- try to reduce app if all params are constructors
         else if let some re ← reduceApp? f args then
           -- trace[Optimize.reduceApp] "application reduction {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (.InitOptimizeExpr re :: xs) proof
         -- unfold non-recursive and non-opaque functions
         -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
         -- NOTE: we can only unfold once all parameters have been optimized.
         else if let some fdef ← getUnfoldFunDef? f args then
           -- trace[Optimize.unfoldDef] "unfolding function definition {reprStr f} {reprStr args} => {reprStr fdef}"
           optimizeExprAux (.InitOptimizeExpr fdef :: xs) proof
         -- normalizing partially apply function after unfolding non-opaque functions
         else if let some pe ← normPartialFun? f args then
           -- trace[Optimize.normPartial] "normalizing partial function {reprStr f} {reprStr args} => {reprStr pe}"
           optimizeExprAux (.InitOptimizeExpr pe :: xs) proof
         -- applying optimization on opaque rec function and app and proceed with fun propagation rules
         else optimizeExprAux (.InitOpaqueRecExpr f args :: xs) proof
       else if idx < pInfo.paramsInfo.size
            then if pInfo.paramsInfo[idx]!.isExplicit
                 then
                  optimizeExprAux
                    (← optimizeExplicitArgs f args idx stopIdx pInfo mInfo stack xs)
                    proof
                 else
                  optimizeExprAux
                    (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: xs)
                    proof
            else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack) proof

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo :: xs =>
        if idx ≥ mInfo.getFirstAltPos then
          if let some r ← matchReduction? f args mInfo then
            optimizeExprAux (.InitOptimizeExpr r :: xs) proof
          else
            -- apply optimization on remaining explicit parameters before reduction
            -- keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
            optimizeExprAux
              (.AppOptimizeExplicitArgs f args startArgIdx args.size pInfo mInfo :: xs)
              proof
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack) proof

  | .MatchRhsLambdaNext next :: xs =>
      match next with
      | Expr.lam n t b bi =>
          optimizeExprAux (.InitOptimizeExpr t :: .MatchRhsLambdaWaitForType n bi b :: xs) proof
      | _ =>
         -- header on xs is expected to be .MatchRhsLambdaWaitForBody
         match (← stackContinuity xs next proof) with
            -- TODO: compose proof certificates with Eq.trans
            --       when both proof and nextProof are present
         | Sum.inl (nextStack, nextProof) => optimizeExprAux nextStack nextProof
         | _ => throwEnvError "optimizeExprAux: continuity expected for MatchRhsLambdaNext !!!"

  | _ => throwEnvError "optimizeExprAux: unexpected optimize stack continuity {reprStr stack} !!!"

  where

    /-- Given `e := Expr.fVar fv` perform the following:
         - When `some v := fv.getValue?`
             `return `Sum.inl (.InitOptimizeExpr v :: stack)`
         - Otherwise:
              `return `stackContinuity stack (← mkExpr e)`
    -/
    @[always_inline, inline]
    normFVar (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity :=
      withLocalContext $ do
        match ← e.fvarId!.getValue? with
        | none => stackContinuity stack (← mkExpr e) proof
        | some v =>
            return Sum.inl (.InitOptimizeExpr (← instantiateMVars v) :: stack, none)

    /-- Given a function `f := Expr const n l` perform the following:
         - When `n := mInfo ∈ isMatcherCache` (i.e., match info already optimized)
             - return `none`
         - When let some mInfo ← getMatcherRecInfo? n l (i.e., f's generic instance not optimized)
             - return `some $ Sum.inr (mInfo, matchFun)`
         - Otherwise `none`
    -/
    @[always_inline, inline]
    hasUnOptMatchInfo? (f : Expr) : TranslateEnvT (Option (MatcherRecInfo × Expr)) := do
      if (← isMatcher? f).isSome then return none -- already optimized
      else if let Expr.const n l := f then
        if let some mInfo ← getMatcherRecInfo? n l then
          let cInfo ← getConstEnvInfo n
          let matchFun ← instantiateValueLevelParams cInfo l
          return some (mInfo, matchFun)
        else return none
      else return none

    @[always_inline, inline]
    inlineLet (v : Expr) (body : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      (.InitOptimizeExpr v :: .LetWaitForValue body :: stack)

    @[always_inline, inline]
    optimizeLambda
      (n : Name) (t : Expr) (b : Expr) (bi : BinderInfo)
      (xs : List OptimizeStack) (inDite := false) : List OptimizeStack :=
        .InitOptimizeExpr t :: .LambdaWaitForType n bi b inDite :: xs

    @[always_inline, inline]
    optimizeDiteArg (e : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      match e with
      | Expr.lam n t b bi => optimizeLambda n t b bi stack (inDite := true)
      | _ => .InitOptimizeExpr e :: stack

    @[always_inline, inline]
    optimizeExplicitArgs
      (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
      (pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (stack : List OptimizeStack)
      (nxtStack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := withLocalContext $ do
      if isBlasterDiteConst f then
        if idx == 1 then
         -- skipping optimization for Blaster.dite' cond as already performed by choice reduction on dite
         return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: nxtStack)
        else if idx == 2 || idx == 3
        then return optimizeDiteArg args[idx]! stack
        else return (.InitOptimizeExpr args[idx]! :: stack)
      else if let some argInfo := mInfo then
         if idx >= argInfo.getFirstDiscrPos && idx < argInfo.getFirstAltPos then
           -- skipping optimization for discriminators as already performed by choice reduction on match
           return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: nxtStack)
         else if idx >= argInfo.getFirstAltPos && idx < argInfo.arity then
           optimizeMatchAlt args argInfo idx args[idx]! stack
         else return (.InitOptimizeExpr args[idx]! :: stack)
      else return (.InitOptimizeExpr args[idx]! :: stack)


@[always_inline, inline]
def optimizeExpr (e : Expr) : TranslateEnvT OptimizeResult :=
  optimizeExprAux [.InitOptimizeExpr e]

/-- Same as optimizeExpr but updates local context before optimizing expression -/
@[always_inline, inline]
def optimizeExpr' (e : Expr) : TranslateEnvT OptimizeResult := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  optimizeExprAux [.InitOptimizeExpr e ]

/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun : TranslateEnvT Unit := do
  callOptimize natAdd
  callOptimize natSub
  callOptimize natMul
  callOptimize natBle
  callOptimize natBeq
  callOptimize natPow
  callOptimize intPow

 where
   callOptimize (e : Expr) : TranslateEnvT Unit :=
     discard $ optimizeExprAux [.InitOpaqueRecExpr e #[]]

/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`, returning an optional proof certificate alongside the result.
-/
def Optimize.main (e : Expr) : TranslateEnvT OptimizeResult := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  -- populate recFunInstCache with recursive function definition.
  cacheOpaqueRecFun
  optimizeExpr e


/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: This function is to be used only by callOptimize in package Test.
-/
def command (sOpts: BlasterOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  -- keep the current name generator and restore it afterwards
  let ngen ← getNGen
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let (⟨optExpr, _proof⟩, translateEnv) ← Optimize.main e|>.run env
  -- restore name generator
  setNGen ngen
  return (optExpr, translateEnv)


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Blaster.Optimize
