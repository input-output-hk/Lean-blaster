import Lean
import Blaster.Optimize.Rewriting.FunPropagation
import Blaster.Optimize.Rewriting.OptimizeBoolNot
import Blaster.Optimize.Rewriting.OptimizeBoolPropBinary
import Blaster.Optimize.Rewriting.OptimizeDecide
import Blaster.Optimize.Rewriting.OptimizeDecideBoolBinary
import Blaster.Optimize.Rewriting.OptimizeExists
import Blaster.Optimize.Rewriting.OptimizeInt
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeNat
import Blaster.Optimize.Rewriting.OptimizeString
import Blaster.Optimize.OptimizeStack

open Lean Meta

namespace Blaster.Optimize

/-- Given application `f x₁ ... xₙ`, perform the following:
     - When `isOpaqueRecFun f #[x₁ ... xₙ] ∧ allExplicitParamsAreCtor f #[x₁ ... xₙ]
          - When some auxFun ← unfoldOpaqueFunDef f #[x₁ ... xₙ]
             - When some body ← getFunBody auxFun.getAppFn'
                - return `Expr.beta body auxFun.getAppArgs`
             - Otherwise:
                - return ⊥
          - Otherwise:
              - return none
     - When `isRecursiveFun f ∧ ¬ isOpaqueFunExpr f #[x₁ ... xₙ] ∧ allExplicitParamsAreCtor f #[x₁ ... xₙ]
         - When some body ← getFunBody f:
             - return `Expr.beta body #[x₁ ... xₙ]`
         - Otherwise:
             - return ⊥
     - Otherwise:
         - return none
-/
def reduceApp? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if let some r ← isOpaqueRecReduction? f args then return r
 if (← isOpaqueFunExpr f args) then return none
 if let some r ← isFunRecReduction? f args then return r
 return none

 where
   isOpaqueRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     if !(← isOpaqueRecFun f args) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some auxFun ← unfoldOpaqueFunDef f args | return none
     let some fbody ← getFunBody auxFun.getAppFn'
       | throwEnvError "reduceApp?: recursive function body expected for {reprStr f}"
     return (betaLambda fbody auxFun.getAppArgs)

   isFunRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let Expr.const n _ := f | return none
     if !(← isRecursiveFun n) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some fbody ← getFunBody f
       | throwEnvError "reduceApp?: recursive function body expected for {reprStr f}"
     return (betaLambda fbody args)

/-- Perform constant propagation and apply simplification and normalization rules
    on application expressions.
-/
def optimizeAppAux (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  let args ← reorderOperands f args
  if let some e ← optimizePropNot? f args then return e
  if let some e ← optimizePropBinary? f args then return e
  if let some e ← optimizeBoolNot? f args then return e
  if let some e ← optimizeBoolBinary? f args then return e
  if let some e ← optimizeEquality? f args then return e
  if let some e ← optimizeNat? f args then return e
  if let some e ← optimizeInt? f args then return e
  if let some e ← optimizeExists? f args then return e
  if let some e ← optimizeDecide? f args then return e
  if let some e ← optimizeRelational? f args then return e
  if let some e ← optimizeString? f args then return e
  let appExpr := mkAppN f args
  if (← isResolvableType appExpr) then return (← resolveTypeAbbrev appExpr)
  return appExpr

/-- Perform the following:
     - apply normalization and simplification rrules on the given application expression
     - When restart flag is set:
        - add optimized application on continuation stack
     - Otherwise:
         - try tp apply function propagation over ite and match:
            - When propagation rules are triggered:
                - add result on continuation stack
            - Otherwise:
                - cache normalized application
                - proceed with stack continuity

    NOTE: skipPropCheck is set to `true` only when it is known beforehand that `f`
    is a recursive function for which `allExplicitParamsAreCtor f args (funPropagation := true)`
    returns `true`.
-/
def optimizeApp
  (f : Expr) (args: Array Expr)
  (stack : List OptimizeStack) (skipPropCheck := false) : TranslateEnvT OptimizeContinuity := do
  let e ← optimizeAppAux f args
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else
    match (← isFunPropagation? e) with
    | some r => return Sum.inl (.InitOptimizeExpr r :: stack)
    | none => stackContinuity stack (← mkExpr e) -- cache expression and proceed with continuity

  where
    @[always_inline, inline]
    isFunPropagation? (e : Expr) : TranslateEnvT (Option Expr) :=
      if e.isApp then
        let (f', args') := getAppFnWithArgs e
        funPropagation? f' args' skipPropCheck
      else return none

/-- Given application `f x₁ ... xₙ`,
     - When `isFunITE f` (i.e., f is a Blaster.dite' that return a function)
         - return none
     - when `isNotfun f`
         - return none
     - when `t₁ → ... → tₘ ← inferType f ∧ n < m`:
        - when ∀ i ∈ [1..n], ¬ isExplicit tᵢ:
           - return none
        - otherwise:
           - return `etaExpand (mkAppN f args)`
     - otherwise `none`
-/
def normPartialFun? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if isFunITE f then return none
 if (← isNotFun f) then return none
 let pInfo ← getFunEnvInfo f
 if pInfo.paramsInfo.size <= args.size then return none
 let nbImplicits := pInfo.paramsInfo.foldl (fun acc p => if !p.isExplicit then acc + 1 else acc) 0
 if nbImplicits == args.size then return none
 etaExpand (mkAppN f args)

 where
   isFunITE (e : Expr) : Bool :=
     match e with
     | Expr.const ``Blaster.dite' _ => args.size > 4
     | _ => false

/-- Try to rewrite a goal with a single expression.
    Returns the new goal if the rewrite succeeded, or the original goal unchanged. -/
private def tryRewriteStep (g : MVarId) (proof : Expr) : MetaM MVarId := do
  if ← g.isAssigned then return g
  try
    let r ← g.rewrite (← g.getType) proof
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    try g'.refl; return g' catch _ => pure ()
    return g'
  catch _ => return g

/-- Close an induction subgoal for recursive function equivalence.
    Leaves the goal unassigned if unable to close. -/
private def closeInductionSubgoal (sg : MVarId)
    (ufSteps rfSteps : Array ProofStep) : MetaM Unit := do
  if ← sg.isAssigned then return
  try sg.refl; return catch _ => pure ()
  -- Iteratively unfold head definitions on both sides
  let g ← sg.withContext do
    let mut g := sg
    let mut progress := true
    while progress do
      progress := false
      if ← g.isAssigned then return g
      try
        let ty ← g.getType
        match ty.eq? with
        | some (_, lhs, rhs) =>
          let lhsU ← unfoldDefinition? lhs
          let rhsU ← unfoldDefinition? rhs
          let lhs' := lhsU.getD lhs
          let rhs' := rhsU.getD rhs
          if lhs' != lhs || rhs' != rhs then
            let newTy ← mkEq lhs' rhs'
            g ← g.change newTy
            try g.refl; return g catch _ => pure ()
            progress := true
        | none => pure ()
      catch _ => pure ()
    return g
  if ← g.isAssigned then return
  -- uf local steps
  let g ← g.withContext do
    let mut g := g
    for step in ufSteps do
      if ← g.isAssigned then return g
      match step with
      | .rewrite proof _ =>
        g ← tryRewriteStep g proof
      | .exact _ => pure ()
    return g
  if ← g.isAssigned then return
  -- rf local steps (both directions)
  let g ← g.withContext do
    let mut g := g
    for step in rfSteps do
      if ← g.isAssigned then return g
      match step with
      | .rewrite proof _ =>
        g ← tryRewriteStep g proof
        if ← g.isAssigned then return g
        try
          let r ← g.rewrite (← g.getType) proof (symm := true)
          let g' ← g.replaceTargetEq r.eNew r.eqProof
          try g'.refl; return g' catch _ => pure ()
          g := g'
        catch _ => pure ()
      | .exact _ => pure ()
    return g
  if ← g.isAssigned then return
  try g.refl; return catch _ => pure ()
  -- Rewrite with hypotheses
  let g ← g.withContext do
    let lctx ← getLCtx
    let decls := lctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push decl
    let mut g : MVarId := g
    for decl in decls do
      if ← g.isAssigned then return g
      if !(← isProp decl.type) then continue
      g ← tryRewriteStep g decl.toExpr
      if ← g.isAssigned then return g
    return g
  if ← g.isAssigned then return
  -- Commutativity lemmas
  let g ← g.withContext do
    let mut g : MVarId := g
    for commName in #[``Int.mul_comm, ``Nat.mul_comm, ``Int.add_comm, ``Nat.add_comm] do
      if ← g.isAssigned then return g
      g ← tryRewriteStep g (mkConst commName)
      if ← g.isAssigned then return g
    return g
  if ← g.isAssigned then return
  -- Retry hypotheses after commutativity
  g.withContext do
    let lctx ← getLCtx
    let decls := lctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push decl
    let mut g : MVarId := g
    for decl in decls do
      if ← g.isAssigned then return
      if !(← isProp decl.type) then continue
      g ← tryRewriteStep g decl.toExpr
      if ← g.isAssigned then return

/-- Prove `uf = rf` by structural induction, universally quantified over free variables.
    Returns the forall-quantified proof so that `rewrite` can unify with any instantiation.
    Falls back to `admit` for subgoals that cannot be closed. -/
private def proveRecFunEquiv (ufApp rfApp : Expr)
    (ufSteps rfSteps : Array ProofStep := #[]) : MetaM Expr := do
  let eq ← mkEq ufApp rfApp
  let fvarIds ← do
    let s := collectFVars {} eq
    sortFVarIds s.fvarSet.toArray
  let allFvars := fvarIds.map mkFVar
  if allFvars.isEmpty then
    let proof ← mkFreshExprMVar eq
    try proof.mvarId!.refl catch _ => proof.mvarId!.admit
    return proof
  let mut inductIdx? : Option Nat := none
  for h : i in [:allFvars.size] do
    let fvarId := allFvars[i].fvarId!
    try
      let ty ← fvarId.getType
      if let .const tyName _ := ty.getAppFn then
        if let some (.inductInfo _) := (← getEnv).find? tyName then
          inductIdx? := some i
    catch _ => continue
  let forallType ← mkForallFVars allFvars eq
  let proof ← mkFreshExprMVar forallType
  let goalId := proof.mvarId!
  let (introFVarIds, goalId) ← goalId.introNP allFvars.size
  match inductIdx? with
  | none =>
    unless ← goalId.isAssigned do goalId.admit
  | some idx =>
    try
      goalId.withContext do
        let inductFVarId := introFVarIds[idx]!
        let ty ← inductFVarId.getType
        let .const tyName _ := ty.getAppFn
          | goalId.admit; return
        let results ← goalId.induction inductFVarId (Name.mkStr tyName "rec")
        for result in results do
          closeInductionSubgoal result.mvarId ufSteps rfSteps
        for result in results do
          unless ← result.mvarId.isAssigned do result.mvarId.admit
    catch _ =>
      unless ← goalId.isAssigned do goalId.admit
  return proof

/-- Retrieve the local proof stack for a function from recFunInstCache.
    Returns empty array if not found. -/
private def getRecFunLocalProofStack (f : Expr) (args : Array Expr)
    : TranslateEnvT (Array ProofStep) := do
  let cache := (← get).optEnv.recFunInstCache
  try
    let params ← getImplicitParameters f args
    let instApp ← getInstApp f params
    match cache.get? instApp with
    | some result => return result.proofStack
    | none =>
      match cache.get? f with
      | some result => return result.proofStack
      | none => return #[]
  catch _ => return #[]

/-- Emit a rewrite proof step for recursive function equivalence.
    Retrieves local proof stacks from recFunInstCache and uses them
    to close induction subgoals. -/
private def emitRecFunEquivStep
    (uf rf : Expr) (uargs : Array Expr)
    : TranslateEnvT Unit := do
  let ufApp := mkAppN uf uargs
  let rfApp := mkAppN rf uargs
  try if ← isDefEq ufApp rfApp then return catch _ => pure ()
  let ufSteps ← getRecFunLocalProofStack uf uargs
  let rfSteps ← getRecFunLocalProofStack rf uargs
  try
    let ufTy ← inferType ufApp
    let rfTy ← inferType rfApp
    if ← isDefEq ufTy rfTy then
      let proof ← withLocalContext do proveRecFunEquiv ufApp rfApp ufSteps rfSteps
      let proof ← instantiateMVars proof
      unless containsSorry proof do
        pushProofStep (.rewrite proof)
  catch _ => pure ()
where
  containsSorry : Expr → Bool
    | .const ``sorryAx _ => true
    | .app f a => containsSorry f || containsSorry a
    | .lam _ t b _ => containsSorry t || containsSorry b
    | .forallE _ t b _ => containsSorry t || containsSorry b
    | .letE _ t v b _ => containsSorry t || containsSorry v || containsSorry b
    | .mdata _ e => containsSorry e
    | .proj _ _ e => containsSorry e
    | _ => false

/-- Given application `f x₁ ... xₙ` perform the following:
    - when `f` corresponds to a recursive definition `λ p₁ ... pₙ → body` the following actions are performed:
        - params ← getImplicitParameters f #[x₁ ... xₙ]
        - fᵢₙₛ ← getInstApp f params
        - When entry `fᵢₙₛ := fdef` exists in the instance cache and `fdef := fₙ` is in the recursive function map.
             - return `optimizeRecApp fₙ params`
        - when no entry for `fᵢₙₛ` exists in the instance cache:
           - fbody' ← optimizer (← generalizeRecCall f params (λ p₁ ... pₙ → body))`
           - call `storeRecFunDef` to update instance cache and check if recursive definition already exists in map, i.e.:
               fᵢ ← storeRecFunDef fᵢₙₛ fbody'
           - return `optimizeRecApp fᵢ params`
    - when `f` is not a recursive definition or is already in the recursive visited cache.
       - return `optimizeApp f x₁ ... xₙ`.
    Assumes that an entry exists for each opaque recursive function in `recFunMap` before
    optimization is performed (see function `cacheOpaqueRecFun`).
-/
def normOpaqueAndRecFun (s : OptimizeStack) (xs : List OptimizeStack) :
  TranslateEnvT OptimizeContinuity := withLocalContext $ do
  match s with
  | .InitOpaqueRecExpr uf uargs =>
      let Expr.const n _ := uf | return (← stackContinuity xs (← mkAppExpr uf uargs))
      let isOpaqueRec ← isOpaqueRecFun uf uargs
      if (← isRecursiveFun n) || isOpaqueRec
      then
        if (← allExplicitParamsAreCtor uf uargs (funPropagation := true)) then
          -- call fun propagation to avoid optimizing rec body
          -- if rec function is an opaqueRec call app optimization first
          -- before calling fun propagation
          optimizeApp uf uargs xs (skipPropCheck := true)
        else
          -- trace[Optimize.recFun] "normalizing rec function {n}"
          let (f, args) ← resolveOpaque uf uargs isOpaqueRec
          -- trace[Optimize.recFun] "resolved opaque instance {reprStr f} {reprStr args}"
          -- retrieve implicit arguments
          let params ← getImplicitParameters f args
          -- trace[Optimize.recFun] "implicit arguments for {n} ==> {reprStr params}"
          -- get instance application
          let instApp ← getInstApp f params
          if (← isVisitedRecFun instApp) then
            -- trace[Optimize.recFun] "rec function instance {instApp} is in visiting cache"
            optimizeRecApp uf f uargs params xs -- already cached
          else if let some r ← hasRecFunInst? instApp then
            -- trace[Optimize.recFun] "rec function instance {instApp} is already equivalent to {reprStr r}"
            optimizeRecApp uf r uargs params xs
          else
            cacheFunName instApp -- cache function name
            let some fbody ← getFunBody f
              | throwEnvError "normOpaqueAndRecFun: recursive function body expected for {reprStr f}"
            -- instantiating polymorphic parameters in fun body
            let fdef ← generalizeRecCall f params fbody
            -- trace[Optimize.recFun] "generalizing rec body for {n} got {reprStr fdef}"
            let subsInst ← opaqueInstApp uf uargs isOpaqueRec instApp
            -- optimize recursive fun definition and store
            let recCtx ← mkRecFuncStackContext
            updateLocalProofStack #[]
            return Sum.inl
              (.InitOptimizeExpr
                fdef :: .RecFunDefWaitForStorage uargs instApp subsInst params recCtx :: xs)
      else optimizeApp uf uargs xs -- optimizations on opaque functions

  | .RecFunDefStorage uargs instApp subsInst params optDef recCtx =>
        uncacheFunName instApp
        -- trace[Optimize.recFun] "optimized rec body for {reprStr subsInst} got {reprStr optDef}"
        let localStack := (← get).optEnv.localProofStack
        let fn' ← storeRecFunDef subsInst params optDef localStack
        -- trace[Optimize.recFun] "rec function instance {reprStr subsInst} is equivalent to {reprStr fn'}"
        restoreRecFunStackContext recCtx
        optimizeRecApp subsInst fn' uargs params xs

  | _ => throwEnvError "normOpaqueAndRecFun: unexpected continuity {reprStr s} !!!"

 where

   /-- Given a function application f x₁ ... xₙ, flag `isOpaqueRec` and default instance application `instApp`
       perform the following:
         - When isOpaqueRec:
             - return `getInstApp (← getImplicitParameters f x₁ ... xₙ)`
         - Otherwise:
             - return instApp
   -/
   opaqueInstApp (f : Expr) (args : Array Expr) (isOpaqueRec : Bool) (instApp : Expr) : TranslateEnvT Expr := do
     if isOpaqueRec then
        getInstApp f (← getImplicitParameters f args)
     else return instApp

   /-- Given a function application f x₁ ... xₙ and flag `isOpaqueRec` perform the following:
         - When isOpaqueRec:
             let auxApp ← unfoldOpaqueFunDef f x₁ ... xₙ
              - when auxApp := λ α₀ → ... → λ αₖ → fₑ x₀ ... xₙ` (i.e., partially applied opaque relational function)
                 - return (fₑ, x₀ ... xₙ₋ₖ)
              - when auxApp := fₑ x₀ ... xₙ` (default case)
                 - return (fₑ, x₀ ...xₙ)
         - Otherwise:
              - return (f, x₁ ... xₙ)
   -/
   resolveOpaque (f : Expr) (args : Array Expr) (isOpaqueRec : Bool) : TranslateEnvT (Expr × Array Expr) := do
     if isOpaqueRec then
       let some auxApp ← unfoldOpaqueFunDef f args
         | throwEnvError "resolveOpaque: unfolded definition expected for {reprStr f}"
       if auxApp.isLambda then
         -- partially applied function
         let appCall := getLambdaBody auxApp
         let largs := appCall.getAppArgs
         return (appCall.getAppFn', largs.take (largs.size-auxApp.getNumHeadLambdas))
       else
         return (auxApp.getAppFn', auxApp.getAppArgs)
     else return (f, args)

   normRecOpaque (f : Expr) : Bool :=
     match f with
     | Expr.const ``Nat.beq _
     | Expr.const ``Nat.ble _ => true
     | _ => false

   /-- Given `rf` a function application instance (see function `getInstApp`) and `params` its
       implicit parameter inffo (see function `getImplicitParameters`), perform the following:
         let instanceArgs := [ params[i] | ∀ i ∈ [0..params.size-1] ∧ params[i].isInstance ]
        - When params.isEmpty :
            - return rf
        - When instanceArgs.isEmpty ∨ f =ₚₜᵣ rf (i.e., non ploymorphic function or rec call in fun body)
            - return `optimizeApp rf args`
        - When rf.isConst (i.e., polymorphic function equivalent to a non-polymorphic one)
            - return `optimizeApp rf [params[i] | ∀ i ∈ [0..params.size-1] ∧ ¬ params[i].instance]`
        - Otherwise:
            let auxApp := Expr.beta rf (getEffectiveParams params)
             - When `auxApp := λ α₀ → ... → λ αₖ → fₑ x₀ ... xₙ` (i.e., partially applied polymorphic function)
                 - return `optimizeApp fₑ x₀ ...xₙ₋ₖ`
             - When `auxApp := fₑ x₀ ... xₙ` (default case)
                 - return `optimizeApp fₑ x₀ ...xₙ`
   -/
   optimizeRecApp
     (uf rf : Expr) (uargs : Array Expr)
     (params : ImplicitParameters) (xs : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
     if params.isEmpty then
       return ← stackContinuity xs (← mkExpr rf (cacheResult := !(normRecOpaque rf))) -- catch fun expression
     if exprEq uf rf then
       -- case for when same recursive call
       -- trace[Optimize.recFun.app] "same recursive call case {reprStr rf} {reprStr uargs}"
       if rf.isConst then
         optimizeApp rf uargs xs
       else -- polyomrphic case: we need to remove the generic parameters
         let auxApp := rf.beta (← getEffectiveParams params)
         let (f, args) := getAppFnWithArgs auxApp
         optimizeApp f args xs
     else if rf.isConst then
         -- case when a polymorphic/non-polymorphic function is equivalent to another non-polymorphic one
         let eargs := Array.filterMap (λ p => if !p.isInstance then some p.effectiveArg else none) params
         -- trace[Optimize.recFun.app] "non-polymorphic equivalent case {reprStr rf} {reprStr eargs}"
         emitRecFunEquivStep uf rf uargs
         optimizeApp rf eargs xs
     else
       let auxApp := rf.beta (← getEffectiveParams params)
       if auxApp.isLambda then
         -- case for partially applied functions, i.e., some explicit arguments not provided
         let appCall := getLambdaBody auxApp
         let (f, largs) := getAppFnWithArgs appCall
         -- trace[Optimize.recFun.app] "partially applied case {reprStr appCall.getAppFn'} {reprStr largs[0:largs.size-auxApp.getNumHeadLambdas]}"
         emitRecFunEquivStep uf rf uargs
         optimizeApp f (largs.take (largs.size-auxApp.getNumHeadLambdas)) xs
       else
         -- trace[Optimize.recFun.app] "polymorphic equivalent case {reprStr auxApp.getAppFn'} {reprStr auxApp.getAppArgs}"
         let (f, args) := getAppFnWithArgs auxApp
         emitRecFunEquivStep uf rf uargs
         optimizeApp f args xs

initialize
  registerTraceClass `Optimize.recFun
  registerTraceClass `Optimize.recFun.app


end Blaster.Optimize
