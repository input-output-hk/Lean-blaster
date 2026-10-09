import Lean

import Blaster.Optimize.Env

open Lean Meta

namespace Blaster.Optimize

@[inline] def mapTranslateEnvT [MonadControlT TranslateEnvT m] [Monad m] (f : forall {α}, (β → TranslateEnvT α) → TranslateEnvT α) {α} (k : β → m α) : m α :=
  controlAt TranslateEnvT fun runInBase => f fun b => runInBase <| k b

@[inline] def map2TranslateEnvT [MonadControlT TranslateEnvT m] [Monad m] (f : forall {α}, (β → γ → TranslateEnvT α) → TranslateEnvT α) {α} (k : β → γ → m α) : m α :=
  controlAt TranslateEnvT fun runInBase => f fun b c => runInBase <| k b c


variable [MonadControlT TranslateEnvT n] [Monad n]

/-- Return `some className` if `n` corresponds to a class or is transitively an abbrevation
    to a class definition (e.g., DecidableEq, DecidableLT, DecidableRel, etc).
-/
@[always_inline, inline]
def isClassConstraint? (n : Name) : TranslateEnvT (Option Name) := do
  if (← isClassConstraint n)
  then return n
  else return none

/-- Return `true` if `e` corresponds to a class constraint expression
    (see function `isClassConstraint`).
-/
@[always_inline, inline]
def isClassConstraintExpr? (e : Expr) : TranslateEnvT (Option Name) := do
 match e.getAppFn' with
 | Expr.const n _ => isClassConstraint? n
 | _ => return none

@[always_inline, inline]
private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true


structure TelescopeEnv where
  lctx : LocalContext
  localInsts : LocalInstances
  fvars : Array Expr

@[always_inline, inline]
def mkLocalDecl (fvar : Expr) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : TranslateEnvT Unit := do
  let optClass ← isClassConstraintExpr? type
  modifyOptEnv
   fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨⟨fvarIdToDecl, decls, auxDecl⟩, localInsts⟩, o14⟩ =>
      let decl := LocalDecl.cdecl decls.size fvar.fvarId! userName type bi kind
      let fvarIdToDecl := fvarIdToDecl.insert fvar.fvarId! decl
      let decls := decls.push decl
      match optClass with
      | none => ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨⟨fvarIdToDecl, decls, auxDecl⟩, localInsts⟩, o14⟩
      | some c =>
          if decl.isImplementationDetail then
            ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨⟨fvarIdToDecl, decls, auxDecl⟩, localInsts⟩, o14⟩
          else ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨⟨fvarIdToDecl, decls, auxDecl⟩, localInsts.push ⟨c, fvar⟩⟩, o14⟩


@[always_inline, inline]
private def forallTelescopeAuxAux
    (maxFVars? : Option Nat)
    (type : Expr)
    (k : Array Expr → Expr → TranslateEnvT α) : TranslateEnvT α := do
  let rec @[specialize] process (type : Expr) (fvars : Array Expr) : TranslateEnvT α := do
    match type with
    | .forallE n t b bi =>
       if fvarsSizeLtMaxFVars fvars maxFVars? then
         let t ← instantiateSharedRevRange t 0 fvars.size fvars
         let fvarId ← mkFreshFVarId
         let fvar ← mkExpr (mkFVar fvarId)
         mkLocalDecl fvar n t bi
         let fvars := fvars.push fvar
         process b fvars
       else
         let type ← instantiateSharedRevRange type 0 fvars.size fvars
         k fvars type
    | _ =>
      let type ← instantiateSharedRevRange type 0 fvars.size fvars
      k fvars type
  process type (Array.emptyWithCapacity type.approxDepth.toNat)

@[always_inline, inline]
private def forallTelescopeAux
  (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → TranslateEnvT α) : TranslateEnvT α := do
  match maxFVars? with
  | some 0 => k #[] type
  | _ =>
     if type.isForall then
       forallTelescopeAuxAux maxFVars? type k
     else
       k #[] type

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def forallTelescope (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2TranslateEnvT (fun k => forallTelescopeAux type none k) k

/--
  Similar to `forallTelescope`, stops constructing the telescope when
  it reaches size `maxFVars`.
-/
@[always_inline, inline]
def forallBoundedTelescope (type : Expr) (maxFVars : Nat) (k : Array Expr → Expr → n α) : n α :=
  map2TranslateEnvT (fun k => forallTelescopeAux type (some maxFVars) k) k

@[always_inline, inline]
private def lambdaTelescopeImp
  (e : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → TranslateEnvT α) : TranslateEnvT α := do
  process e (Array.emptyWithCapacity e.approxDepth.toNat)

where
  @[specialize] process (e : Expr) (fvars : Array Expr) : TranslateEnvT α := do
    match e with
    | .lam n t b bi =>
       if fvarsSizeLtMaxFVars fvars maxFVars? then
         let fvarId ← mkFreshFVarId
         let fvar ← mkExpr (mkFVar fvarId)
         let t ← instantiateSharedRevRange t 0 fvars.size fvars
         mkLocalDecl fvar n t bi
         let fvars := fvars.push fvar
         process b fvars
       else
         let e ← instantiateSharedRevRange e 0 fvars.size fvars
         k fvars e
    | _ =>
       let e ← instantiateSharedRevRange e 0 fvars.size fvars
       k fvars e

/--
  Given `e` of the form `fun xs => A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def lambdaTelescope (e : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2TranslateEnvT (fun k => lambdaTelescopeImp e none k) k


/--
  Given `e` of the form `fun ..xs ..ys => A`, execute `k xs (fun ..ys => A)` where
  `xs.size ≤ maxFVars`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`.
-/
@[always_inline, inline]
def lambdaBoundedTelescope (e : Expr) (maxFVars : Nat) (k : Array Expr → Expr → n α) : n α :=
  map2TranslateEnvT (fun k => lambdaTelescopeImp e (some maxFVars) k) k


/--
  Given `type` of the form `forall xs => A`, create a new metavariable
  for each `x` ∈ xs and instantiate `A` such that:
    - When `type := inst ∈ forallMetaCache`
        - ∀ i ∈ [0..inst.mvarArgs.size - 1],
        - return `inst`
    - Otherwise:
        - let mvarArgs correspond to the metavariables created for each `x` ∈ xs
        - let instExpr corresponds to the instantiation of `A` with mvarArgs
        - Add `type := {instExpr, mvarArgs}` to forallMetaCache
        - return `{instExpr, mvarArgs}`
  NOTE: Once called, the metavariables must be substitued with their assignment before a
  new call to `forallMetaTelescopeEnv` is done.
  NOTE: There is no need to unassign metavariables or reset their depth upon a catch hit
  as this function is expected to be used only in tryReduction (see OptimizeMatch.lean)
-/
@[always_inline, inline]
def forallMetaTelescopeEnv (type : Expr) : TranslateEnvT ForallMeta := do
  match (← get).optEnv.memCache.forallMetaCache.get? type with
  | some b => return b
  | none =>
       let instMeta ← process type #[]
       -- update cache
       updateForallMetaCache type instMeta
       return instMeta

  where
   process (type : Expr) (mvars : Array Expr) : TranslateEnvT ForallMeta := do
     match type with
     | .forallE _ t b _ =>
          let t ← instantiateSharedRevRange t 0 mvars.size mvars
          let mvar ← mkExpr (← mkFreshExprMVar t)
          let mvars := mvars.push mvar
          process b mvars
     | _ =>
       return {instExpr := ← instantiateSharedRevRange type 0 mvars.size mvars, mvarArgs := mvars}

/-- Helper function for withLocalDecl' -/
@[always_inline, inline]
private def withLocalDeclAux (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → TranslateEnvT α) : TranslateEnvT α := do
  IO.setNumHeartbeats 0
  let fvarId ← mkFreshFVarId
  let ⟨⟨fvarIdToDecl, decls, c3⟩, localInsts⟩ := (← get).optEnv.ctx
  let decl := LocalDecl.cdecl decls.size fvarId name type bi .default
  let optClass ← isClassConstraintExpr? type
  let fvar ← mkExpr (mkFVar fvarId)
  let localInsts :=
    match optClass with
    | none => localInsts
    | some c =>
      if decl.isImplementationDetail
      then localInsts
      else localInsts.push { className := c, fvar := fvar }
  let ctx : LocalContext := ⟨fvarIdToDecl.insert fvarId decl, decls.push decl, c3⟩
  updateLocalContext ⟨ctx, localInsts⟩
  k fvar

/-- Same as default withLocalDecl but rests heartbeats. -/
@[always_inline, inline]
def withLocalDecl' (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → n α) : n α :=
  mapTranslateEnvT (fun k => withLocalDeclAux name bi type k) k

/--
  Eta expand the given expression.
  Example:
  ```
  etaExpand (mkConst ``Nat.add)
  ```
  produces `fun x y => Nat.add x y`
-/
@[always_inline, inline]
def etaExpand (e : Expr) : TranslateEnvT Expr := do
  forallTelescope (← inferTypeEnv e) fun xs _ => do mkLambdaFVarsExpr xs (← mkAppNExpr e xs)

private def binderCntLtMaxBinders (n : Nat) (maxBinders? : Option Nat) : Bool :=
  match maxBinders? with
  | some maxCnt => n < maxCnt
  | none          => true

@[always_inline, inline]
private def applyOnLambdaBodyImp (e : Expr) (maxBinders? : Option Nat) (f : Expr → TranslateEnvT Expr) : TranslateEnvT Expr :=
  let rec @[specialize] visit (e : Expr) (binderCnt : Nat) : TranslateEnvT Expr := do
    match e with
    | .lam _ t b _ =>
         if binderCntLtMaxBinders binderCnt maxBinders? then
           e.updateLambdaExpr! t (← visit b (binderCnt + 1))
         else f e
    | _ => f e
  visit e 0

/-- Given `e` of the form `λ (a₁ : α₁) → ... → λ (aₙ : αₙ) → b`,
    return `λ (a₁ : α₁) → ... → λ (aₙ : αₙ) → f b`.
    NOTE: This function can be used only it is guaranteed the modifications induced by
    `f` will not break the de-bruijn indices.
     E.g.,
       - f b ===> b * 2
       - f b ===> b x₁ ... xₙ s.t., x₁ .. xₙ don't have any bounded variables.
       - etc

    Assume that all inputs are maximally shared
    Assume that f will return a maximally shared expr
    Guarantee that result is maximally shared
-/
@[always_inline, inline]
def applyOnLambdaBody (e : Expr) (f : Expr → TranslateEnvT Expr) : TranslateEnvT Expr :=
  applyOnLambdaBodyImp e none f

/-- Given `e` of the form `λ (a₁ : α₁) → ... → λ (aₙ : αₙ) → b`,
    return `λ (a₁ : α₁) → f λ (aₖ : αₖ → ... → λ (aₙ : αₙ)` where k < maxBinders
    NOTE: This function can be used only it is guaranteed the modifications induced by
    `f` will not break the de-bruijn indices.
     E.g.,
       - f b ===> b * 2
       - f b ===> b x₁ ... xₙ s.t., x₁ .. xₙ don't have any bounded variables.
       - etc
-/
@[always_inline, inline]
def applyOnLambdaBoundedBody (e : Expr) (maxBinders : Nat) (f : Expr → TranslateEnvT Expr) : TranslateEnvT Expr :=
  applyOnLambdaBodyImp e (some maxBinders) f

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
      - When maxTypes? := some k:
          return `#[α₁ ... αₖ]`
      - Otherwise:
          return `#[α₁ ... αₙ]`
     Note: Dependent types are instantiated (whenever necessary).

     Assume that input is maximally shared
     Guanratee that output is maximally shared
-/
private def getLambdaBinderTypesImp (e : Expr) (maxTypes? : Option Nat) : TranslateEnvT (Array Expr) :=
  loop e #[]
  where
    loop (e : Expr) (types : Array Expr) : TranslateEnvT (Array Expr) := do
      match e with
      | .lam _ t b _ =>
           if fvarsSizeLtMaxFVars types maxTypes?
           then
             let t ← instantiateSharedRevRange t 0 types.size types
             loop b (types.push t)
           else return types
      | _ => return types

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
     - let k = maxTypes
     - return `#[α₁ ... αₖ]`
     Note: Dependent types are instantiated (whenever necessary).

     Assume that input is maximally shared
     Guanratee that output is maximally shared
-/
@[always_inline, inline]
def getLambdaBoundedBinderTypes (e : Expr) (maxTypes : Nat) : TranslateEnvT (Array Expr) :=
  getLambdaBinderTypesImp e (some maxTypes)

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, return `#[α₁ ... αₙ]`.
    Note: Dependent types are instantiated (whenever necessary).

   Assume that input is maximally shared
   Guanratee that output is maximally shared
-/
@[always_inline, inline]
def getLambdaBinderTypes (e : Expr) : TranslateEnvT (Array Expr) :=
  getLambdaBinderTypesImp e none


@[always_inline, inline]
def ParamInfo.isExplicit (p : ParamInfo) : Bool := p.binderInfo.isExplicit

/-- Return `pInfo` when `f := pInfo ∈ getFunEnvInfoCache`. Otherwise, performing the following
     - Let v₁ : t₁ → .. → vₙ : tₙ := inferTypeEnv f
     - Let p := #[ { binderInfo := declᵢ.binderInfo, isProp := ← isProp declᵢ.type } |
                   ∀ i ∈ [1..n-1], declᵢ ← vᵢ.fvarId!.getEnvDecl ]
     - Let pInfo := { paramsInfo := p, type := v₁ : t₁ → .. → vₙ : tₙ }
     - add f := pInfo to `getFunEnvInfoCache`
     - return pInfo
-/
def getFunEnvInfo (f : Expr) : TranslateEnvT FunEnvInfo := do
  match (← get).optEnv.memCache.getFunEnvInfoCache.get? f with
  | some p => return p
  | none =>
       let t ← inferTypeEnv f
       let handleFVar (acc : Array ParamInfo) (fv : Expr) : TranslateEnvT (Array ParamInfo):= do
         let decl ← fv.fvarId!.getEnvDecl
         let isProp ← isPropEnv (← inferTypeEnv fv)
         return acc.push { binderInfo := decl.binderInfo, isProp }
       let fInfo ← forallTelescope t fun fvars _ => do
           pure { paramsInfo := ← fvars.foldlM handleFVar #[], type := t }
       updateFunInfoCache f fInfo
       return fInfo

/-- Given `t := ∀ α₀ → ∀ α₂ → ... → αₙ` corresponding to function type and `x₁ ... xₘ` the
    function's applied arguments, determine the application type by properly
    instantiating the implicit arguments.
    Assume that input is maximally shared
    Guarantee that output is maximally shared
-/
def inferAppType (t : Expr) (args : Array Expr) : TranslateEnvT Expr :=
  let rec visit (idx : Nat) (stop : Nat) (t : Expr) (types : Array Expr) : TranslateEnvT Expr := do
    if idx == stop then instantiateSharedRevRange t 0 types.size types
    else
     match t with
     | Expr.forallE _n t b bi =>
         if !bi.isExplicit
         then
           let types := types.push args[idx]!
           visit (idx + 1) stop b types
         else
           let types := types.push t
           visit (idx + 1) stop b types
     | _ => instantiateSharedRevRange t 0 types.size types
  visit 0 args.size t (Array.emptyWithCapacity args.size)

/-- Given `t := ∀ α₀ → ∀ α₂ → ... → αₙ` corresponding to function type and `x₁ ... xₘ` the
    function's applied arguments, determine the ith argument type by properly
    instantiating the implicit arguments.
    Assume that input is maximally shared
    Guarantee that output is maximally shared
-/
def inferArgTypeAt (t : Expr) (args : Array Expr) (i : Nat) : TranslateEnvT Expr :=
  let rec visit (idx : Nat) (stop : Nat) (t : Expr) (types : Array Expr) : TranslateEnvT Expr := do
    if idx ≥ stop then panic! "inferArgTypeAt: i expected to be greater than args.size"
    else
     match t with
     | Expr.forallE _n t b _ =>
         if idx == i then
           instantiateSharedRevRange t 0 types.size types
         else
           let types := types.push args[idx]!
           visit (idx + 1) stop b types
     | _ => panic! "inferArgTypeAt: i expected to be greater than args.size"
  visit 0 args.size t (Array.emptyWithCapacity args.size)

/-- Given a `f : Expr.const n l` a function name expression,
    return `true` if `f` has at least one implicit argument.
-/
def hasImplicitArgs (f : Expr) : TranslateEnvT Bool := do
  let fInfo ← getFunEnvInfo f
  return fInfo.paramsInfo.any (λ p => !p.isExplicit)


/-- Given application `f x₀ ... xₙ` and indices `beginIdx` and `endIdx` return the following sequence:
      let A := [x₀ ... xₙ]
      let instanceArgs := [ { implicitArg := A[i], isInstance := ¬ isExplicit A[i],
                              isGeneric := isGenericParam A[i] }
                            | i ∈ [beginIdx..endIdx-1] ]
      return instanceArgs
    NOTE: It is also assumed that args does not contain any meta or bounded variables.
-/
def getImplicitParametersRange (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : TranslateEnvT ImplicitParameters := do
 let mut instanceParams := (#[] : ImplicitParameters)
 let pInfo ← getFunEnvInfo f
 let nbSize := if endIdx < pInfo.paramsInfo.size then endIdx else pInfo.paramsInfo.size
 if beginIdx < pInfo.paramsInfo.size then
   for i in [beginIdx:nbSize] do
     let p := args[i]!
     if !pInfo.paramsInfo[i]!.isExplicit then
       let isGeneric ← isGenericParam p
       instanceParams := instanceParams.push {effectiveArg := p, isInstance := true, isGeneric}
     else
       instanceParams := instanceParams.push {effectiveArg := p, isInstance := false, isGeneric := false}
   return instanceParams
 else return instanceParams

/-- Given application `f x₀ ... xₙ`, return the following sequence:
      let A := [x₀ ... xₙ]
      let instanceArgs := [ { implicitArg := A[i], isInstance := ¬ isExplicit A[i],
                              isGeneric := isGenericParam A[i] }
                            | i ∈ [0..n] ]
      return instanceArgs
    NOTE: It is also assumed that args does not contain any meta or bounded variables.
-/
@[always_inline, inline]
def getImplicitParameters (f : Expr) (args : Array Expr) : TranslateEnvT ImplicitParameters :=
  getImplicitParametersRange f 0 args.size args


/-- Given function `f` and `params` its implicit parameter info (see `getImplicitParameters`),
    perform the following:
     let instanceArgs := [ params[i] | i ∈ [0..params.size-1] ∧ params[i].isInstance ]
     let genFVars ← retrieveGenericFVars params
      - When instanceArgs.isEmpty
          - return `f`
      - Otherwise:
          - When instanceArgs.size == params.size (i.e., only implicit arguments provided)
             - return `mkLambdaFVars genFVars f`
          - Otherwise:
             - return `mkLambdaFVars genFVars (specializeLambda (← etaExpand f) params)`
-/
def getInstApp (f : Expr) (params : ImplicitParameters) : TranslateEnvT Expr := do
 let instanceArgs := Array.filter (λ p => p.isInstance) params
 if instanceArgs.isEmpty then return f
 else
  let genFVars ← retrieveGenericFVars params
  if instanceArgs.size == params.size
  then mkLambdaFVarsExpr genFVars f -- only implicit arguments provided
  else mkLambdaFVarsExpr genFVars (← specializeLambda (← etaExpand f) params)


end Blaster.Optimize
