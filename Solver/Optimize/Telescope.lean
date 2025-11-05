import Lean
import Solver.Optimize.Env

open Lean Meta

namespace Solver.Optimize

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

private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true

@[always_inline, inline]
private def updateLocalInstance
  (fvar fvarType : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : TranslateEnvT LocalInstances := do
  if let some c ← isClassConstraintExpr? fvarType
  then
    match lctx.find? fvar.fvarId! with
    | none => throwError f!"updateLocalInstance: unknown free variable '{fvar}'"
    | some localDecl =>
       if localDecl.isImplementationDetail
       then return localInsts
       else return localInsts.push { className := c, fvar := fvar }
  else return localInsts

structure TelescopeEnv where
  lctx : LocalContext
  localInsts : LocalInstances
  fvars : Array Expr

abbrev TelescopeEnvT := StateRefT TelescopeEnv TranslateEnvT

private def mkDecl (fvar : Expr) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : TelescopeEnvT Unit := do
  let optClass ← isClassConstraintExpr? type
  modify (fun env =>
            let idx  := env.lctx.decls.size
            let decl := LocalDecl.cdecl idx fvar.fvarId! userName type bi kind
            let localInsts' :=
              match optClass with
              | none => env.localInsts
              | some c =>
                if decl.isImplementationDetail
                then env.localInsts
                else env.localInsts.push { className := c, fvar := fvar }
            { env with
                   lctx.fvarIdToDecl := env.lctx.fvarIdToDecl.insert fvar.fvarId! decl,
                   lctx.decls := env.lctx.decls.push decl
                   localInsts := localInsts'
                   fvars := env.fvars.push fvar
            })

private partial def forallTelescopeAuxAux
    (maxFVars? : Option Nat)
    (type : Expr)
    (k : Array Expr → Expr → TranslateEnvT α) : TranslateEnvT α := do
  let rec process (type : Expr) : TelescopeEnvT Expr := do
    match type with
    | .forallE n t b bi =>
      if fvarsSizeLtMaxFVars (← get).fvars maxFVars? then
        let fvarId ← mkFreshFVarId
        let fvar  := mkFVar fvarId
        mkDecl fvar n t bi
        process (b.instantiate1 fvar)
      else return type
    | _ => return type
  let (body, env) ← process type|>.run {lctx := ← getLCtx, localInsts := ← getLocalInstances, fvars := #[]}
  withLCtx env.lctx env.localInsts do
    k env.fvars body

private partial def forallTelescopeAux
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

private partial def lambdaTelescopeImp
  (e : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → TranslateEnvT α) : TranslateEnvT α := do
  let (body, env) ← process e |>.run {lctx := ← getLCtx, localInsts := ← getLocalInstances, fvars := #[]}
  withLCtx env.lctx env.localInsts do
    k env.fvars body
where
  process (e : Expr) : TelescopeEnvT Expr := do
    match e with
    | .lam n t b bi =>
       if fvarsSizeLtMaxFVars (← get).fvars maxFVars? then
         let fvarId ← mkFreshFVarId
         let fvar := mkFVar fvarId
         mkDecl fvar n t bi
         process (b.instantiate1 fvar)
       else return e
    | _ => return e

/--
  Given `e` of the form `fun ..xs => A`, execute `k xs A`.
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
  Eta expand the given expression.
  Example:
  ```
  etaExpand (mkConst ``Nat.add)
  ```
  produces `fun x y => Nat.add x y`
-/
def etaExpand (e : Expr) : TranslateEnvT Expr := do
  forallTelescope (← inferTypeEnv e) fun xs _ => mkLambdaFVars xs (mkAppN e xs)

/-- Given a sequence of nested foralls `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
      - When maxTypes? := some k:
         return `#[α₁ ... αₖ]`
      - Otherwise:
         return `#[α₁ ... αₙ]`
      NOTE: Dependent types are instantiated (whenever necessary).
-/
private partial def getForallBinderTypesImp (e : Expr) (maxTypes? : Option Nat) : Array Expr := loop e #[]
  where
    loop (e : Expr) (types : Array Expr) : Array Expr :=
      match e with
      | .forallE _ t b _ =>
           if fvarsSizeLtMaxFVars types maxTypes?
           then loop (b.instantiate1 t) (types.push t)
           else types
      | _ => types

/-- Given a sequence of nested foralls `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
     - let k = maxTypes
     - return `#[α₁ ... αₖ]`
    NOTE: Dependent types are instantiated (whenever necessary).
-/
@[always_inline, inline]
def getForallBoundedBinderTypes (e : Expr) (maxTypes : Nat) : Array Expr :=
  getForallBinderTypesImp e (some maxTypes)

/-- Given a sequence of nested foralls `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, return `#[α₁ ... αₙ]`.
    NOTE: Dependent types are instantiated (whenever necessary).
-/
@[always_inline, inline]
def getForallBinderTypes (e : Expr) : Array Expr :=
  getForallBinderTypesImp e none

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
      - When maxTypes? := some k:
          return `#[α₁ ... αₖ]`
      - Otherwise:
          return `#[α₁ ... αₙ]`
     Note: Dependent types are instantiated (whenever necessary).
-/
private partial def getLambdaBinderTypesImp (e : Expr) (maxTypes? : Option Nat) : Array Expr := loop e #[]
  where
    loop (e : Expr) (types : Array Expr) : Array Expr :=
      match e with
      | .lam _ t b _ =>
           if fvarsSizeLtMaxFVars types maxTypes?
           then loop (b.instantiate1 t) (types.push t)
           else types
      | _ => types

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, perform the following:
     - let k = maxTypes
     - return `#[α₁ ... αₖ]`
     Note: Dependent types are instantiated (whenever necessary).
-/
@[always_inline, inline]
def getLambdaBoundedBinderTypes (e : Expr) (maxTypes : Nat) : Array Expr :=
  getLambdaBinderTypesImp e (some maxTypes)

/-- Given a sequence of nested lambdas `(a₁ : α₁) → ... → (aₙ : αₙ) → _`, return `#[α₁ ... αₙ]`.
    Note: Dependent types are instantiated (whenever necessary).
-/
@[always_inline, inline]
def getLambdaBinderTypes (e : Expr) : Array Expr :=
  getLambdaBinderTypesImp e none


@[always_inline, inline]
def ParamInfo.isExplicit (p : ParamInfo) : Bool := p.binderInfo.isExplicit

/-- Return `pInfo` when `f := pInfo ∈ getFunEnvInfoCache`. Otherwise, performing the following
     - Let v₁ : t₁ → .. → vₙ : tₙ := inferTypeEnv f
     - Let p := #[ { binderInfo := declᵢ.binderInfo, isProp := ← isProp declᵢ.type, isFun := isFunAux declᵢ.type } |
                   ∀ i ∈ [1..n-1], declᵢ ← getFVarLocalDecl vᵢ ]
     - Let pInfo := { paramsInfo := p, type := v₁ : t₁ → .. → vₙ : tₙ }
     - add f := pInfo to `getFunEnvInfoCache`
     - return pInfo
-/
def getFunEnvInfo (f : Expr) : TranslateEnvT FunEnvInfo := do
  match (← get).optEnv.memCache.getFunEnvInfoCache.get? f with
  | some p => return p
  | none =>
       let t ← inferTypeEnv f
       forallTelescope t fun fvars _ => do
         let mut paramsInfo := #[]
         for h : i in [:fvars.size] do
           let decl ← getFVarLocalDecl fvars[i]
           let isProp ← isPropEnv decl.type
           paramsInfo := paramsInfo.push { binderInfo := decl.binderInfo, isProp }
         let fInfo := { paramsInfo, type := t }
         modify (fun env => { env with optEnv.memCache.getFunEnvInfoCache :=
                                       env.optEnv.memCache.getFunEnvInfoCache.insert f fInfo })
         return fInfo

/-- Given `t := ∀ α₀ → ∀ α₂ → ... → αₙ` corresponding to function type and `x₁ ... xₘ` the
    function's applied arguments, determine the instantiated fun type by properly
    instantiating the implicit arguments.

    TODO: change function to pure tail rec call using stack-based approach
-/
partial def inferFunType (t : Expr) (args : Array Expr) : Expr :=
  let rec visit (idx : Nat) (e : Expr) : Expr :=
    if idx ≥ args.size then e
    else
     match e with
     | Expr.forallE n t b bi =>
         if !bi.isExplicit
         then Expr.forallE n args[idx]! (visit (idx + 1) (b.instantiate1 args[idx]!)) bi
         else Expr.forallE n t (visit (idx + 1) b) bi
     | _ => e
  visit 0 t

/-- Given `t := ∀ α₀ → ∀ α₂ → ... → αₙ` corresponding to function type and `x₁ ... xₘ` the
    function's applied arguments, determine the application type by properly
    instantiating the implicit arguments.
-/
partial def inferAppType (t : Expr) (args : Array Expr) : Expr :=
  let rec visit (idx : Nat) (t : Expr) : Expr :=
    if idx ≥ args.size then t
    else
     match t with
     | Expr.forallE _n _t b bi =>
         if !bi.isExplicit
         then visit (idx + 1) (b.instantiate1 args[idx]!)
         else visit (idx + 1) b
     | _ => t
  visit 0 t

/-- Given a `f : Expr.const n l` a function name expression,
    return `true` if `f` has at least one implicit argument.
-/
def hasImplicitArgs (f : Expr) : TranslateEnvT Bool := do
  let fInfo ← getFunEnvInfo f
  for h : i in [:fInfo.paramsInfo.size] do
    if !fInfo.paramsInfo[i].isExplicit then return true
  return false

/-- Given application `f x₀ ... xₙ`, return the following sequence:
      let A := [x₀ ... xₙ]
      let instanceArgs := [ { implicitArg := A[i], isInstance := ¬ isExplicit A[i],
                              isGeneric := isGenericParam A[i], idxArg := i}
                            | i ∈ [0..n] ]
      return instanceArgs
    NOTE: It is also assumed that args does not contain any meta or bounded variables.
-/
def getImplicitParameters (f : Expr) (args : Array Expr) : TranslateEnvT ImplicitParameters := do
 let mut instanceParams := (#[] : ImplicitParameters)
 let pInfo ← getFunEnvInfo f
 let nbSize := if args.size < pInfo.paramsInfo.size then args.size else pInfo.paramsInfo.size
 for i in [:nbSize] do
   let p := args[i]!
   if !pInfo.paramsInfo[i]!.isExplicit then
     let isGeneric ← isGenericParam p
     instanceParams := instanceParams.push {effectiveArg := p, isInstance := true, isGeneric}
   else
     instanceParams := instanceParams.push {effectiveArg := p, isInstance := false, isGeneric := false}
 return instanceParams


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
def getInstApp (f : Expr) (params: ImplicitParameters) : TranslateEnvT Expr := do
 let instanceArgs := Array.filter (λ p => p.isInstance) params
 if instanceArgs.isEmpty then return f
 else
  let genFVars ← retrieveGenericFVars params
  if instanceArgs.size == params.size then
    -- only implicit arguments provided
    mkLambdaFVars genFVars f
  else
    mkLambdaFVars genFVars (specializeLambda (← etaExpand f) params) (usedOnly := true)


end Solver.Optimize
