import Lean
import Blaster.Optimize.Env.Abstract
import Blaster.Optimize.Env.Instantiate
import Blaster.Optimize.Env.InstantiateMVars
import Blaster.Optimize.Env.Replace
import Blaster.Optimize.Env.SynthInstance
import Blaster.Optimize.Opaque

open Lean Meta Blaster.Data.HashSet

namespace Blaster.Optimize

/-- Same as the default `getConstInfo` but cache result. -/
@[inline] def getConstEnvInfo (n : Name) : TranslateEnvT ConstantInfo := do
  match (← get).optEnv.memCache.getConstInfoCache.get? n with
  | some info => return info
  | none =>
      let info ← getConstInfo n
      updateConstInfoCache n info
      return info

/-- Return `true` if c corresponds to a constructor. -/
@[always_inline, inline]
def isCtorName (c : Name) : TranslateEnvT Bool :=
  return (← getConstEnvInfo c).isCtor

/-- Return `true` if e corresponds to a constructor expression. -/
@[always_inline, inline]
def isCtorExpr (e : Expr) : TranslateEnvT Bool := do
 match e with
 | Expr.const n _ => return (← getConstEnvInfo n).isCtor
 | _ => return false

/-- Return `true` if `n` correspond to a structure ctor. The result is memoized. -/
@[inline] def isStructureCtorEnv (n : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isStructureCache.get? n with
  | some b => return b
  | none =>
      let b ← isStructureCtorBase n
      updateIsStructureCache n b
      return b
  where
    isStructureCtorBase (n : Name) : TranslateEnvT Bool := do
      let ConstantInfo.ctorInfo info ← getConstEnvInfo n | return false
      return isStructure (← getEnv) info.induct

/-- set optimize option `inPatternMatchin` to `h`. -/
def setInPatternMatching (h : HashSet FVarId) : TranslateEnvT Unit := do
  modify (fun env => {env with smtEnv.options.inPatternMatching := h })

/-- Perform the following actions:
     - let s := (← get).smtEnv.options.inPatternMatching
     - set `inPatternMatching` to `s ∪ h`
     - execute `f`
     - set `inPatternMatching` to s
-/
@[always_inline, inline]
def withTranslatePattern (h : HashSet FVarId) (f: TranslateEnvT α) : TranslateEnvT α := do
  let s := (← get).smtEnv.options.inPatternMatching
  setInPatternMatching (s.union h)
  let t ← f
  setInPatternMatching s
  return t


/-- Return `true` only when there are no hypotheses, match patterns, or equalities
    in scope. The hypothesis, equality and match patterns map are populated only inside
    committed context, i.e., when curCtx != 0. Indeed, the root context does not
    have any hypothesis, equality and match patterns in scope.
-/
@[always_inline, inline]
def isGlobalContext (env : TranslateEnv) : Bool := env.optEnv.options.curCtx == 0

/-- Perform the following:
      - When isGlobal
         - Add entry `a := b` to `globalRewriteCache`
      - Otherwise
         - Add entry `a := b` to `localRewriteCache`
-/
@[always_inline, inline]
def updateOptimizeEnvCache (a : Expr) (b : Expr) (isGlobal : Bool) : TranslateEnvT Unit := do
  -- trace[Optimize.cacheExpr] "cacheExpr {← ppExpr a} ===> {← ppExpr b}"
  if exprEq a b then
    if a.hasFVar then
      if isGlobal
      then updateGlobalRewriteCache a b (insertIfNew := true)
      else updateLocalRewriteCache a b (insertIfNew := true)
    else updateGlobalRewriteCache a b (insertIfNew := true)
  else
    if isGlobal
    then updateGlobalRewriteCache a b
    else updateLocalRewriteCache a b

/-- Perform the following:
      - When isGlobal
         - When `a := b ∈ globalRewriteCache`
            - return `some b`
         - Otherwise `none`
      - Otherwise
         - When `a := b ∈ localRewriteCache`
            - return `some b`
         - Otherwise `none`
-/
@[always_inline, inline]
def isInOptimizeCache? (a : Expr) (isGlobal : Bool) (env : TranslateEnv) : IO Expr := do
 if isGlobal
 then findGlobalCache a env
 else findLocalCache a env


/-- Return `true` if `f` is already in the recursive function cache. -/
@[always_inline, inline] def isVisitedRecFun (f : Expr) : TranslateEnvT Bool :=
 return (← get).optEnv.recFunCache.contains f


/-- Return `true` if `f` corresponds to a theorem name. -/
@[always_inline, inline]
def isTheorem (f : Name) : TranslateEnvT Bool := do
  match (← getConstEnvInfo f) with
  | ConstantInfo.thmInfo _ => pure true
  | _ => pure false

/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : TranslateEnvT Bool :=
  return (opaqueFuns.contains f || (← isOpaqueRelational f args))

/-- Given `f := Expr.const n _` return `true` only when `isOpaqueFun n`. -/
def isOpaqueFunExpr (f : Expr) (args: Array Expr) : TranslateEnvT Bool :=
  match f with
  | Expr.const n _ => isOpaqueFun n args
  | _ => return false


/-- Return `true` only when `f` is a class instance. -/
@[always_inline, inline]
def isInstanceClass (f : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isInstanceCache.get? f with
  | some b => return b
  | none =>
      let b ← isInstance f
      updateInstanceCache f b
      return b

/-- Return `true` when `f` is neither a theorem nor a class instance and
    is tagged as a well-founded recursive definition.
-/
@[always_inline, inline]
def isRecursiveFun (f : Name) : TranslateEnvT Bool := do
  match (← getConstEnvInfo f) with
  | .defnInfo _ =>
      if ← isInstanceClass f then return false
      else
        match (← get).optEnv.memCache.isRecFunCache.get? f with
        | some b => return b
        | none =>
            let b ← isRecursiveDefinition f
            updateIsRecFunCache f b
            return b
  | _ => return false

/-- Helper function for isClassConstraint -/
private partial def isClassConstraintAux (n : Name) : TranslateEnvT Bool := do
 if isClass (← getEnv) n then return true
 else
   match (← getConstEnvInfo n) with
   | ConstantInfo.defnInfo defnInfo =>
       match (getForallLambdaBody defnInfo.value).getAppFn' with
       | Expr.const c _ => isClassConstraintAux c
       | _ => return false
   | _ => return false

/-- Return `true` if `n` corresponds to a class or is transitively an abbrevation
    to a class definition (e.g., DecidableEq, DecidableLT, DecidableRel, etc).
-/
@[always_inline, inline]
def isClassConstraint (n : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isClassCache.get? n with
  | some b => return b
  | none =>
      let b ← isClassConstraintAux n
      updateIsClassCache n b
      return b

/-- Helper function for getMatcherRecInfo? -/
private def getMatcherRecInfoAux? (n : Name) (l : List Level) : TranslateEnvT (Option MatcherRecInfo) := do
 if let some r ← getMatcherInfo? n then return ({mInfo := r, isCasesOn := false} : MatcherRecInfo)
 else if !(isCasesOnRecursor (← getEnv) n) then return none
 else
   let indName := n.getPrefix
   if let ConstantInfo.inductInfo info ← getConstEnvInfo indName then
     let mInfo := { numParams := info.numParams,
                    numDiscrs := info.numIndices + 1,
                    altNumParams := ← updateAltNumParams info.ctors #[]
                    uElimPos? := if info.levelParams.length == l.length then none else some 0
                    discrInfos := Array.replicate (info.numIndices + 1) {}
                  }
     return some { mInfo, isCasesOn := true}
   else return none

 where
   updateAltNumParams (ctors : List Name) (altNumParams : Array Nat) : TranslateEnvT (Array Nat) := do
     match ctors with
     | [] => return altNumParams
     | ctor :: xs =>
         match (← getConstEnvInfo ctor) with
         | ConstantInfo.ctorInfo ctorInfo =>
             updateAltNumParams xs (altNumParams.push ctorInfo.numFields)
         | _ => throwEnvError "updateAltNumParams: ctor info expected for {reprStr ctor} !!!"

/-- Same as the default `getMatcherInfo` in the Lean library but also handles casesOn recursor application. -/
@[always_inline, inline]
def getMatcherRecInfo? (n : Name) (l : List Level) : TranslateEnvT (Option MatcherRecInfo) := do
 match (← get).optEnv.memCache.getMatcherCache.get? n with
 | some m => return m
 | none =>
     let m ← getMatcherRecInfoAux? n l
     updateMatcherCache n m
     return m

/-- Return `some mInfo` when `f := Expr.const n l` ∧ n := mInfo ∈ isMatcherCache.
    Otherwise `none`.
-/
@[always_inline, inline]
def isMatcher? (f : Expr) : TranslateEnvT (Option MatchInfo) := do
 match f with
 | Expr.const n _ => return (← get).optEnv.memCache.isMatcherCache.get? n
 | _ => return none

/-- Return `true` if `n` is a function tagged with the `partial` keyword. -/
private def isPartialDefAux (n : Name) : TranslateEnvT Bool := do
  match ← getConstEnvInfo n with
  | .opaqueInfo _ => return ((← getEnv).find? (Compiler.mkUnsafeRecName n)).isSome
  | _ => return false

/-- Determine if `n` corresponds to a partial definition and cache result. -/
@[always_inline, inline]
def isPartialDef (n : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isPartialCache.get? n with
  | some b => return b
  | none =>
      let b ← isPartialDefAux n
      updateIsPartialCache n b
      return b

/-- Return `true` if `e` corresponds to a class constraint expression
    (see function `isClassConstraint`).
-/
@[always_inline, inline]
def isClassConstraintExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const n _ => isClassConstraint n
 | _ => return false


/-- Return `true` if `f` corresponds to an inductive type. -/
@[always_inline, inline]
def isInductiveType (f : Name) : TranslateEnvT Bool := return (← getConstEnvInfo f).isInductive

/-- Return `true` if `f` corresponds to an axiom/opaque definition. -/
@[always_inline, inline]
def isAxiomOrOpaque (f : Name) : TranslateEnvT Bool := do
  match (← getConstEnvInfo f) with
  | ConstantInfo.axiomInfo _
  | ConstantInfo.opaqueInfo _ => return true
  | _ => return false

/-- Return `true` if `e` corresponds to an inductive type or is an abbreviation to an inductive type. -/
@[always_inline, inline]
def isInductiveTypeExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn with -- keeping mdata here is necessary
 | Expr.const n _ => isInductiveType n
 | _ => return false

structure MVarIdDecl where
  mvar : Expr
  value : Expr
deriving Inhabited

abbrev MVarIdDecls := Array MVarIdDecl

structure BetaLambdaResult where
  /-- beta reduced lambda expression with MVarId as applied arguments. -/
  betaReduced : Expr

  /-- previous meta variable assignment when beta lambda result is in cache. -/
  prevMVarIdDecls : Option MVarIdDecls

private def betaCacheMiss : BetaLambda := ⟨instCacheMiss, #[]⟩

instance : HAppend (Option MVarIdDecls) (Option MVarIdDecls) (Option MVarIdDecls) where
  hAppend
   | none, none => none
   | none, x => x
   | x, none => x
   | some a, some b => some (a ++ b)


@[always_inline, inline]
private unsafe def getMVarDeclsImp (mvars : Array Expr) (mAssignments : MVarAssignments) : MVarIdDecls :=
  let rec loop (idx : USize) (stop : USize) (res : MVarIdDecls) : MVarIdDecls :=
      if idx ≥ stop then res
      else
         let m := (mvars.uget idx lcProof)
         loop (idx + 1) stop (res.uset idx ⟨m, getEnvMVarValue! m mAssignments⟩ lcProof)
  loop 0 mvars.usize (Array.replicate mvars.size default)

def getMVarDecls (mvars : Array Expr) : TranslateEnvT MVarIdDecls :=
  return unsafe getMVarDeclsImp mvars (← get).optEnv.mAssignments

/-- If `e` is a lambda expression, than "beta-reduce" it using assigned meta-variables w.r.t. `args` such that:
    - let types ← getLambdaBinderInstantiatedTypes e args
    - When `(e, types.size) := beta ∈ betaLambdaCache`:
         - Save previous declaration of all meta-variables in beta.mvarArgs, i.e.,
            - let decls ← beta.mvarArgs.mapM (λ m => return ⟨m.mvarId!, ← m.mvarId!.getDecl, ← getAssignment m.mvarId!⟩)
         - ∀ i ∈ [0..beta.mvarArgs.size - 1],
             - set type of meta-variable beta.mvarArgs[i] to types[i]
             - assign meta-variable beta.mvarArgs[i] to args[i]
         - return { betaReduced := beta.betaReduced, prevMVarIdDecls := some decls }
    - Otherwise:
        - Create new meta-variables for applied args, i.e.,:
            - let mvars ← types.mapM (λ t => mkFreshExprMVar (some t))
         - ∀ i ∈ [0..mvars.size - 1],
             - set type of meta-variable mvars[i] to types[i]
             - assign meta-variable mvars[i] to args[i]
         - beta reduced e with mvars, i.e.,
             - let betaExpr := betaLambda e mvars
         - Add `(e, types.size) := betaExpr` to betaLambdaCache
         - return { betaReduced := betaExpr, prevMVarIdDecls := none }
-/
@[always_inline, inline]
partial def betaLambdaEnv (lam : Expr) (args : Array Expr) : TranslateEnvT BetaLambdaResult := do
  let nbParams := Expr.getNumHeadLambdas lam
  let nbParamsU := nbParams.toUSize
  let nbArgs := args.usize
  if nbArgs == 0
  then return ⟨lam, none⟩
  else if lam.isLambda then
    let nbEffective := if nbParamsU < nbArgs then nbParamsU else nbArgs
    let betaRes ← getBetaReduce lam args nbEffective
    if nbParamsU < nbArgs
    then return { betaRes with betaReduced := ← mkAppRangeExpr betaRes.betaReduced nbParams nbArgs.toNat args }
    else return betaRes
  else return ⟨← mkAppNExpr lam args, none⟩

  where
    getBetaReduce (e : Expr) (args : Array Expr) (nbArgs : USize) : TranslateEnvT BetaLambdaResult := do
      let rec updateAssignments
        (mvars : Array Expr)
        (val : Array Expr) (mAssignments : MVarAssignments)
        (idx : USize) (stop : USize) : MVarAssignments :=
        if idx ≥ stop then mAssignments
        else
          let mAssignments := mAssignments.insert mvars[idx]! val[idx]!
          updateAssignments mvars val mAssignments (idx + 1) stop
      let assignMVars' (mvars : Array Expr) (val : Array Expr) : TranslateEnvT Unit := do
        modifyOptEnv
          fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩ =>
            let mAssignments := updateAssignments mvars val mAssignments 0 nbArgs
            ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩

      let assignMVars (mvars : Array Expr) (val : Array Expr) : TranslateEnvT MVarIdDecls := do
        let decls ← getMVarDecls mvars
        assignMVars' mvars val
        return decls
      let key := mkInstKey e nbArgs
      let cached := (← get).optEnv.memCache.betaLambdaCache.getD key betaCacheMiss
      if !exprEq cached.betaReduced instCacheMiss then
        -- assign mvars with value
        let decls ← assignMVars cached.mvarArgs args
        return {betaReduced := cached.betaReduced, prevMVarIdDecls := decls}
      else
        let nbElems := nbArgs.toNat
        let mvars ←
          Nat.foldM nbElems
           (λ _ _ acc => do return acc.push (← mkExpr (← mkFreshExprMVar none)))
           (Array.emptyWithCapacity nbElems)
        let betaExpr ← betaLambdaShared e mvars
        -- update cache
        let betaDecl := { betaReduced := betaExpr, mvarArgs := mvars }
        updateBetaLambdaCache key betaDecl
        -- assign mvars with value
        assignMVars' mvars args
        return {betaReduced := betaExpr, prevMVarIdDecls := none }


inductive ResolveTypeStack where
 | InitExpr (t : Expr) : ResolveTypeStack
 | ArgsExpr (f : Expr) (args : Array Expr) (idx : Nat) (stop : Nat) : ResolveTypeStack


/-- Same as the default `isProp` but cache result. -/
@[inline]
def isPropEnv (e : Expr) : TranslateEnvT Bool := do
 let e ← if e.hasMVar then instantiateSharedMVars e else pure e
 match (← get).optEnv.memCache.isPropCache.get? e with
 | some b => return b
 | none =>
    let b ← isPropAux e
    updatePropCache e b
    return b

 where
   isPropAux (e : Expr) : TranslateEnvT Bool :=
     withLocalContext $ do
      match (← isPropQuick e) with
      | .true  => return true
      | .false => return false
      | .undef =>
          let isPropType (t : Expr) :=
             match t with
             | Expr.sort u => u.isAlwaysZero
             | _ => false
          return isPropType (← inferTypeEnv e)

@[inline]
def getLevelEnv (t : Expr) : TranslateEnvT Level := do
  match ← inferTypeEnv t with
  | Expr.sort u => return u
  | _ => throwEnvError "getLevelEnv: sort expected for {reprStr t}"

@[always_inline, inline]
def reduceEnvProj? (e : Expr) : TranslateEnvT (Option Expr) := do
  let e ← if e.hasMVar then instantiateSharedMVars e else pure e
  withLocalContext $ do reduceProj? e

@[always_inline, inline]
def projectEnvCore? (e : Expr) (i : Nat) : TranslateEnvT (Option Expr) :=
  -- NOTE : No need to instantiate MVars as projectEnvCore? is used only when `e` has been optimized.
  withLocalContext $ do projectCore? e i


/-- Return `true` is `t` is a potential resolvable type -/
def isResolvableType (t : Expr) : TranslateEnvT Bool := do
  match t with
   | Expr.const n _ =>
        match ← getConstEnvInfo n with
        | cinfo@ (.defnInfo _) =>
             if (← isClassConstraint n) then return false
             let t ← if cinfo.type.hasMVar then instantiateMVars cinfo.type else pure cinfo.type
             match t with
             | Expr.sort u => return !u.isAlwaysZero
             | _ => return false
        | _ => return false
   | _ => return false

/-- Given `t x₀ .. xₙ` a type expression, this function resolves type
    abbreviation by performing the following:
    - When `t := Expr.const n us ∧ `defnInfo(n) := d α₀ ... αₙ`:
       - return `resolveTypeAbbrev $ d (resolveTypeAbbrev x₀) ... (resolveTypeAbbrev xₙ)`
    - Otherwise
       - return `t (resolveTypeAbbrev x₀) ... (resolveTypeAbbrev xₙ)`
-/
private partial def resolveTypeAbbrevAux (s : List ResolveTypeStack) : TranslateEnvT Expr := do
  match s with
  | .InitExpr t :: xs =>
      let (f, args) := getAppFnWithArgs t
      match f with
      | Expr.const n us =>
         match (← getConstEnvInfo n) with
         | cinfo@(ConstantInfo.defnInfo _) =>
            let auxApp ← hashcons (← instantiateValueLevelParams cinfo us)
            resolveTypeAbbrevAux ( .InitExpr (← betaLambdaShared auxApp args) :: xs)
         | _ => resolveTypeAbbrevAux ( .ArgsExpr f args 0 args.size :: xs)
      | _ =>
         match xs with
         | [] => return t
         | .ArgsExpr f args idx stop :: xs =>
              resolveTypeAbbrevAux ( .ArgsExpr f (args.set! idx t) (idx + 1) stop :: xs )
         | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"
  | .ArgsExpr f args idx stop :: xs =>
       if idx ≥ stop then
         let t' ← mkAppNExpr f args
         match xs with
         | [] => return t'
         | .ArgsExpr f' args' idx' stop' :: ys' =>
               resolveTypeAbbrevAux ( .ArgsExpr f' (args'.set! idx' t') (idx' + 1) stop' :: ys' )
         | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"
       else resolveTypeAbbrevAux (.InitExpr args[idx]! :: s)
  | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"


@[inline, always_inline] def resolveTypeAbbrev (t : Expr) : TranslateEnvT Expr := do
  resolveTypeAbbrevAux [.InitExpr t]

/-- Return all fvar expressions in `e`. The return array preserved dependencies between fvars,
    i.e., child fvars appear first.

    TODO: change function to pure tail rec call using stack-based approach
-/
@[inline] partial def getFVarsInExpr (e : Expr) : TranslateEnvT (Array Expr) :=
 let rec @[specialize] visit (e : Expr) (acc : Array Expr) : TranslateEnvT (Array Expr) := do
  if !e.hasFVar then return acc else
    match e with
    | Expr.forallE _ d b _   => visit b (← visit d acc)
    | Expr.lam _ d b _       => visit d (← visit b acc)
    | Expr.mdata _ e         => visit e acc
    | Expr.letE _ t v b _    => visit t (← visit v (← visit b acc))
    | Expr.app f a           => visit a (← visit f acc) -- considering arguments in proper order
    | Expr.proj _ _ e        => visit e acc
    | Expr.fvar _            => return (← visit (← inferTypeEnv e) acc).push e
    | _                      => return acc
 visit e #[]

/-- Return `true` whenever `e` satisfies one of the following:
    - `e` is a sort type;
    - `e` is a const or variable of sort type;
    - `e` is an application that transitively has at least one argument of sort type.
-/
partial def isGenericParam (e : Expr) : TranslateEnvT Bool := do
 match e with
 | Expr.sort .zero -- prop type
 | Expr.lit ..
 | Expr.lam ..
 | Expr.proj ..
 | Expr.letE .. => return false
 | Expr.forallE _n t b _ => isGenericParam t <||> isGenericParam b
 | Expr.sort .. => return true
 | Expr.mdata _ e  => isGenericParam e
 | Expr.const n _ =>
     match (← getConstEnvInfo n) with
     | .defnInfo _ =>
          if (← isInstanceClass n <||> isClassConstraint n) then return false
          -- resolve type abbreviation (if any)
          let t ← resolveTypeAbbrev e
          if !(exprEq t e) then isGenericParam t
          else return false
     | .opaqueInfo _
     | .axiomInfo _ => isGenericParam (← inferTypeEnv e)
     | _ => return false
 | Expr.fvar _ => isGenericParam (← inferTypeEnv e)
 | Expr.app _ arg => isGenericParam arg
 | Expr.bvar _ => throwEnvError "isGenericParam: unexpected bound variable {reprStr e}"
 | Expr.mvar .. => throwEnvError "isGenericParam: unexpected meta variable {reprStr e}"

/-- Helper function for `retrieveGenericFVars` and `retrieveGenericArgs` --/
def updateGenericArgs
  (e : Expr) (gargs : Array Expr)
  (pset : HashSet Expr) : TranslateEnvT (Array Expr × HashSet Expr) := do
 let fvars ← getFVarsInExpr e
 let mut gargs := gargs
 let mut pset := pset
 for h : i in [:fvars.size] do
   let p := fvars[i]
   if !(pset.contains p) then
     gargs := gargs.push p
     pset := pset.insert p
 return (gargs, pset)

/-- Given arguments `params` obtained from getImplicitParameters, perform the following:
      let V := #[α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr params[i] ∧ params[i].isGeneric]
      return V
-/
def retrieveGenericFVars (params : ImplicitParameters) : TranslateEnvT (Array Expr) := do
  let mut genericArgs := #[]
  let mut knownGenParams := (.emptyWithCapacity : HashSet Expr)
  for h : i in [:params.size] do
    let e := params[i]
    if e.isGeneric then
      (genericArgs, knownGenParams) ← updateGenericArgs e.effectiveArg genericArgs knownGenParams
  return genericArgs


/-- Given `params` an implicit parameters perform the following:
      let genArgs ← retrieveGenericFVars
      let P := #[ params[i].effectiveArgs | i ∈ [0..params.size-1] ∧ ¬ params[i].isInstance ]
      return `genArgs ++ P`
-/
@[inline] def getEffectiveParams (params : ImplicitParameters) : TranslateEnvT (Array Expr) := do
  let mut args ← retrieveGenericFVars params
  for h : i in [:params.size] do
    let e := params[i]
    if !e.isInstance then
      args := args.push e.effectiveArg
  return args

/-- Given `f` a function name expression, `params` its implicit parameters info (see `getImplicitParameters`),
    and `fbody` corresponding the recursive definition for `f`, perform the following actions:
      - let fbody' be `fbody` in which the recurisve call is annotated with `_solver.recursivecall`
      - When ∀ i ∈ [0..params.size-1], ¬ params[i].isInstance:
          - return fbody'
      - Otherwise:
          - let genFVars ← retrieveGenericFVars params
          - return mkLambdaFVarsExpr genFVars (specializeLambda fbody' params) (usedOnly := true)
-/
partial def generalizeRecCall (f : Expr) (params: ImplicitParameters) (fbody : Expr) : TranslateEnvT Expr := do
  let fbody' ← replaceShared fbody replacePred
  if !(params.any (λ p => p.isInstance)) then
    return fbody'
  else
    let genFVars ← retrieveGenericFVars params
    mkLambdaFVarsExpr genFVars (← specializeLambda fbody' params)

where
  replacePred (e : Expr) : TranslateEnvT (Option Expr) := do
    if exprEq (e.getAppFn) f
    then tagAsRecursiveCall e
    else return none


/-- Return `fₙ` if `body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ] := fₙ` is already
    in the recursive function map.
    Otherwise,
       - update recursive function map with `body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ] := f`
       - return `f`.
     where:
       - α₁ ... αₖ` correspond to the implicit arguments of `f` that are still polymorphic (if any).
       - `x₁ ... xₙ` correspond to the effective parameters of the recursive call (excluding implicit arguments).
    NOTE:
      - `f` is also removed from the visiting cache.
      - The polymorphic instance cache is updated with `f := body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ]`
        (if required) for all cases. This is essential to avoid performing structural equivalence check again on an
        already handled recursive function.
    Assumes that:

      - `f` is either a function name expression or a fully/partially instantiated polymorphic function (see `getInstApp`)
      - an entry exists for each opaque recursive function in `recFunMap` before optimization is performed
        (see function `cacheOpaqueRecFun`).
-/
partial def storeRecFunDef (f : Expr) (params : ImplicitParameters) (body : Expr) : TranslateEnvT Expr := do
  let body' ← replaceShared body (replacePred (← internalRecFunExpr))
  -- update polymorphic instance cache
  updateRecFunInst f body'
  match (← get).optEnv.recFunMap.get? body' with
  | some fb => return fb
  | none =>
     updateRecFunMap body' f
     return f

where
  replacePred (recFun : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
   match toTaggedRecursiveCall? e with
   | some b =>
        let mut margs := b.getAppArgs
        -- replace any occurrence in args first
        for i in [:margs.size] do
           margs ← margs.modifyM i (λ a => replaceShared a (replacePred recFun))
        if params.isEmpty then
          -- case when function does not have any implicit parameters and is passed as argument (HOF)
          mkAppNExpr recFun margs
        else
          let mut effectiveArgs := #[]
          for h1 : i in [:margs.size] do
             if h2 : i < params.size
             then
               if params[i].isGeneric || !(params[i].isInstance)
               then effectiveArgs := effectiveArgs.push margs[i]
             else effectiveArgs := effectiveArgs.push margs[i] -- case when f is partially applied
          mkAppNExpr recFun effectiveArgs
   | _ => return none

/-- Given `instApp` corresponding either to a function name expression or
    to a fully/partially instantiated polymorphic function (see function `getInstApp`),
    determine if `instApp` has already a mapping in `recFunInstCache`. If so then retrieve the corresponding
    function application in `recFunMap`. Otherwise return `none`.
    An error is triggered if no corresponding entry can be found in `recFunMap`.
-/
def hasRecFunInst? (instApp : Expr) : TranslateEnvT (Option Expr) := do
  let ⟨_, ⟨_, _, _, _, recFunInstCache,_,recFunMap, _, _, _, _, _, _, _⟩⟩ ← get
  match recFunInstCache.get? instApp with
  | some fbody =>
     -- retrieve function application from recFunMap
     match recFunMap.get? fbody with
     | none => throwEnvError "hasRecFunInst: expecting entry for {reprStr fbody} in recFunMap"
     | res => return res
  | none => return none

initialize
  registerTraceClass `Optimize.cacheExpr

end Blaster.Optimize
