import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeProjection
import Blaster.Optimize.Telescope
import Blaster.Optimize.RetentionProfile

open Lean Meta Elab Blaster.Data.HashMap Blaster.Data.HashSet

namespace Blaster.Optimize

abbrev HypsStackContext := Option CtxScope -- context scope to close on exit

instance : Repr (Option MVarIdDecls) where
  reprPrec _ _ := "<MVarIdDecls>"

inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr) (mvarDecls : Option MVarIdDecls := none)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool) (mvarDecls : Option MVarIdDecls)
 | InitOpaqueRecExpr (f : Expr) (args : Array Expr)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters) (startCtxId : CtxId)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr)
                    (startCtxId : CtxId)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (hctx : HypsStackContext) (isProp : Bool)
 | AppWaitForConst (args : Array Expr)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat)
                           (pInfo : FunEnvInfo) (prevInApp : Bool)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo)
                           (mInfo : Option MatchInfo) (prevInApp : Bool)
 | InitNonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
 | NonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat) (prevInCtor : Bool)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (prevInApp : Bool)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (idx : Nat) (mInfo : MatchInfo) (prevInApp : Bool)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | LambdaWaitForBody (x : Expr) (hctx : HypsStackContext) (inDite : Bool) (startCtxId : CtxId)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr)
 | MatchLhsSkipForallType (e : Expr)
 | MatchLhsForallWaitForBody (e : Expr)
 | MatchAltWaitForExpr (params : Array Expr) (hctx : HypsStackContext) (idx : USize) (mInfo : MatchInfo)
 | LetWaitForValue (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 | ProjWaitForExpr (n : Name) (idx : Nat)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) Expr


@[always_inline, inline]
def resetContext (h : HypsStackContext) : TranslateEnvT Unit := do
  match h with
  | some scope => endCtx scope
  | none => return ()


@[always_inline, inline]
def resetChoiceContext (h : HypsStackContext) (fvars : Array Expr) (lam : Expr) (idx : USize) : TranslateEnvT Unit := do
  match h with
  | some scope =>
       updateContextReuseCache lam idx ⟨scope, fvars⟩
       modifyOptEnv
         fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, _, s6, active, s7, s8⟩, o12, o13, o14⟩ =>
             ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, scope.parent, s6, active.erase scope.current, s7, s8⟩, o12, o13, o14⟩
  | none => return ()

def restoreMVarDecls (optDecls : Option MVarIdDecls) : TranslateEnvT Unit :=
  match optDecls with
  | none => pure ()
  | some mdecls =>
      let rec updateAssignments
        (idx : Nat) (stop : Nat) (mdecls : MVarIdDecls)
        (mAssignments : MVarAssignments) : MVarAssignments :=
        if idx ≥ stop then mAssignments
        else
          let d := mdecls[idx]!
          let mAssignments := mAssignments.insert d.mvar d.value
          updateAssignments (idx + 1) stop mdecls mAssignments
      modifyOptEnv
        fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩ =>
          let mAssignments := updateAssignments 0 mdecls.size mdecls mAssignments
          ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩

def isInEqualityMap (e : Expr) (isGlobal : Bool) : TranslateEnvT Expr := do
  if isGlobal then return e
  else
    match (← eqMapFind? e) with
    | none => return e
    | some b => return b

def stackContinuity (stack : List OptimizeStack) (optExpr : Expr) (skipCache := false) : TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] => return Sum.inr optExpr

  | .InitOptimizeReturn e isGlobal mvarDecls :: xs =>
       let optExpr ← isInEqualityMap optExpr isGlobal
       if !skipCache then
         updateOptimizeEnvCache optExpr optExpr isGlobal
         if !e.hasMVar && !exprEq e optExpr then updateOptimizeEnvCache e optExpr isGlobal
       restoreMVarDecls mvarDecls
       match xs with
       | [] => return Sum.inr optExpr
       | _ => stackContinuity xs optExpr

  | .RecFunDefWaitForStorage args instApp subsInst params startCtxId :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr startCtxId :: xs)

  | .ForallWaitForType n bi body :: xs =>
       -- optExpr corresponds to optimized forall binder type
       -- check forall reduction to avoid optimizing body
       let isProp ← isPropEnv (← mkForallExpr n bi optExpr body)
       if let some r ← forallReduction? optExpr body isProp then
         match r with
         | Expr.const ``True _ => stackContinuity xs r
         | _ => return Sum.inl ( .InitOptimizeExpr r :: xs)
       else
         -- continuity with optimizing forall body
          withLocalDecl' n bi optExpr fun x => do
            let body' ← instantiateShared1 body x
            let mscope ← addHypotheses optExpr x (isPropBody := isProp)
            return Sum.inl ( .InitOptimizeExpr body' :: .ForallWaitForBody x optExpr mscope isProp :: xs)

  | .ForallWaitForBody x t hctx isProp :: xs =>
       -- optExpr corresponds to optimized forall body
       -- continuity with applying forall normalization rules.
       let e ← optimizeForall x t optExpr hctx isProp
       resetContext hctx
       if ← isRestart then
         resetRestart
         return Sum.inl (.InitOptimizeExpr e :: xs)
       else -- continuity with optimizing next expression
         stackContinuity xs e

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- reset inFunApp flag
       setInFunApp false
       -- check if optExpr is a lambda
       if optExpr.isLambda then
         -- perform beta reduction and apply optimization
         let betaRes ← betaLambdaEnv optExpr (← resolveMVarsArgs #[] args)
         return Sum.inl (.InitOptimizeExpr betaRes.betaReduced betaRes.prevMVarIdDecls :: xs)
       else
         let (rf, extraArgs) := getAppFnWithArgs optExpr
         let args ← resolveMVarsArgs extraArgs args
         let is_match ← isMatchExpr rf
         if (← isNotFun rf <&&> pure !is_match) then
            return Sum.inl (.InitNonFunOptimizeArgs rf args extraArgs.size args.size :: xs)
         else
           let pInfo ← getFunEnvInfo rf
           -- apply optimization on match generic instance (if necessary)
           match (← hasUnOptMatchInfo? rf) with
           | none =>
              -- continuity with optimization on implicit arguments
              let prevInApp ← isAppArg
              if !(isBlasterDiteConst rf) then setIsAppArg true
              return Sum.inl (.AppOptimizeImplicitArgs rf args extraArgs.size extraArgs.size args.size pInfo prevInApp :: xs)
           | some (mInfo, instApp) =>
              -- continuity with optimizing match generic instance
              -- NOTE: instApp is expected to be a lambda term
              -- NOTE: we here only want to optimize the lambda params type, which mainly
              -- correspond to the match lhs.
              match instApp with
              | Expr.lam n t b bi =>
                    let mWait := .OptimizeMatchInfoWaitForInst rf args extraArgs.size pInfo mInfo :: xs
                    -- NOTE: we only optimize the lhs forall body and not the types.
                    return Sum.inl (.MatchLhsSkipForallType t :: .MatchRhsLambdaWaitForType n bi b :: mWait)
              | _ => throwEnvError "stackContinuity: lambda expected for match instance but got {reprStr instApp}"


  | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo :: xs =>
       -- optExpr corresponds to optimized match generic instance
       -- update cache isMatcherCache
       if let Expr.const n _ := f then
         let argInfo := ({ name := n, nameExpr := f, instApp := optExpr, recInfo := mInfo } : MatchInfo)
         updateIsMatcherCache n argInfo
         -- apply optimization only on implicit parameters to remove mdata annotation
         -- we don't consider explicit parameters at this stage to avoid performing
         -- optimization on unreachable arguments
         let prevInApp ← isAppArg
         return Sum.inl (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo prevInApp :: xs)
       else throwEnvError "stackContinuity: name expression for match application but got {reprStr f} !!!"

  | .NonFunOptimizeArgs f args idx stopIdx prevInCtor :: xs =>
       -- optExpr corresponds to the optimized non-fun argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       return Sum.inl (.NonFunOptimizeArgs f (args.set! idx optExpr) (idx + 1) stopIdx prevInCtor :: xs)

  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized implicit argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       return Sum.inl (.AppOptimizeImplicitArgs f (args.set! idx optExpr) (idx + 1) startArgIdx stopIdx pInfo prevInApp :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized explicit argument referenced by idx.
       -- continuity with optimizing the next explicit argument.
       return Sum.inl (.AppOptimizeExplicitArgs f (args.set! idx optExpr) (idx + 1) stopIdx pInfo mInfo prevInApp :: xs)

  | .DiteChoiceWaitForCond f args pInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized Blaster.dite' conditional, i.e., referenced by index 1.
       -- When some r ← optimizeDiteChoice f (args.set! 1 optExpr)
       --  - continuity with optimizing `r`
       -- Otherwise
       --  - continuity with optimizing remaining explicit parameters before reduction
       -- set isAppArg to keep context for eventual constant match.
       setIsAppArg true
       if let some r ← optimizeDITEChoice f (args.set! 1 optExpr) then
           return Sum.inl (.InitOptimizeExpr r :: xs)
       else
          return Sum.inl (.AppOptimizeExplicitArgs f (args.set! 1 optExpr) 2 args.size pInfo none prevInApp :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       return Sum.inl (.MatchChoiceOptimizeDiscrs f (args.set! idx optExpr) pInfo (idx + 1) mInfo prevInApp :: xs)

  | .LambdaWaitForType n bi body :: xs =>
       -- optExpr corresponds to optimized lambda type
       withLocalDecl' n bi optExpr fun x => do
         let bodyOpt := .InitOptimizeExpr (← instantiateShared1 body x)
         -- NOTE: keeping track of next ctxId to clean-up rewrite cache
         let nextCtxId := (← get).optEnv.options.nextCtxId
         return Sum.inl (bodyOpt :: .LambdaWaitForBody x none false nextCtxId :: xs)

  | .LambdaWaitForBody x hctx inDite startCtxId :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       let e ← mkLambdaFVarExpr x optExpr
       if inDite then
         if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
         resetChoiceContext hctx #[x] e 0
         stackContinuity xs e
       else
         -- clean-up rewrite cache
         freeRewriteCacheRange startCtxId (← get).optEnv.options.nextCtxId
         stackContinuity xs e

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalDecl' n bi optExpr fun x => do
          let bodyOpt := .MatchRhsLambdaNext (← instantiateShared1 body x)
          return Sum.inl (bodyOpt :: .MatchRhsLambdaWaitForBody x :: xs)

  | .MatchRhsLambdaWaitForBody x :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        let e ← mkLambdaFVarExpr x optExpr
        stackContinuity xs e

  | .MatchAltWaitForExpr params hctx idx mInfo :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       let e ← mkLambdaFVarsExpr params optExpr
       if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
       resetChoiceContext hctx params mInfo.nameExpr idx
       stackContinuity xs e

  | .MatchLhsForallWaitForBody x :: xs =>
       -- optExpr corresponds to the optimized lhs forall body
       -- continuity with optimizing next expression
       let e ← mkForallFVarExpr x optExpr
       stackContinuity xs e

  | .LetWaitForValue body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       return Sum.inl (.InitOptimizeExpr (← instantiateShared1 body optExpr) :: xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       stackContinuity xs (← mkMDataExpr d optExpr)

  | .ProjWaitForExpr n idx :: xs =>
      -- optExpr corresponds to optimized projection structure
      if let some re ← optimizeProjection? n idx optExpr then
         return Sum.inl (.InitOptimizeExpr re :: xs)
      else
        -- continuity with optimizing next expression
        stackContinuity xs (← mkProjExpr n idx optExpr)

  | _ => throwEnvError "stackContinuity: unexpected optimize stack continuity {reprStr stack} !!!"

  where
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
          let matchFun ← hashcons (← instantiateValueLevelParams cInfo l)
          return some (mInfo, matchFun)
        else return none
      else return none

    @[always_inline, inline]
    resolveMVarsArgs (extra_args : Array Expr) (args : Array Expr) : TranslateEnvT (Array Expr) := do
      let mAssignments := (← get).optEnv.mAssignments
      let rec visit (idx : Nat) (stop : Nat) (args : Array Expr) : Array Expr :=
         if idx ≥ stop then args
         else
           let e := args[idx]!
           match e with
           | Expr.mvar _ => visit (idx + 1) stop (args.set! idx (getEnvMVarValue' e mAssignments))
           | _ => visit (idx + 1) stop args
      let rec visit'
          (idx : Nat) (offset : Nat) (stop : Nat)
          (extra_args : Array Expr) (args : Array Expr) (pargs : Array Expr) : Array Expr :=
         if idx ≥ stop then pargs
         else
           let p := if idx < offset then extra_args[idx]! else args[idx - offset]!
           match p with
           | Expr.mvar _ => visit' (idx + 1) offset stop extra_args args (pargs.push (getEnvMVarValue' p mAssignments))
           | _ => visit' (idx + 1) offset stop extra_args args (pargs.push p)
      let extra_size := extra_args.size
      if mAssignments.size == 0 then
        -- no mvar assignments: resolution is the identity, only concatenation remains
        if extra_size == 0 then return args
        else return extra_args ++ args
      else if extra_size == 0 then
        return visit 0 args.size args
      else
        let stop := extra_size + args.size
        return visit' 0 extra_size stop extra_args args (Array.emptyWithCapacity stop)


/-! ## Hash-cons GC v2 — mark-and-rebuild

v1 (bulk clear, `maybeGCHashCons`) hangs: the intern table's entries are
load-bearing identity/visited state. v2 instead computes the transitive
pointer closure of every Expr the rest of the run can still touch (driver
stack + semantic env state) and FILTERS by reachability:

* `hashConsCache`: keep entries whose canonical node is marked;
* the `InstKey`-keyed caches (`betaLambdaCache`, `contextReuseCache`):
  keep entries whose embedded pointer address (low 47 bits of `packed`)
  is marked — unmarked keys' objects may be freed and their addresses
  recycled, which would produce wrong hits;
* the `PtrExpr`-keyed memo caches: cleared (recomputable; any traversal
  the future performs starts from marked roots, whose entries survive
  in the table, so no exponential re-expansion is possible).

Dropping a REACHABLE entry can never happen (mark is a superset of use);
dropping an unreachable one costs at most re-interning (linear, self-
populating) and cross-time sharing. Controlled by `BLASTER_HASHCONS_GC=<n>`
(fire threshold, 0=off) and `BLASTER_GC_MASK` (bit1=clear memo caches,
bit2=filter InstKey caches; the table rebuild always runs). -/

section GCv2

/-- Mark-set key: a pointer address as a `Nat` inside a single-field
    structure. Addresses are < 2^47 so the `Nat` is a tagged immediate, and
    the trivial single-field wrapper is erased at runtime — zero allocation
    per stored entry (a `USize` field would box). The dedicated type also
    carries its own `Hashable` (the pointer mixer — core's near-identity
    `Nat` hash would cluster 16-byte-aligned addresses) without shadowing
    `instHashableNat`, which is baked into `CtxId`-keyed map types. -/
private structure GCAddr where
  a : Nat
private instance : BEq GCAddr := ⟨fun x y => x.a == y.a⟩
private instance : Hashable GCAddr := ⟨fun x => ptrAddrHash (USize.ofNat x.a)⟩
private instance : Inhabited GCAddr := ⟨⟨0⟩⟩

private abbrev GCMark := HashSet GCAddr

private unsafe def gcAddrAux (e : Expr) : GCAddr := ⟨(ptrAddrUnsafe e).toNat⟩
@[inline] private def gcAddr (e : Expr) : GCAddr := unsafe gcAddrAux e

/-- GCT instrumentation (TEMPORARY, root-sweep cost diagnosis): borrow-only
    physical address of an `Array Expr`; an address change between two
    observations of the same `mut` array means a reallocation happened
    (copy-on-write if not a capacity growth). `ptrAddrUnsafe` takes its
    argument `@&`, so this is RC-traffic-free. -/
private unsafe def gcArrAddrAux (a : Array Expr) : Nat := (ptrAddrUnsafe a).toNat
@[inline] private def gcArrAddr (a : Array Expr) : Nat := unsafe gcArrAddrAux a

/-- GCT instrumentation: append one line to `$BLASTER_RETENTION_PROFILE.gct`. -/
private def gcTimeLog (line : String) : IO Unit := do
  match ← IO.getEnv "BLASTER_RETENTION_PROFILE" with
  | some p => IO.FS.withFile (p ++ ".gct") .append fun h => h.putStrLn line
  | none => pure ()

/-- Iterative pointer-closure mark: visits each distinct physical node once.
    Membership is detected by insert-then-size-delta — one table probe per
    visit instead of `contains` + `insert`. -/
private def gcMark (roots : Array Expr) : GCMark := Id.run do
  let mut marked : GCMark := HashSet.emptyWithCapacity 262144
  let mut stk : Array Expr := roots
  while stk.size > 0 do
    let e := stk.back!
    stk := stk.pop
    let szBefore := marked.size
    marked := marked.insert (gcAddr e)
    if marked.size == szBefore then
      continue  -- already visited
    match e with
    | .app f a => stk := (stk.push f).push a
    | .lam _ d b _ => stk := (stk.push d).push b
    | .forallE _ d b _ => stk := (stk.push d).push b
    | .letE _ t v b _ => stk := ((stk.push t).push v).push b
    | .mdata _ b => stk := stk.push b
    | .proj _ _ b => stk := stk.push b
    | _ => pure ()
  return marked

/-- Exprs held by one driver-stack frame. -/
private def gcFrameExprs (rs : Array Expr) (f : OptimizeStack) : Array Expr := Id.run do
  let mut rs := rs
  let pushDecls (rs : Array Expr) (mds : Option MVarIdDecls) : Array Expr := Id.run do
    let mut rs := rs
    if let some ds := mds then
      for d in ds do
        rs := (rs.push d.mvar).push d.value
    return rs
  let pushParams (rs : Array Expr) (ps : ImplicitParameters) : Array Expr := Id.run do
    let mut rs := rs
    for p in ps do
      rs := rs.push p.effectiveArg
    return rs
  let pushMInfo (rs : Array Expr) (m : MatchInfo) : Array Expr :=
    (rs.push m.nameExpr).push m.instApp
  match f with
  | .InitOptimizeExpr e mds => rs := pushDecls (rs.push e) mds
  | .InitOptimizeReturn e _ mds => rs := pushDecls (rs.push e) mds
  | .InitOpaqueRecExpr g args => rs := (rs.push g) ++ args
  | .RecFunDefWaitForStorage args instApp subsInts params _ =>
      rs := pushParams (((rs ++ args).push instApp).push subsInts) params
  | .RecFunDefStorage args instApp subsInts params optBody _ =>
      rs := pushParams ((((rs ++ args).push instApp).push subsInts).push optBody) params
  | .ForallWaitForType _ _ body => rs := rs.push body
  | .ForallWaitForBody x t _ _ => rs := (rs.push x).push t
  | .AppWaitForConst args => rs := rs ++ args
  | .OptimizeMatchInfoWaitForInst g args _ pInfo _ =>
      rs := ((rs.push g) ++ args).push pInfo.type
  | .AppOptimizeImplicitArgs g args _ _ _ pInfo _ =>
      rs := ((rs.push g) ++ args).push pInfo.type
  | .AppOptimizeExplicitArgs g args _ _ pInfo mInfo? _ =>
      rs := ((rs.push g) ++ args).push pInfo.type
      if let some m := mInfo? then rs := pushMInfo rs m
  | .InitNonFunOptimizeArgs g args _ _ => rs := (rs.push g) ++ args
  | .NonFunOptimizeArgs g args _ _ _ => rs := (rs.push g) ++ args
  | .DiteChoiceWaitForCond g args pInfo _ => rs := ((rs.push g) ++ args).push pInfo.type
  | .MatchChoiceOptimizeDiscrs g args pInfo _ mInfo _ =>
      rs := pushMInfo (((rs.push g) ++ args).push pInfo.type) mInfo
  | .LambdaWaitForType _ _ body => rs := rs.push body
  | .LambdaWaitForBody x _ _ _ => rs := rs.push x
  | .MatchRhsLambdaWaitForType _ _ body => rs := rs.push body
  | .MatchRhsLambdaNext e => rs := rs.push e
  | .MatchRhsLambdaWaitForBody x => rs := rs.push x
  | .MatchLhsSkipForallType e => rs := rs.push e
  | .MatchLhsForallWaitForBody e => rs := rs.push e
  | .MatchAltWaitForExpr params _ _ mInfo => rs := pushMInfo (rs ++ params) mInfo
  | .LetWaitForValue body => rs := rs.push body
  | .MDataRecCallWaitForExpr _ => pure ()
  | .ProjWaitForExpr _ _ => pure ()
  return rs

/-- Every Expr the rest of the run can still touch: driver stack frames plus
    the semantic state in `TranslateEnv` (rewrite caches, hypothesis /
    equality / pattern maps, recFun registrations, mvar assignments, local
    context, local instances). Derived memo caches are deliberately NOT
    roots — they are recomputable and would defeat the collection. -/
private def gcCollectRoots (stack : List OptimizeStack) (liveCtxs : HashSet Nat) : TranslateEnvT (Array Expr) := do
  let o := (← get).optEnv
  -- GCT instrumentation (TEMPORARY): per-section wall clock + rs.size, and
  -- reallocation counters on one bind-crossing section (rewriteCache) and
  -- one pure section (inferTypeCache) to discriminate copy-on-write.
  let dbg ← Retention.enabledIO
  let mut gt ← IO.monoMsNow
  let mut gl : String := ""
  let mut rs : Array Expr := Array.emptyWithCapacity 8192
  for f in stack do
    rs := gcFrameExprs rs f
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" stack={t-gt}/{rs.size}"; gt := t
  let mut cpRw := 0
  let mut pa := gcArrAddr rs
  for (ctx, ref) in o.rewriteCache.pairs do
    if liveCtxs.contains ctx then
      if gcArrAddr rs != pa then cpRw := cpRw + 1
      for (k, v) in (← ref.get).pairs do
        rs := (rs.push k.expr).push v
      pa := gcArrAddr rs
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" rewrite={t-gt}/{rs.size}/cp{cpRw}"; gt := t
  for (k, ref) in o.hypothesisContext.hypothesisMap.pairs do
    rs := rs.push k.expr
    for (_, v) in (← ref.get) do
      rs := rs.push v
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" hyp={t-gt}/{rs.size}"; gt := t
  for (k, ref) in o.hypothesisContext.equalityMap.pairs do
    rs := rs.push k.expr
    for (_, v) in (← ref.get) do
      rs := rs.push v
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" eq={t-gt}/{rs.size}"; gt := t
  for (k, ref) in o.matchInContext.pairs do
    rs := rs.push k.expr
    for (_, sref) in (← ref.get) do
      for p in (← sref.get).vals do
        rs := rs.push p.expr
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" matchIn={t-gt}/{rs.size}"; gt := t
  for (k, v) in o.recFunInstCache.pairs do
    rs := (rs.push k.expr).push v
  for (k, v) in o.recFunMap.pairs do
    rs := (rs.push k.expr).push v
  for k in o.recFunCache.vals do
    rs := rs.push k.expr
  for (k, v?) in o.synthInstanceCache.pairs do
    rs := rs.push k.expr
    if let some v := v? then rs := rs.push v
  for (k, v) in o.matchCache.pairs do
    rs := (rs.push k.expr).push v
  for (k, v) in o.mAssignments.pairs do
    rs := (rs.push k.expr).push v
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" recEtc={t-gt}/{rs.size}"; gt := t
  -- decls is a PersistentArray; iterating it directly in this deep monad
  -- measured 212 us/element (54.8 s of a 54.9 s sweep — the entire "GC
  -- stall"). Flatten to an Array first (pure, fast), then iterate.
  for d? in o.ctx.ctx.decls.toArray do
    if let some d := d? then
      rs := rs.push d.type
      if let some v := d.value? then rs := rs.push v
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" decls={t-gt}/{rs.size}"; gt := t
  for inst in o.ctx.localInsts do
    rs := rs.push inst.fvar
  -- ALL alive holders are roots — marking an alive object costs no memory
  -- (it is retained regardless); it only preserves its table entry and so
  -- its identity, preventing twin-minting churn. Memo caches retain their
  -- keys AND values, so both are alive holders:
  for e in ← Retention.gcExtraRootsRef.get do
    rs := rs.push e
  let m := o.memCache
  let mut cpIt := 0
  pa := gcArrAddr rs
  for (k, v) in m.inferTypeCache.pairs do
    if gcArrAddr rs != pa then cpIt := cpIt + 1
    rs := (rs.push k.expr).push v
    pa := gcArrAddr rs
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" inferT={t-gt}/{rs.size}/cp{cpIt}"; gt := t
  for (k, v) in m.getFunEnvInfoCache.pairs do
    rs := (rs.push k.expr).push v.type
  for (k, v?) in m.getFunBodyCache.pairs do
    rs := rs.push k.expr
    if let some v := v? then rs := rs.push v
  for (k, _) in m.isPropCache.pairs do
    rs := rs.push k.expr
  for (k, _) in m.isNotFunCache.pairs do
    rs := rs.push k.expr
  for (k, vs) in m.matchAltsCache.pairs do
    rs := (rs.push k.expr) ++ vs
  for (k, _) in m.genericMatchCache.pairs do
    rs := rs.push k.expr
  for (k, v) in m.forallMetaCache.pairs do
    rs := (rs.push k.expr).push v.instExpr
  for k in m.isCtorMatchPropCache.vals do
    rs := rs.push k.expr
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" memA={t-gt}/{rs.size}"; gt := t
  for (_, ref) in m.contextReuseCache.pairs do
    for (_, scope) in (← ref.get).pairs do
      rs := rs ++ scope.fvars
  if dbg then let t ← IO.monoMsNow; gl := gl ++ s!" ctxReuse={t-gt}/{rs.size}"; gt := t
  for (_, v) in m.betaLambdaCache.pairs do
    rs := (rs.push v.betaReduced) ++ v.mvarArgs
  -- PtrName-keyed caches whose VALUES hold hot alive Exprs (previously the
  -- unrooted twin sources): match-instance apps re-entered by every match
  -- reduction, and constant-definition bodies
  for (_, v) in m.isMatcherCache.pairs do
    rs := (rs.push v.nameExpr).push v.instApp
  for (_, ci) in m.getConstInfoCache.pairs do
    rs := rs.push ci.type
    if let some val := ci.value? then rs := rs.push val
  if dbg then
    let t ← IO.monoMsNow
    gl := gl ++ s!" tail={t-gt}/{rs.size}"
    gcTimeLog s!"roots{gl}"
  return rs

/-- Address embedded in an `InstKey` (low 47 bits of `packed`). -/
@[inline] private def gcInstKeyAddr (k : InstKey) : GCAddr :=
  ⟨k.packed &&& ((1 <<< 47) - 1)⟩

/-- Context ids whose rewrite maps remain REACHABLE: the active ancestor
    chain (the only thing `findAncestorCache` consults) plus, transitively,
    contexts a surviving `contextReuseCache` entry could reactivate
    (`setAndCommitCtx` fires only when the entry's recorded parent is the
    then-current ctx, so reachability propagates parent→scope). Conservative:
    ignores lambda liveness, so it may keep a few maps whose reuse entry is
    later dropped — safe, never the reverse. Maps of ids outside this set
    are erased by `gcRebuild`: they are invisible to lookups and were the
    dominant dead-weight the marker previously treated as roots. -/
private def gcLiveCtxs : TranslateEnvT (HashSet Nat) := do
  let o := (← get).optEnv
  let mut live : HashSet Nat := HashSet.emptyWithCapacity 1024
  let mut work : Array Nat := Array.emptyWithCapacity 1024
  live := live.insert 0
  work := work.push 0
  -- seed: the FULL active set (covers `withParentHyps` windows and any
  -- chain subtleties), plus the explicit parent chain from curCtx
  for ctx in o.options.active.vals do
    if !live.contains ctx then
      live := live.insert ctx
      work := work.push ctx
  let mut ctx := o.options.curCtx
  let mut fuel := 1000000
  while ctx != 0 && fuel > 0 do
    if !live.contains ctx then
      live := live.insert ctx
      work := work.push ctx
    ctx := o.options.parents.getD ctx 0
    fuel := fuel - 1
  -- reuse reachability as BFS over a once-built adjacency (parent →
  -- reactivatable ctxs): O(edges), no ref re-reads, no fixed-point rounds
  -- (the round-scanning version measured ~200 s per collection).
  -- Buckets are LISTS: `(adj.getD p #[]).push c` on Arrays borrows the
  -- bucket while the map still holds it, copying the whole bucket per
  -- edge — O(k²) per parent, ~180 s per collection measured. Cons shares
  -- the tail: O(1) per edge, no copy.
  let mut adj : HashMap Nat (List Nat) := HashMap.emptyWithCapacity 4096
  for (_, ref) in o.memCache.contextReuseCache.pairs do
    for (parent, scope) in (← ref.get).pairs do
      adj := adj.insert parent (scope.scope.current :: adj.getD parent [])
  while work.size > 0 do
    let p := work.back!
    work := work.pop
    for c in adj.getD p [] do
      if !live.contains c then
        live := live.insert c
        work := work.push c
  return live

private def gcRebuild (marked : GCMark) (liveCtxs : HashSet Nat) : TranslateEnvT Nat := do
  let mask ← Retention.gcMaskRef.get
  let o := (← get).optEnv
  -- table: keep marked canonicals. Bit 16 = KEEP-ALL control experiment
  -- (mark+sweep+rebuild with zero drops): separates rebuild mechanics from
  -- eviction semantics as the stall trigger.
  let survivors := if mask &&& 16 != 0 then o.hashConsCache.vals
    else o.hashConsCache.vals.filter fun se => marked.contains (gcAddr se.expr)
  let live := survivors.size
  let table := survivors.foldl (init := HashSet.emptyWithCapacity (max 4096 (live * 2))) fun t se => t.insert se
  -- rewrite maps: erase contexts no lookup or reactivation should reach.
  -- OPT-IN (mask bit 8): the 2026-08-05 run measured iteration inflation
  -- 25.86 M → 35 M+ with erasure on, i.e. some erased maps DO get probed
  -- again — with erasure off those probes still hit (kept maps stay
  -- intact), so the invariant must hold while the table still collects.
  let rewrite := if mask &&& 8 != 0 then
    o.rewriteCache.pairs.foldl
      (init := (HashMap.emptyWithCapacity 4096 : RewriteCacheMap)) fun m (ctx, ref) =>
        if liveCtxs.contains ctx then m.insert ctx ref else m
    else o.rewriteCache
  modifyOptEnv fun o => Id.run do
    let mut o := { o with hashConsCache := table, rewriteCache := rewrite }
    if mask &&& 2 != 0 then
      -- FILTER by key liveness, do not clear: cleared memo caches push the
      -- tail's giant terms onto Lean's inferType/whnf, which runs here with
      -- heartbeats disabled — any excursion there is a silent unbounded
      -- stall. Live-keyed entries keep absorbing that traffic.
      let keepM {β} (m : HashMap PtrExpr β) : HashMap PtrExpr β :=
        m.pairs.foldl (init := (HashMap.emptyWithCapacity 4096 : HashMap PtrExpr β)) fun acc (k, v) =>
          if marked.contains (gcAddr k.expr) then acc.insert k v else acc
      o := { o with memCache := { o.memCache with
        inferTypeCache := keepM o.memCache.inferTypeCache
        getFunEnvInfoCache := keepM o.memCache.getFunEnvInfoCache
        getFunBodyCache := keepM o.memCache.getFunBodyCache
        isPropCache := keepM o.memCache.isPropCache
        isNotFunCache := keepM o.memCache.isNotFunCache
        matchAltsCache := keepM o.memCache.matchAltsCache
        genericMatchCache := keepM o.memCache.genericMatchCache
        forallMetaCache := keepM o.memCache.forallMetaCache
        isCtorMatchPropCache := o.memCache.isCtorMatchPropCache.vals.foldl
          (init := (HashSet.emptyWithCapacity 4096 : HashSet PtrExpr)) fun acc k =>
            if marked.contains (gcAddr k.expr) then acc.insert k else acc } }
    if mask &&& 4 != 0 then
      let bl := o.memCache.betaLambdaCache.pairs.foldl
        (init := (HashMap.emptyWithCapacity 1024 : BetaLambdaMap)) fun m (k, v) =>
          if marked.contains (gcInstKeyAddr k) then m.insert k v else m
      let cr := o.memCache.contextReuseCache.pairs.foldl
        (init := (HashMap.emptyWithCapacity 1024 : ContextReuseMap)) fun m (k, v) =>
          if marked.contains (gcInstKeyAddr k) then m.insert k v else m
      o := { o with memCache := { o.memCache with betaLambdaCache := bl, contextReuseCache := cr } }
    return o
  return live

/-- v2 GC trigger: one `IO.Ref` read per driver iteration when disabled;
    two reads and NO writes on the armed not-yet path (the rearm point is
    initialized once and then written only by collections). Rearm is
    proportional — `live + max(interval, live)` — so total GC work stays
    O(total interns) with geometrically spaced pauses. -/
def maybeGCv2 (stack : List OptimizeStack) : TranslateEnvT Unit := do
  let interval ← Retention.gcIntervalRef.get
  if interval == 0 then return ()
  let nextFire ← Retention.gcNextFireRef.get
  if nextFire == 0 then
    Retention.gcNextFireRef.set interval
    return ()
  if (← get).optEnv.hashConsCache.size < nextFire then
    return ()
  let t0 ← IO.monoMsNow
  Retention.gcRunsRef.modify (· + 1)
  let mask ← Retention.gcMaskRef.get
  -- component-isolation bits (stall bisection): 32 = observe-only (read
  -- sweep + mark, ZERO mutations); 64 = rebuild-without-sweep (skip root
  -- collection and marking entirely; combine with 16 for keep-all)
  if mask &&& 32 != 0 then
    let liveCtxs ← gcLiveCtxs
    let tA ← IO.monoMsNow
    let roots ← gcCollectRoots stack liveCtxs
    let tB ← IO.monoMsNow
    let marked := gcMark roots
    let tC ← IO.monoMsNow
    if ← Retention.enabledIO then
      gcTimeLog s!"m33 livectx={tA-t0} roots={tB-tA}/{roots.size} mark={tC-tB}/{marked.size}"
    Retention.gcLiveRef.set marked.size
    let sz := (← get).optEnv.hashConsCache.size
    Retention.gcNextFireRef.set (sz + interval)
    Retention.gcPauseMsRef.modify (· + ((← IO.monoMsNow) - t0))
    return ()
  let (marked, liveCtxs) ←
    if mask &&& 64 != 0 then
      pure ((HashSet.emptyWithCapacity 8 : GCMark), (HashSet.emptyWithCapacity 8 : HashSet Nat))
    else do
      let liveCtxs ← gcLiveCtxs
      let tLc ← IO.monoMsNow
      Retention.gcLiveCtxMsRef.modify (· + (tLc - t0))
      let roots ← gcCollectRoots stack liveCtxs
      let t1 ← IO.monoMsNow
      Retention.gcRootsMsRef.modify (· + (t1 - t0))
      let marked := gcMark roots
      Retention.gcMarkMsRef.modify (· + ((← IO.monoMsNow) - t1))
      pure (marked, liveCtxs)
  let t2 ← IO.monoMsNow
  let live ← gcRebuild marked liveCtxs
  Retention.gcLiveRef.set live
  Retention.gcNextFireRef.set (live + max interval live)
  let t3 ← IO.monoMsNow
  Retention.gcRebuildMsRef.modify (· + (t3 - t2))
  Retention.gcPauseMsRef.modify (· + (t3 - t0))

end GCv2

@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else stackContinuity stack e

/-- Apply simplification/normalization rules on Blaster.dite' expressions.
    Assume that f = Expr.const ``Blaster.dite'.
-/
@[always_inline, inline]
def optimizeIfThenElse? (f : Expr) (args : Array Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
   mkOptimizeContinuity (← optimizeDITE f args) stack

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) (mvarDecls : Option MVarIdDecls) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  -- retention profiling: one driver iteration (no-op unless BLASTER_RETENTION_PROFILE is set)
  if ← Retention.due then Retention.sample "tick" stack.length
  -- hash-cons GC v2, mark-and-rebuild (no-op unless BLASTER_HASHCONS_GC is set)
  maybeGCv2 stack
  let env ← get
  -- NOTE: Always consider global context when `a` does not contain any FVar/MVar
  let isGlobal := !(hasVar a) || isGlobalContext env
  let useCache := !a.hasMVar
  if useCache then
    let cached := ← isInOptimizeCache? a isGlobal env
    if !exprEq cached instCacheMiss then Sum.inr <$> stackContinuity stack cached
    else
      -- retention diagnostics (p0a): would this local miss have hit
      -- another context's cache? No-op unless profiling is enabled.
      if !isGlobal then Retention.probeWouldHit a env
      return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)
  else return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)

  where
    hasVar (e : Expr) : Bool := e.hasFVar || e.hasMVar

end Blaster.Optimize
