import Blaster.Proof.Explore.Chc
import Blaster.Proof.Induction.Observed
import Blaster.Proof.Induction.ObserverFacts
import Blaster.Proof.Library
import Blaster.Proof.Export.Basic

/-!
Connect symbolic exploration to ordinary theorem proving. Search proposes
invariants; replay creates closed obligations, whose proofs are checked before
the original goal is assigned. No script-specific theorem or state table is
accepted by this interface.
-/
namespace Blaster.Proof.Explore.Frontend
open Lean Meta Elab Tactic
open Blaster.Proof

register_option blaster.explore.enabled : Bool := {
  defValue := true
  descr := "Use symbolic exploration for observed fuel-recursive machines" }
register_option blaster.explore.timeoutMs : Nat := {
  defValue := 900000
  descr := "Maximum solver time for an explorer invariant search" }

/-- Proves a closed proposition (the second argument) from facts, or answers `none`. -/
abbrev FactProver := Array Expr → Expr → TermElabM (Option Expr)

/-- Reuse closed proofs between cases of one theorem. A successful proof is
independent of the facts offered to search; failed attempts retain those facts
in their key. Worker-private declarations are never cached. -/
private def memoizeProver (prove : FactProver) : TermElabM FactProver := do
  let proved ← IO.mkRef ({} : Std.HashMap Expr Expr)
  let failed ← IO.mkRef ({} : Std.HashSet (Array Expr × Expr))
  let sharedEnv ← getEnv
  return fun facts target => do
    if target.hasFVar || target.hasMVar then return ← prove facts target
    if let some proof := (← proved.get)[target]? then return some proof
    let key := (facts, target)
    if (← failed.get).contains key then return none
    let result ← prove facts target
    match result with
    | none => failed.modify (·.insert key)
    | some pr =>
      if !pr.hasFVar && !pr.hasMVar && !pr.hasSorry && pr.getUsedConstants.all sharedEnv.contains then
        proved.modify (·.insert target pr)
    return result

/-- Report progress on standard error, with the seconds since `start` and the
goal it concerns, if any (see `blaster.explore.progress`). -/
private def progress (start : Nat) (s : String) (label : String := "") : CoreM Unit := do
  if ← progressEnabled then
    (← IO.getStderr).putStrLn s!"[explore {label}{((← IO.monoMsNow) - start) / 1000}s] {s}"

/-- The conjuncts of `e` (through nested `∧`), appended to `acc`. -/
partial def conjunctsOf (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjunctsOf e.appArg! (conjunctsOf e.appFn!.appArg! acc) else acc.push e

/-- `∀ xs, c` restricted to the premises that share variables with `c`
(transitively), and the closed ones (a closed premise such as `false = true`
can be the contradiction that proves `c`): the other premises cannot matter for
a closed condition whose binders are independent. Binders are kept when used. -/
private def sliceVCParts (xs : Array Expr) (c : Expr) (facts : Array Expr := #[])
    (allPremiseMatches : Bool := false) : MetaM (Array Expr × Array Expr × Expr) := do
  let props ← xs.filterM fun x => do isProp (← inferType x)
  let mut rel : FVarIdSet := (collectFVars {} c).fvarSet
  let mut keep : Array Expr := #[]
  let mut changed := true
  while changed do
    changed := false
    for h in props do
      if keep.contains h then continue
      let fs := (collectFVars {} (← instantiateMVars (← inferType h))).fvarIds
      if fs.isEmpty || !c.hasFVar || fs.any rel.contains then
        keep := keep.push h
        for f in fs do rel := rel.insert f
        changed := true
  -- binders: the used non-propositional ones, in the original order
  let binders := xs.filter fun x => rel.contains x.fvarId! || keep.contains x
  -- instances of the proved facts at the condition's own terms, as premises
  let hypTys ← keep.mapM fun h => do instantiateMVars (← inferType h)
  -- Replay retains intermediate results as equations (`f x = r`, `r = ok y`).
  -- Match library premises against the combined equation too, so a fact about
  -- the successful value is instantiated at y. These expressions only guide
  -- matching: every returned instance is still reconstructed from its theorem,
  -- and the solver must establish its premises from the original hypotheses.
  let mut replacements : Subst := {}
  for h in hypTys do
    if let some (_, l, r) := h.eq? then
      if l.isFVar && !r.containsFVar l.fvarId! && (← isCtorApp r) then
        replacements := replacements.insert l.fvarId! r
      else if r.isFVar && !l.containsFVar r.fvarId! && (← isCtorApp l) then
        replacements := replacements.insert r.fvarId! l
  -- A result may pass through several constructors (`r = ok d`, `d = Map xs`).
  -- This bounded closure is only for matching facts, never for rebinding a
  -- machine state. Self-referential equations were excluded above.
  let matchHyps ← hypTys.mapM fun h => Chc.normalizeFact (Chc.applyFix replacements h 4)
  let terms := Chc.appSubterms c (matchHyps.foldl (fun acc h => Chc.appSubterms h acc) #[])
  let insts ← if facts.isEmpty then pure #[] else
    Chc.factInstances facts terms (matchHyps ++ hypTys) allPremiseMatches
  let insts := insts.filter fun i => (collectFVars {} i).fvarIds.all fun f => rel.contains f
  let body := insts.foldr (fun i acc => mkForall `hf .default i acc) c
  return (binders, insts, ← mkForallFVars binders body)

/-- A verification condition restricted to what it needs (`sliceVCParts`). -/
private structure PreparedSlice where
  /-- The positions of the binders kept, among the condition's. -/
  binders : Array Nat
  /-- Instance types abstracted over the original condition's binders. -/
  instances : Array Expr
  /-- The restricted condition. -/
  type : Expr
  deriving Inhabited

/-- Prepare each slice once. Apart from avoiding repeated fact search, this
preserves the exact premise ordering of the condition the solver checked. -/
private def prepareSlice (xs : Array Expr) (c : Expr) (facts : Array Expr) : MetaM PreparedSlice := do
  let (binders, instances, type) ← sliceVCParts xs c facts
  return {
    binders := xs.zipIdx.filterMap fun (x, i) => if binders.contains x then some i else none
    instances := instances.map (·.abstract xs)
    type }

/-- A failed conjunction can be split under the same checked fact instances.
Its conclusions were already included in the group's fact search. -/
private def prepareConjunct (xs : Array Expr) (group : PreparedSlice) (c : Expr) : MetaM PreparedSlice := do
  let instances := group.instances.map (·.instantiateRev xs)
  let body := instances.foldr (fun i acc => mkForall `hf .default i acc) c
  let type ← mkForallFVars (group.binders.map (xs[·]!)) body
  return {group with type}

/-- First-order matching of a pattern with metavariables against a term, without
reduction: assigns the pattern's metavariables (an instance at a constructor,
`match x :: xs with …`, is matched before either side reduces). -/
private partial def foMatch (p t : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  if let .mvar id := p then
    unless ← id.isAssigned do
      unless ← isDefEq (← inferType p) (← inferType t) do return false
      id.assign t
      return true
  match p, t with
  | .app f a, .app g b => return (← foMatch f g) && (← foMatch a b)
  | .forallE _ d b _, .forallE _ d' b' _ =>
    if b.hasLooseBVars || b'.hasLooseBVars then return p == t
    return (← foMatch d d') && (← foMatch b b')
  | .mdata _ x, _ => foMatch x t
  | _, .mdata _ y => foMatch p y
  | _, _ => return p == t

/-- A proof of a fact instance (`sliceVC`'s premises): the fact at the values
matching its conclusion, its premises kept as the instance's own. -/
private def instanceProofUncached (facts : Array Expr) (inst : Expr) : MetaM Expr := do
  -- facts whose conclusion has the instance's head first (a unification
  -- attempt against an unrelated fact can unfold deep definitions); the
  -- others only if none of those applies
  let key := fun (ty : Expr) => forallTelescopeReducing ty fun _ b => pure (Chc.premiseKey b)
  let instKey ← key inst
  let wild := fun (k : Name) => k == .anonymous || k == `other
  let mut near := #[]
  let mut far := #[]
  for f in facts do
    let k ← key (← inferType f)
    if wild k || wild instKey || k == instKey then near := near.push f else far := far.push f
  for structural in #[true, false] do
    for f in near ++ far do
      let r? ← withNewMCtxDepth do
        let (ms, _, body) ← forallMetaTelescopeReducing (← inferType f)
        let props ← ms.filterM fun m => do isProp (← inferType m)
        let mut cand := body
        for m in props.reverse do cand := mkForall `h .default (← inferType m) cand
        -- first-order first: an instance at a constructor must not be reduced
        -- before it is matched; unification otherwise
        if structural then
          unless ← foMatch cand inst do return none
        unless ← isDefEq cand inst do return none
        -- the premises stay open: abstracted as the instance's own hypotheses
        let mut p := (← instantiateMVars (mkAppN f ms)).abstract props
        for m in props.reverse do
          p := mkLambda `h .default (← instantiateMVars (← inferType m)) p
        if p.hasMVar then return none
        return some p
      if let some p := r? then return p
  throwError "no fact proves the instance {← ppExpr inst}"

/-- Proofs of fact instances, by instance type abstracted over its locals (with their types). -/
private abbrev InstanceCache := IO.Ref (Std.HashMap (Expr × Array Expr) Expr)

/-- Equal fact instances in different conditions differ only in their local
variable names. Reuse the abstracted proof when those variables have closed
types. The cache belongs to one case and its fixed fact library. -/
private def instanceProof (facts : Array Expr) (inst : Expr)
    (cache? : Option InstanceCache := none) : MetaM Expr := do
  let some cache := cache? | instanceProofUncached facts inst
  let vars := Chc.fvarsInOrder inst
  let types ← vars.mapM inferType
  if types.any (fun t => t.hasFVar || t.hasMVar) then return ← instanceProofUncached facts inst
  let key := (inst.abstract vars, types)
  if let some proof := (← cache.get)[key]? then return proof.instantiateRev vars
  let proof ← instanceProofUncached facts inst
  let abstracted := proof.abstract vars
  unless abstracted.hasFVar || abstracted.hasMVar || abstracted.hasSorry do
    cache.modify (·.insert key abstracted)
  return proof

/-- Simplify a failed condition before extending its facts. Return the new
condition and a closed proof of `newCondition → originalCondition`. The bridge
retains equality substitution and reconstructs every added theorem instance. -/
private def prepareEnriched (target : Expr) (facts : Array Expr)
    (cache? : Option InstanceCache := none) : TermElabM (Expr × Expr) :=
  withLCtx {} {} do
    let conditionType ← mkFreshExprMVar (mkSort levelZero)
    withLocalDeclD `condition conditionType fun condition => do
      let original ← mkFreshExprMVar target
      let goals ← Tactic.run original.mvarId! <| Term.withoutErrToSorry do
        evalTactic (← `(tactic| intros; subst_vars))
        withMainContext do
          let goal ← getMainGoal
          let outer := (← getLCtx).foldl (init := #[]) fun acc d =>
            if d.isImplementationDetail || d.fvarId == condition.fvarId! then acc else acc.push d.toExpr
          let closed ← mkForallFVars outer (← goal.getType)
          let discovery ← Induction.Source.discover closed.getUsedConstants
          -- Root checks can be hidden behind Boolean wrappers. Expose these
          -- before matching list-selection facts, keeping recursion folded.
          let closed ← Induction.Source.expose discovery closed true
          let proof ← forallTelescope closed fun xs body => do
            let (binders, instances, type) ← sliceVCParts xs body facts true
            conditionType.mvarId!.assign type
            let instanceProofs ← instances.mapM fun i => do instanceProof facts i cache?
            mkLambdaFVars xs (mkAppN condition (binders ++ instanceProofs))
          goal.assign (mkAppN proof outer)
          setGoals []
      unless goals.isEmpty do throwError "explore: open enriched condition goals"
      let type ← instantiateMVars conditionType
      let proof ← instantiateMVars original
      let bridge ← mkLambdaFVars #[condition] proof
      if bridge.hasMVar || bridge.hasFVar || bridge.hasSorry then
        throwError "explore: incomplete enriched condition bridge"
      return (type, bridge)

/-- What became of a condition in the work stream of `proveCase`. -/
private inductive Outcome where
  /-- Proved by the brief probe. -/
  | probed (proof : Expr)
  /-- Not settled by the probe: extended with fact instances (`type`, with
  `bridge : type → condition`), then proved or not. -/
  | extended (type bridge : Expr) (proof? : Option Expr)

/-- Work on items while a producer is still supplying them: up to `jobs`
threads take the items in order, each item from the elaboration state when the
stream started (as `proveParallel` gives each target), the threads' names kept
apart. The producer `push`es, then `finish` waits for the work and returns
each item with its result, in push order (or rethrows the first failure);
`abandon` drops the items not taken yet and waits for the rest. -/
private structure WorkStream (α : Type) where
  /-- The items supplied so far, and how many are taken. -/
  queue : IO.Ref (Array Expr × Nat)
  /-- Whether the producer is done. -/
  closed : IO.Ref Bool
  /-- The threads: each returns the items it took, with their results. -/
  tasks : Array (Task (Except Exception (Array (Nat × Except Exception α))))

/-- Start `jobs` threads applying `work` to the items to come. -/
private def WorkStream.start (jobs : Nat) (work : Expr → TermElabM α) :
    TermElabM (WorkStream α) := do
  let queue ← IO.mkRef ((#[] : Array Expr), 0)
  let closed ← IO.mkRef false
  let termCtx ← read
  let termSt ← get
  let metaCtx ← readThe Meta.Context
  let metaSt ← getThe Meta.State
  let cancelTk? := (← readThe Core.Context).cancelTk?
  let mut tasks := #[]
  for _ in [0:max 1 jobs] do
    let (child, parent) := (← getNGen).mkChild
    setNGen parent
    let worker : CoreM (Array (Nat × Except Exception α)) := do
      setNGen child
      let initial ← get
      let mut out := #[]
      repeat
        -- (all pushes precede the close: an empty queue after a close is final)
        let wasClosed ← closed.get
        let item? ← queue.modifyGet fun (items, n) =>
          if h : n < items.size then (some (n, items[n]), (items, n + 1)) else (none, (items, n))
        match item? with
        | some (i, e) =>
          set {initial with ngen := ← getNGen}
          let r ← try pure (Except.ok (← ((work e).run' termCtx termSt).run' metaCtx metaSt))
            catch ex => pure (Except.error ex)
          out := out.push (i, r)
        | none =>
          if wasClosed then break
          IO.sleep 2
      return out
    let act ← Core.wrapAsync (fun (_ : Unit) => worker) cancelTk?
    tasks := tasks.push (← EIO.asTask (act ()) (prio := .dedicated))
  return {queue, closed, tasks}

/-- Supply an item. -/
private def WorkStream.push (s : WorkStream α) (e : Expr) : IO Unit :=
  s.queue.modify fun (items, n) => (items.push e, n)

/-- Close the stream and wait: each item with its result, in push order. -/
private def WorkStream.finish (s : WorkStream α) : TermElabM (Array (Expr × α)) := do
  s.closed.set true
  let items := (← s.queue.get).1
  let size := items.size
  let mut results : Array (Option (Except Exception α)) := Array.replicate size none
  let mut failure : Option Exception := none
  for task in s.tasks do
    match ← IO.wait task with
    | .ok rs => for (i, r) in rs do results := results.set! i (some r)
    | .error e => if failure.isNone then failure := some e
  if let some e := failure then throw e
  (items.zip results).mapM fun
    | (item, some (.ok a)) => pure (item, a)
    | (_, some (.error e)) => throw e
    | (_, none) => throwError "explore: an item of a work stream was not processed"

/-- Drop the items not taken yet, and wait for the threads. -/
private def WorkStream.abandon (s : WorkStream α) : IO Unit := do
  s.queue.modify fun (items, n) => (items.extract 0 n, n)
  s.closed.set true
  for task in s.tasks do discard <| IO.wait task

/-- A proof of a conjunction from proofs of its conjuncts (`conjunctsOf`'s leaves). -/
private partial def conjProof (leaf : Expr → MetaM Expr) (c : Expr) : MetaM Expr := do
  if c.isAppOfArity ``And 2 then
    return mkApp4 (mkConst ``And.intro) c.appFn!.appArg! c.appArg!
      (← conjProof leaf c.appFn!.appArg!) (← conjProof leaf c.appArg!)
  if c.isConstOf ``True then return mkConst ``True.intro
  leaf c

/-- Expand finite records with Lean's eliminator, preserving the original goal. -/
private partial def expandRecords (g : MVarId) (todo : List (FVarId × Nat)) : MetaM MVarId := do
  match todo with
  | [] => return g
  | (id, depth) :: rest => g.withContext do
    let some d := (← getLCtx).find? id | expandRecords g rest
    if depth == 0 || d.isImplementationDetail || (← isProp d.type) then return ← expandRecords g rest
    let ty ← whnf d.type
    let some info ← inductiveType? ty | expandRecords g rest
    if [``String, ``Char, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Fin, ``BitVec,
        ``Float].contains info.name || info.ctors.length != 1 || info.isRec || info.numIndices != 0 then
      return ← expandRecords g rest
    let subs ← g.cases id
    unless subs.size == 1 do throwError "explore: record expansion produced several goals"
    let some s := subs[0]? | throwError "explore: record expansion produced no goal"
    let rest := rest.filterMap fun (id, depth) => (s.subst.get id).fvarId?.map (·, depth)
    expandRecords s.mvarId (s.fields.toList.filterMap (fun f => f.fvarId?.map (·, depth - 1)) ++ rest)

/-- The machine run `h` states, if it is about one: its observed form (an
application of a predicate of `Induction.Observed` to a code value) and the
observation. -/
private def observedMachine? (h : Expr) : TermElabM (Option (Expr × Induction.Observed.Result)) := do
  let ty ← inferType h
  let discovery ← Induction.Source.discover ty.getUsedConstants
  if discovery.recursive.isEmpty then
    return none
  let exposed ← Induction.Source.expose discovery ty
  let observed ← Induction.Observed.discover #[exposed] discovery.recursive
  if observed.equations.isEmpty then
    return none
  let expression := Induction.Observed.replace observed.entries exposed
  unless observed.equations.any (fun e => expression.getAppFn.isConstOf e.name) do
    return none
  -- only interpreters: a machine running a code value
  if (← detectCodeType expression.appFn!).isNone then
    return none
  return some (expression, observed)

/-- The observer patterns whose domain is the type of a value a cut point or a
root holds (or of a field of one, three levels deep). -/
private def usefulPatterns (plan : Plan) (roots : Array Expr)
    (patterns : Array Expr) : MetaM (Array Expr) := do
  let mut work : Array (Expr × Nat) := #[]
  for c in plan.cuts do
    for v in c.vars do work := work.push (← inferType v, 3)
  for x in roots do work := work.push (← inferType x, 3)
  let mut types : Array Expr := #[]
  while !work.isEmpty do
    let (ty0, depth) := work.back!
    work := work.pop
    let ty ← instantiateMVars ty0
    if types.contains ty then continue
    types := types.push ty
    if depth == 0 then continue
    let tyW ← whnf ty
    let .const n _ := tyW.getAppFn | continue
    let some info := getStructureInfo? (← getEnv) n | continue
    let some ind ← inductiveType? tyW | continue
    if ind.isRec then continue
    let fields ← withLocalDeclD `s ty fun s => info.fieldNames.filterMapM fun f => do
      try pure (some (← inferType (← mkProjection s f))) catch _ => pure none
    for field in fields do
      unless field.hasLooseBVars || field.hasFVar do work := work.push (field, depth - 1)
  patterns.filterM fun p => do
    let .lam _ dom _ _ := p | return true
    types.anyM (isDefEq dom ·)

/-- The registered library facts about the definitions `expressions` reach. -/
private def libraryFacts (expressions : Array Expr) : TermElabM (Array Expr) := do
  let names := expressions.flatMap Expr.getUsedConstants
  let discovery ← Induction.Source.discover names
  Library.relevant (names ++ discovery.recursive ++ discovery.wrappers ++ discovery.predicates)

/-- The structure of a replay, for an exported proof (`Export.Replay`): its
statements as definitions over the context and the fuel, their conjunction
`all`, the proof of each statement from the induction hypothesis, and the
replay itself (named `base`), which proves what the case theorem `checked`
states. Runs in the replay's local context. -/
private def exportReplay (parts : Parts) (context : Array Expr) (target : Expr) (base checked : Name) :
    MetaM Export.Replay := do
  let nat := mkConst ``Nat
  let n0 := parts.n0
  let statements := (Array.range parts.statements.size).map fun i => base ++ .mkSimple s!"statement_{i + 1}"
  let proofs := (Array.range parts.proofs.size).map fun i => base ++ .mkSimple s!"proof_{i + 1}"
  let all := base ++ `all
  let at_ (c : Name) (n : Expr) : Expr := mkAppN (mkConst c) (context.push n)
  let predicate ← mkForallFVars context (← mkArrow nat (mkSort .zero))
  let mut decls : Array Export.Decl := #[]
  for (s, name) in parts.statements.zip statements do
    let value ← mkLambdaFVars (context.push n0) (← instantiateMVars s)
    decls := decls.push {name, isDef := true, type := predicate, value, group := .statements}
  let value ← mkLambdaFVars (context.push n0) (heapConj (statements.map (at_ · n0)))
  decls := decls.push {name := all, isDef := true, type := predicate, value, group := .statements}
  -- the induction hypothesis at fuel `n`, stated with `all`
  let hypothesis (n : Expr) : MetaM Expr := withLocalDeclD `m nat fun m => do
    mkForallFVars #[m] (← mkArrow (← mkAppM ``LT.lt #[m, n]) (at_ all m))
  let ih ← hypothesis n0
  for ((p, name), statement) in (parts.proofs.zip proofs).zip statements do
    let body := (← instantiateMVars p).abstract #[parts.ih]
    let type ← mkForallFVars (context.push n0) (.forallE `ih ih (at_ statement n0) .default)
    let value ← mkLambdaFVars (context.push n0) (.lam `ih ih body .default)
    decls := decls.push {name, type, value, group := .proofs}
  let step ← withLocalDeclD `n nat fun n => do
    withLocalDeclD `ih (← hypothesis n) fun ih => do
      mkLambdaFVars #[n, ih] (heapIntro (statements.map (at_ · n))
        (proofs.map fun p => mkAppN (mkConst p) (context ++ #[n, ih])))
  let induction := mkApp3 (mkConst ``Nat.strongRecOn [levelZero]) (mkAppN (mkConst all) context)
    parts.fuel step
  let rootArgs ← parts.rootArgs.mapM instantiateMVars
  let value ← mkLambdaFVars context (mkAppN (heapProj parts.root induction) rootArgs)
  decls := decls.push {name := base, type := ← mkForallFVars context target, value, group := .result}
  return {replaces := checked, decls, result := base}

/-- Prove the theorem case `g` (`label` names it in the progress reports). -/
private def proveCase (g : MVarId) (label : String) (succName : Name) (supplied : Array Expr)
    (proveFact proveLink probeVC proveVC : FactProver) (exportBase? : Option Name) :
    TermElabM (Option Export.Replay) := g.withContext do
  let start ← IO.monoMsNow
  let report (s : String) : CoreM Unit := progress start s label
  let jobs ← jobCount
  let target ← instantiateMVars (← g.getType)
  let lctx ← getLCtx
  let some succDecl := lctx.findFromUserName? succName | throwError "explore: lost machine premise"
  let hSucc := succDecl.toExpr
  let some (observed, equations) ← observedMachine? hSucc | throwError "explore: unsupported machine premise"
  let mut roots := #[]
  let mut hyps := #[]
  for d in lctx do
    if d.isImplementationDetail || d.fvarId == succDecl.fvarId then continue
    if ← isProp d.type then hyps := hyps.push d.toExpr else roots := roots.push d.toExpr
  let hypTypes ← hyps.mapM fun h => inferType h
  let library := supplied ++ (← libraryFacts (hypTypes ++ #[target, succDecl.type]))
  let hypConj := hypTypes.foldr (fun h acc => if acc.isConstOf ``True then h else mkAnd h acc) (mkConst ``True)
  withLocalDeclD `fuel (mkConst ``Nat) fun fuel => do
    let machine ← Machine.ofEquations (equations.equations.map fun e => (e.name, e.body, some e.proof)) fuel
    let initial := observed.appFn!
    let machine := {machine with codeType? := ← detectCodeType initial}
    let result ← Explore.run machine initial
    report s!"explored: {result.summary}"
    let isRoot := fun id => result.core.vars[id]?.any (fun v => match v.origin with | .root => true | _ => false)
    let carried ← roots.filterM fun x => do Chc.isCarriedType (← inferType x)
    let ((plan, patterns, anchors), core) ← machine.withOpaque do
      (do
        let anchors ← inCtx do
          return (← Chc.anyElementObservers (← Chc.unfoldProps #[hypConj]) isRoot).map (·.domain)
        let plan ← mkPlan result target (roots ++ hyps) (fun _ => pure (mkConst ``True)) (anchorTypes := anchors)
        let patterns ← Chc.observerPatterns hypConj target isRoot library
        let patterns ← inCtx (usefulPatterns plan roots patterns)
        return (plan, patterns, anchors) : ExM _).run result.core
    report s!"plan cuts={plan.cuts.size}; observer patterns={patterns.size}"
    -- (observer facts mostly wait for their solvers: two provers per job;
    -- more would starve them, and a fact that misses its time is lost)
    let facts ← withLCtx core.lctx {} <| Induction.ObserverFacts.discover (2 * jobs) patterns proveFact
    let candidates ← withLCtx core.lctx {} <| Chc.allCandidates hypConj target isRoot
    let mut facts := facts
    let mut links := #[]
    let mut pending := candidates
    for _ in [0:2] do
      if pending.isEmpty then break
      let before := links.size
      let proofs ← Induction.ObserverFacts.proveParallel (2 * jobs) proveLink links pending
      let mut failed := #[]
      for (candidate, proof?) in pending.zip proofs do
        match proof? with
        | some proof =>
          if proof.hasFVar || proof.hasMVar || proof.hasSorry then throwError "explore: incomplete observer fact"
          let name := (← getEnv).asyncPrefix?.getD (← getEnv).mainModule ++ `exploreLink ++ (← mkFreshId)
          addDecl (.thmDecl {name, levelParams := [], type := candidate, value := proof})
          links := links.push (mkConst name)
          facts := facts.push (mkConst name)
        | none => failed := failed.push candidate
      pending := failed
      if links.size == before then break
    let allFacts := library ++ facts
    report s!"proved {facts.size - links.size} observer facts and {links.size} links; inferring invariants"
    let (proposal, core) ← machine.withOpaque do
      (Chc.propose plan hypConj target isRoot carried
        (timeoutMs := blaster.explore.timeoutMs.get (← getOptions)) (facts := allFacts)).run core
    -- Each obligation is sliced and proved as soon as the replay states it,
    -- while the replay and the check of its reconstruction go on. Most paths
    -- share one large context and have several simple conclusions: a
    -- condition is translated with that context once, and only conditions the
    -- prover cannot settle together are split below; each proof is checked.
    -- Missing contracts cannot be recovered by spending a long solver budget
    -- on the same premises: a brief probe first, and for a condition it
    -- cannot settle, the full attempt with its facts extended (substituting
    -- before matching avoids thousands of duplicate instances at intermediate
    -- constructor names).
    let instanceCache : InstanceCache ← IO.mkRef {}
    let claimed ← IO.mkRef ({} : Std.HashSet Expr)
    let extend (condition : Expr) : TermElabM Outcome := do
      let (type, bridge) ← prepareEnriched condition allFacts (some instanceCache)
      return .extended type bridge (← try proveVC allFacts type catch _ => pure none)
    let probes ← WorkStream.start (2 * jobs) fun vc => do
      let slice ← forallTelescope vc fun xs body => prepareSlice xs body allFacts
      unless ← claimed.modifyGet fun s => (!s.contains slice.type, s.insert slice.type) do
        return (slice, none)
      if let some proof ← (try probeVC allFacts slice.type catch _ => pure none) then
        return (slice, some (.probed proof))
      return (slice, some (← extend slice.type))
    let (obligations, context, holes, reconstruction, sliced, exported?) ← try
        let (replayed, proofCore) ← machine.withOpaque do
          (do
            let checkedPlan ← mkPlan result target (roots ++ hyps)
              (fun t => pure proposal.invs[plan.cutOf[t]!]!)
              (fun e => pure (proposal.posts.getD e (mkConst ``True)))
              (fun e => pure (proposal.ghostVars.getD e #[], proposal.ghostVals.getD e #[]))
              (anchorTypes := anchors) (graph? := plan.graph)
            let hobs ← inCtx (mkExpectedTypeHint hSucc observed)
            provePlan checkedPlan hobs observed.appArg! fun vc => do
              let hole ← mkFreshExprMVar vc
              probes.push vc
              return hole : ExM _).run core
        let obligations := replayed.conditions.map fun (vc, hole) => (vc, hole.mvarId!)
        report s!"replayed {replayed.statements} statements: {obligations.size} obligations"
        -- Closed obligation proofs cannot repair a scope error in the
        -- surrounding replay term: it is checked before they are proved.
        let partialProof := replayed.proof
        let escaped := replayed.freeVars.filter (!lctx.contains ·)
        unless escaped.isEmpty do
          let details ← withLCtx proofCore.lctx {} do
            escaped.toList.take 16 |>.mapM fun id => do
              let type ← try pure (toString (← ppExpr (← inferType (.fvar id)))) catch _ => pure "unknown"
              let user := (proofCore.lctx.find? id).map (·.userName) |>.getD id.name
              return s!"{id.name} ({user}) : {type.take 250}"
          throwError "explore: replay leaves {escaped.size} exploration variables free: {details}"
        let context := lctx.foldl (init := #[]) fun acc d =>
          if d.isImplementationDetail then acc else acc.push d.toExpr
        let holes := obligations.map fun (_, hole) => mkMVar hole
        -- Check the reconstruction as an implication from its closed
        -- obligations. These binders are ordinary hypotheses, not admitted
        -- obligations. The public proof can use this theorem only after
        -- supplying every proof.
        let reconstructionType ← mkForallFVars (context ++ holes) target
        let reconstructionValue ← mkLambdaFVars (context ++ holes) partialProof
        if reconstructionValue.hasMVar || reconstructionValue.hasFVar || replayed.hasSorry then
          throwError "explore: incomplete reconstruction theorem"
        let reconstruction := (← getEnv).asyncPrefix?.getD (← getEnv).mainModule ++
          `exploreReplay ++ (← mkFreshId)
        withOptions (Elab.async.set · false) do
          addDecl (.thmDecl {name := reconstruction, levelParams := [], type := reconstructionType, value := reconstructionValue})
        report s!"checked replay reconstruction for {obligations.size} obligations; proving their conditions"
        -- (the replay's parts and local context are kept only for an export)
        let exported? := if exportBase?.isSome then replayed.parts?.map (·, proofCore.lctx) else none
        pure (obligations, context, holes, reconstruction, ← probes.finish, exported?)
      catch ex =>
        probes.abandon
        throw ex
    let mut grouped : Array Expr := #[]
    let mut prepared : Std.HashMap Expr PreparedSlice := {}
    let mut seen : Std.HashSet Expr := {}
    -- (the replays state their conditions concurrently: matched by statement)
    let sliceOf : Std.HashMap Expr PreparedSlice := sliced.foldl (init := {}) fun m (vc, (slice, _)) =>
      m.insert vc slice
    for (vc, _) in obligations do
      let some slice := sliceOf[vc]? | throwError "explore: a condition was not sliced"
      prepared := prepared.insert vc slice
      unless seen.contains slice.type do
        seen := seen.insert slice.type
        grouped := grouped.push slice.type
    let outcomes : Std.HashMap Expr Outcome := sliced.foldl (init := {}) fun m (_, (slice, outcome?)) =>
      match outcome? with
      | some outcome => m.insert slice.type outcome
      | none => m
    let mut checked : Std.HashMap Expr Expr := {}
    let publish (vc pr : Expr) : TermElabM Expr := do
      if pr.hasFVar || pr.hasMVar || pr.hasSorry then throwError "explore: incomplete condition proof"
      let (vc, pr) := ShareCommon.shareCommon' (vc, pr)
      let name := (← getEnv).asyncPrefix?.getD (← getEnv).mainModule ++ `exploreVC ++ (← mkFreshId)
      addDecl (.thmDecl {name, levelParams := [], type := vc, value := pr})
      return mkConst name
    -- an outcome that mentions a constant the environment lacks (declared in
    -- the thread that computed it: a lemma Lean derives on demand, say) is
    -- redone here
    let mut extended := 0
    for t in grouped do
      let env ← getEnv
      let known (pr : Expr) : Bool := pr.getUsedConstants.all env.contains
      let mut outcome? := outcomes[t]?
      match outcome? with
      | some (.probed pr) =>
        unless known pr do
          match ← probeVC allFacts t with
          | some pr => outcome? := some (.probed pr)
          | none => outcome? := some (← extend t)
      | some (.extended type bridge proof?) =>
        -- (the extension itself can declare lemmas: the source equations it exposes)
        unless known type && known bridge && proof?.all known do
          outcome? := some (← extend t)
      | none => pure ()
      match outcome? with
      | some (.probed pr) => checked := checked.insert t (← publish t pr)
      | some (.extended type bridge proof?) =>
        extended := extended + 1
        if let some pr := proof? then
          let proof ← publish type pr
          checked := checked.insert t (← publish t (mkApp bridge proof))
      | none => pure ()
    report s!"proved {checked.size}/{grouped.size} grouped conditions ({extended} with extended facts)"
    let mut unique : Array Expr := #[]
    let mut leaves : Std.HashMap Expr (Array (Expr × PreparedSlice)) := {}
    seen := {}
    for (vc, _) in obligations do
      if checked.contains prepared[vc]!.type then continue
      let slices ← forallTelescope vc fun xs body => do
        (conjunctsOf body).filterMapM fun conjunct => do
          if conjunct.isConstOf ``True then return none
          return some (conjunct.abstract xs, ← prepareConjunct xs prepared[vc]! conjunct)
      leaves := leaves.insert vc slices
      for (_, slice) in slices do
        unless seen.contains slice.type || checked.contains slice.type do
          seen := seen.insert slice.type
          unique := unique.push slice.type
    if !unique.isEmpty then
      report s!"proved {checked.size}/{grouped.size} grouped conditions; checking {unique.size} remaining conjuncts"
    let proofs ← Induction.ObserverFacts.proveParallel jobs proveVC allFacts unique
    let mut failed := #[]
    for (vc, pr?) in unique.zip proofs do
      match pr? with
      | none => failed := failed.push vc
      | some pr => checked := checked.insert vc (← publish vc pr)
    unless failed.isEmpty do
      let shown := failed.toList.take 3 |>.map fun vc => m!"{indentExpr vc}"
      throwError "explore: {failed.size} of {unique.size} verification conditions remain unproved, \
        for example:{MessageData.joinSep shown "\n"}"
    report "all conditions proved; assembling the case proof"
    for (vc, hole) in obligations do
      let proof ← withLCtx {} {} <| forallTelescope vc fun xs body => do
        let proveSlice (slice : PreparedSlice) : MetaM Expr := do
          let binders := slice.binders.map (xs[·]!)
          let some thm := checked[slice.type]? | throwError "explore: missing checked condition"
          let instanceProofs ← slice.instances.mapM fun inst =>
            instanceProof allFacts (inst.instantiateRev xs) (some instanceCache)
          return mkAppN thm (binders ++ instanceProofs)
        let group := prepared[vc]!
        let proof ← if checked.contains group.type then proveSlice group
          else conjProof (fun c => do
            let some (_, slice) := leaves[vc]!.find? (·.1 == c.abstract xs)
              | throwError "explore: missing prepared conjunct"
            proveSlice slice) body
        mkLambdaFVars xs proof
      hole.assign (← publish vc proof)
    let proof ← instantiateMVars (mkAppN (mkConst reconstruction) (context ++ holes))
    if proof.hasMVar || proof.hasSorry then throwError "explore: incomplete assembled proof"
    let bad := (collectFVars {} proof).fvarIds.filter (!lctx.contains ·)
    unless bad.isEmpty do throwError "explore: assembled proof mentions exploration variables"
    -- Publish a closed theorem before assigning the caller's goal.
    let type ← mkForallFVars context target
    let value ← mkLambdaFVars context proof
    let (type, value) := ShareCommon.shareCommon' (type, value)
    let name := (← getEnv).asyncPrefix?.getD (← getEnv).mainModule ++ `exploreChecked ++ (← mkFreshId)
    report "assembled all obligations; checking the case theorem"
    addDecl (.thmDecl {name, levelParams := [], type, value})
    g.assign (mkAppN (mkConst name) context)
    report "case proved"
    let some exportBase := exportBase? | return none
    let some (parts, replayLCtx) := exported? | throwError "explore: the replay has no parts to export"
    withLCtx replayLCtx {} (some <$> exportReplay parts context target exportBase name)

/-- Try the explorer only when a theorem contains an observed machine. Once
selected, every case must finish; no partial query can close the theorem.
`none` when the explorer does not apply; otherwise the structure of its
replays, for an exported proof (none unless `blaster.induction.export` is set). -/
def run? (facts : Array Expr) (proveFact proveLink probeVC proveVC : FactProver) :
    TacticM (Option (Array Export.Replay)) := do
  unless blaster.explore.enabled.get (← getOptions) do return none
  Chc.clearCaches
  let saved ← saveState
  let initial ← getMainGoal
  let target ← withTransparency .default (whnf (← initial.getType))
  replaceMainGoal [← initial.replaceTargetDefEq target]
  evalTactic (← `(tactic| intros))
  let g ← getMainGoal
  -- Expand records carrying several independent inputs. Scalar wrappers stay
  -- intact at the root, so the query's observers keep their original domains.
  let todo ← g.withContext do
    let mut todo := []
    for d in ← getLCtx do
      if d.isImplementationDetail || (← isProp d.type) then continue
      let some info ← inductiveType? (← whnf d.type) | continue
      unless info.ctors.length == 1 && !info.isRec do continue
      let ctor ← getConstInfoCtor info.ctors[0]!
      if ctor.numFields ≥ 2 then todo := todo ++ [(d.fvarId, 8)]
    return todo
  let g ← expandRecords g todo
  setGoals [g]
  let premise? ← g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail || !(← isProp d.type) then continue
      if (← observedMachine? d.toExpr).isSome then return some d.fvarId
    return none
  let some premise := premise? | saved.restore; return none
  for fact in facts do
    unless !fact.hasMVar && !fact.hasSorry && (← isProp (← inferType fact)) do
      throwError "explore: supplied facts must be complete proofs"
  let succName ← g.withContext (mkFreshUserName `machineSuccess)
  let g ← g.rename premise succName
  setGoals [g]
  Success.decompose #[succName]
  -- (a query variable of a finite sum type stays one variable: exploration
  -- splits it where the machine inspects it, and the solver reasons by cases)
  let cases := (← getGoals).toArray
  let proveFact ← memoizeProver proveFact
  let proveLink ← memoizeProver proveLink
  let probeVC ← memoizeProver probeVC
  let proveVC ← memoizeProver proveVC
  -- (the goals the decomposition of the machine's success leaves: usually one)
  progress (← IO.monoMsNow) s!"proving {cases.size} {if cases.size == 1 then "goal" else "goals"}"
  -- (an exported proof names each replay after the declaration being proved)
  let exportBase? ← if (← Export.target?).isSome then Term.getDeclName? else pure none
  let mut replays := #[]
  for (g, i) in cases.zipIdx do
    let replayName? := exportBase?.map fun base =>
      base ++ if cases.size == 1 then `replay else .mkSimple s!"replay_{i + 1}"
    if let some replay ← proveCase g (caseLabel i cases.size) succName facts proveFact proveLink
        probeVC proveVC replayName? then
      replays := replays.push replay
  setGoals []
  return some replays
where
  caseLabel (i n : Nat) : String := if n == 1 then "" else s!"goal {i + 1}/{n} "

end Blaster.Proof.Explore.Frontend
