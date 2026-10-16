import Blaster.Proof.Explore.Stuck
import Blaster.Proof.Explore.Unify

/-!
# Symbolic exploration: search

Depth-first symbolic execution of a machine from an initial state. Every state
reached is registered under its structural key as a *template*. A state that
matches an ancestor's key but is not an instance widens the ancestor (loop
head) and restarts it; a state matching another explored template either joins
it (instance) or generalizes it into a new version. States whose code repeats
with a strictly growing continuation designate a *procedure*: its body is
explored once with an abstract continuation `κ`, its exits are the states
whose step needs `κ`, and callers continue at the anti-unified exit shape.

Everything the search decides is recorded (templates, transition trees,
procedure summaries) so that a proof can replay it. The search itself proves
nothing and is never trusted.
-/
namespace Blaster.Proof.Explore
open Lean Meta

register_option blaster.explore.maxStates : Nat := {
  defValue := 400000
  descr := "Maximum number of machine steps taken by symbolic exploration" }

/-- Iterations of a loop over closed data (a computation on program
constants) that are executed rather than generalized. -/
def maxUnrolled : Nat := 64

/-- Stuck points resolved within one machine step: more is a recursive
computation on symbolic data inside the step, recorded as unreachable. -/
def maxStuckDepth : Nat := 512

/-- A decision fact on the current path. -/
structure Decision where
  prop : Expr
  positive : Bool
  hyp : Expr
deriving Inhabited, BEq

/-- What a path of the exploration knows. -/
structure Path where
  /-- The decisions taken on the path. -/
  decisions : Array Decision := #[]
  /-- Generalized subterms introduced on this path. -/
  defs : Array (Expr × Expr) := #[]
  /-- Known constructor values of generalized variables. -/
  splits : Array (Expr × Expr) := #[]
  /-- Stuck resolutions since the last machine step. -/
  depth : Nat := 0
deriving Inhabited

/-- A node of a transition tree: how the exploration got from a template's
state to its next states and leaves. -/
inductive Node where
  /-- Case split on a variable (all occurrences). -/
  | split (atom : Expr) (alts : Array (Name × Array Expr × Nat))
  /-- Generalize a subterm (all occurrences) as a canonical variable. -/
  | gen (expr : Expr) (var : Expr) (fresh : Bool) (next : Nat)
  /-- A generalized variable whose constructor is already known on this path. -/
  | known (var : Expr) (value : Expr) (next : Nat)
  /-- Case analysis of the decision `inst : Decidable prop`, with the
  hypotheses of either case. -/
  | cond (inst prop : Expr) (hTrue hFalse : Expr) (onTrue onFalse : Nat)
  /-- Rewrite with a checked equation `proof : lhs = rhs` (all occurrences). -/
  | rewrite (lhs rhs proof : Expr) (next : Nat)
  /-- A decision already taken on this path (hypothesis `hyp`). -/
  | knownCond (inst prop : Expr) (positive : Bool) (hyp : Expr) (next : Nat)
  /-- The machine accepts (the step reduced to `True`). -/
  | accept
  /-- The machine rejects (`False`). -/
  | reject
  /-- The step reduced to a proposition that is not a state. -/
  | leaf (prop : Expr)
  /-- Arrival at a template (resolved to its final version after the search). -/
  | goto (state : Expr) (key : UInt64)
  /-- Call of a procedure (entry template `entry`, exit shape `shape`); `ret`
  continues at the return state (the shape with the caller's continuation). -/
  | call (state : Expr) (proc : Nat) (entry : Nat) (shape : Option Expr) (ret : Option Nat)
  /-- A procedure exit: this state's step needs the continuation. -/
  | exit (state : Expr)
  /-- The exploration gave up here: the result proves nothing. -/
  | abort (why : String)
  /-- A point the program cannot reach under the path's facts: every proof
  must refute it (`facts → False`). Recorded where exploring on would be
  meaningless or unbounded (unknown program code, an unbounded chain of stuck
  resolutions within one step). -/
  | unreachable (why : String)
deriving Inhabited

/-- A template: a state whose non-root variables are pattern variables,
explored once for all its instances. -/
structure Tpl where
  /-- Its structural key (`stateKey`, in its context `ctxKey`). -/
  key : UInt64
  /-- The state. -/
  body : Expr
  /-- The decisions an instance must have taken to join it. -/
  decisions : Array Decision
  /-- The procedure whose body it is in. -/
  proc? : Option Nat
  /-- Entry template of the enclosing procedure region. -/
  entry? : Option Nat := none
  /-- The root of its transition tree, once explored. -/
  node? : Option Nat := none
  /-- Whether it is explored. -/
  done : Bool := false
  /-- Replaced by a more general version, or undone by a restart. -/
  abandoned : Bool := false
  /-- Consecutive concrete iterations of a loop this template unrolls. -/
  unrolled : Nat := 0
  /-- Use clock when the template was created. -/
  logStart : Nat := 0
  /-- Once explored: the decisions its transitions relied on. -/
  need : Array Decision := #[]
deriving Inhabited

/-- How far a procedure's body is explored. -/
inductive ProcStatus where
  | fresh | exploring | explored
deriving BEq, Inhabited

/-- A procedure: code that runs with a growing continuation, explored once
with the abstract continuation `kappa`. -/
structure Proc where
  /-- The key of its states without the continuation (`codeKeyOf`). -/
  codeKey : UInt64
  /-- The abstract continuation. -/
  kappa : Expr
  /-- The position of the continuation among the state's arguments. -/
  stackArg : Nat
  /-- Entry template body (the stack is `kappa`). -/
  body? : Option Expr := none
  /-- Its entry template. -/
  entry? : Option Nat := none
  /-- The states at which the body needs its continuation. -/
  exits : Array Expr := #[]
  /-- The anti-unification of the exits: where callers continue. -/
  shape? : Option Expr := none
  status : ProcStatus := .fresh
  /-- Incremented when the body is explored again (its templates are then new). -/
  version : Nat := 0
  /-- Call nodes waiting for an exit shape: node, caller stack. -/
  pending : Array (Nat × Expr) := #[]
  /-- Exit shape assumed by recursive calls during the current exploration. -/
  seed? : Option Expr := none
deriving Inhabited

/-- Why the exploration of a segment restarts at template `tpl`. -/
inductive Restart where
  /-- A loop: the template is replaced by the more general `body`. -/
  | widen (tpl : Nat) (body : Expr) (decisions : Array Decision)
  /-- Its state turned out to be the call of a procedure. -/
  | reArrive (tpl : Nat)
deriving Inhabited

/-- Thrown to unwind the search to the segment that explores the template a
restart concerns (`Search.pendingRestart` says which and how). -/
initialize restartExceptionId : InternalExceptionId ←
  registerInternalExceptionId `Blaster.Proof.Explore.restart

def Restart.tpl : Restart → Nat
  | .widen t .. => t
  | .reArrive t => t

/-- Where the exploration is: in which procedure, under which ancestors. -/
structure Ctx where
  /-- The procedure being explored, and its continuation. -/
  proc? : Option (Nat × Expr) := none
  procVersion : Nat := 0
  /-- The entry template of the region. -/
  entry? : Option Nat := none
  /-- The ancestor templates, by key: arriving at one again is a loop. -/
  ancs : PersistentHashMap UInt64 Nat := {}
  /-- The ancestors by code key, with the keys of their continuation's frames:
  the same code with a growing continuation is a procedure. -/
  ancCode : PersistentHashMap UInt64 (Array (Array UInt64 × UInt64 × Nat)) := {}
deriving Inhabited

/-- Counts of what the exploration did, for the progress reports. -/
structure Stats where
  states : Nat := 0
  templates : Nat := 0
  joins : Nat := 0
  loops : Nat := 0
  widenings : Nat := 0
  crossWidenings : Nat := 0
  restarts : Nat := 0
  splits : Nat := 0
  gens : Nat := 0
  conds : Nat := 0
  accepts : Nat := 0
  rejects : Nat := 0
  leaves : Nat := 0
  aborts : Nat := 0
  unreachables : Nat := 0
  calls : Nat := 0
  exits : Nat := 0
  growths : Nat := 0
deriving Inhabited

/-- The state of the search; what a proof replays. -/
structure Search where
  tpls : Array Tpl := #[]
  /-- The nodes of the transition trees. -/
  nodes : Array Node := #[]
  /-- The versions of the templates with each key, oldest first. -/
  byKey : Std.HashMap UInt64 (Array Nat) := {}
  /-- Templates by context and exact state (`exactKey`). -/
  exact : Std.HashMap (UInt64 × Expr) Nat := {}
  /-- The templates in order of creation (for undoing a restarted segment). -/
  created : Array Nat := #[]
  procs : Array Proc := #[]
  procByCode : Std.HashMap UInt64 Nat := {}
  /-- The continuation argument of each predicate (`stackArg?`), memoized. -/
  stackArgs : Std.HashMap Name (Option Nat) := {}
  pendingRestart : Option Restart := none
  /-- Clock of path-fact uses, and the last use of each decision hypothesis. -/
  useClock : Nat := 0
  lastUse : Std.HashMap FVarId Nat := {}
  /-- Machine steps left (`blaster.explore.maxStates`). -/
  budget : Nat
  stats : Stats := {}

abbrev SearchM := StateRefT Search ExM

def liftCore (k : ExM α) : SearchM α := liftM k

/-- Add a node; its index. -/
def addNode (n : Node) : SearchM Nat := do
  let id := (← get).nodes.size
  modify fun s => {s with nodes := s.nodes.push n}
  return id

def setNode (id : Nat) (n : Node) : SearchM Unit :=
  modify fun s => {s with nodes := s.nodes.set! id n}

def bump (f : Stats → Stats) : SearchM Unit :=
  modify fun s => {s with stats := f s.stats}

/-! ## Stacks and procedure keys -/

/-- Index of the continuation argument of a predicate: the first argument of
type `List τ` with `τ` a control type that the machine's steps change (an
argument every step passes on unchanged, a table of procedures say, is not a
continuation). -/
def stackArg? (s : Expr) : SearchM (Option Nat) := do
  let .const n _ := s.getAppFn | return none
  if let some r := (← get).stackArgs[n]? then return r
  let M := (← getThe Core).machine
  let args := s.getAppArgs
  let mut r := none
  for i in [0:args.size] do
    let ty ← liftCore <| inCtx do whnf (← inferType args[i]!)
    if ty.isAppOfArity ``List 1 && !ty.hasFVar then
      if (← liftCore (isControl ty.appArg!)) && !(← liftCore (inCtx (M.passesThrough n i))) then
        r := some i
        break
  modify fun st => {st with stackArgs := st.stackArgs.insert n r}
  return r

/-- The keys of the frames of a continuation (a list), outermost first, and of its tail. -/
partial def frameKeys (l : Expr) (acc : Array UInt64 := #[]) : ExM (Array UInt64 × UInt64) := do
  if l.isAppOfArity ``List.cons 3 then
    let h ← keyOf l.appFn!.appArg!
    frameKeys l.appArg! (acc.push h)
  else return (acc.reverse, ← keyOf l)

/-- Whether `a` is a proper prefix of `b`. -/
def isPrefixArr (a b : Array UInt64) : Bool :=
  a.size < b.size && (a.toList.zip (b.toList.take a.size)).all fun (x, y) => x == y

/-- Key of a state without its continuation argument. -/
def codeKeyOf (s : Expr) (stack : Nat) : ExM UInt64 := do
  let mask ← stateMask s
  let args := s.getAppArgs
  let mut h : UInt64 := hash s.getAppFn
  for i in [0:args.size] do
    if i != stack then h := mixHash h (← keyOf args[i]! (mask[i]?.getD false))
  return h

/-- The key `k` in context: inside a procedure (of a version), templates are its own. -/
def ctxKey (ctx : Ctx) (k : UInt64) : UInt64 :=
  match ctx.proc? with
  | some (pk, _) => mixHash (mixHash k (hash pk)) (hash ctx.procVersion)
  | none => k

/-! ## Facts -/

/-- The decisions of the path about variables of `body`. -/
def relevantDecisions (path : Path) (body : Expr) : Array Decision :=
  path.decisions.filter fun d =>
    (collectFVars {} d.prop).fvarIds.all fun v => body.containsFVar v

/-- The path decisions matching `tplFacts` under `subst` (their hypotheses),
or `none` if some fact does not hold on the path. -/
def matchFacts (tplFacts : Array Decision) (subst : Std.HashMap FVarId Expr) (path : Path) :
    Option (Array Expr) :=
  tplFacts.foldlM (init := #[]) fun acc d =>
    let p := d.prop.replace fun t => match t with
      | .fvar id => subst[id]?
      | _ => none
    (path.decisions.find? fun d' => d'.prop == p && d'.positive == d.positive).map fun d' =>
      acc.push d'.hyp

/-- Record that the path decisions with hypotheses `hs` were relied on. -/
def useHyps (hs : Array Expr) : SearchM Unit := do
  if hs.isEmpty then return
  modify fun s => Id.run do
    let c := s.useClock + 1
    let mut lu := s.lastUse
    for h in hs do
      if let .fvar id := h then lu := lu.insert id c
    return {s with useClock := c, lastUse := lu}

/-- The facts an arrival must establish to join `t`: once `t` is explored,
only those its transition tree relied on (a known decision, or a join that
needed it); before that, all of them. -/
def joinFacts (t : Tpl) : Array Decision :=
  if t.done then t.need else t.decisions

/-- Mark a template explored and record the decisions its subtree used. -/
def markDone (id : Nat) : SearchM Unit :=
  modify fun s => {s with tpls := s.tpls.modify id fun x =>
    if x.done then x else
    {x with done := true, need := x.decisions.filter fun d => match d.hyp with
      | .fvar h => s.lastUse.getD h 0 > x.logStart
      | _ => true}}

/-! ## Templates -/

/-- Create a template. -/
def newTpl (key : UInt64) (body : Expr) (decisions : Array Decision) (ctx : Ctx) : SearchM Nat := do
  let id := (← get).tpls.size
  modify fun s => {s with
    tpls := s.tpls.push {key, body, decisions, logStart := s.useClock, proc? := ctx.proc?.map (·.1), entry? := ctx.entry?}
    byKey := s.byKey.insert key ((s.byKey.getD key #[]).push id)
    created := s.created.push id}
  bump fun st => {st with templates := st.templates + 1}
  return id

/-- Retire a template: no state joins it any more. -/
def abandon (id : Nat) : SearchM Unit :=
  modify fun s =>
    let t := s.tpls[id]!
    {s with
      tpls := s.tpls.set! id {t with abandoned := true}
      byKey := s.byKey.insert t.key ((s.byKey.getD t.key #[]).filter (· != id))}

/-- A candidate element-wise producer in `e`: a constant from lists to lists
(other than `List.map`) applied to one argument, possibly under binders.
Returns the head constant (with its universe levels). -/
partial def producerHead? (e : Expr) : ExM (Option Expr) := do
  let nonProducers := (← get).nonProducers
  let found ← IO.mkRef (none : Option Expr)
  let cands ← IO.mkRef (#[] : Array Expr)
  e.forEach fun t => do
    if t.getAppNumArgs == 1 then
      if let .const n _ := t.getAppFn then
        if n != ``List.map && !nonProducers.contains n then
          cands.modify fun c => if c.contains t.getAppFn then c else c.push t.getAppFn
  for f in ← cands.get do
    if (← found.get).isSome then break
    let ok ← inCtx do
      let ty ← inferType f
      match ty with
      | .forallE _ d c _ =>
        -- list types spelled through abbreviations (`Withdrawals`) are lists
        if c.hasLooseBVars then pure false
        else pure ((← whnfR d).isAppOfArity ``List 1 && (← whnfR c).isAppOfArity ``List 1)
      | _ => pure false
    if ok then found.set (some f)
    else modify fun c => {c with nonProducers := c.nonProducers.insert f.constName!}
  found.get

/-- For a producer constant `f : List α → List β` certified element-wise:
`(List.map g, proof : f = List.map g)`. Cached per constant. -/
def producerMap? (f : Expr) : ExM (Option (Expr × Expr)) := do
  if let some r := (← get).producerMaps.get? f then return r
  let cache ← IO.mkRef (← get).mappings
  let r ← inCtx do
    let .forallE n d _ _ ← inferType f | return none
    withLocalDeclD n d fun xs => do
      let some (rhs, proof) ← Induction.MappedLists.asMap? (mkApp f xs) cache | return none
      unless rhs.isAppOfArity ``List.map 4 && rhs.appArg! == xs do return none
      let mapFn := rhs.appFn!
      if mapFn.containsFVar xs.fvarId! then return none
      let pointwise ← mkLambdaFVars #[xs] proof
      let eq ← mkFunExt pointwise
      return some (mapFn, eq)
  let updated ← cache.get
  modify fun c => {c with mappings := updated, producerMaps := c.producerMaps.insert f r}
  if r.isNone then modify fun c => {c with nonProducers := c.nonProducers.insert f.constName!}
  return r

/-- The eager producer rewrite of a state: `(f, List.map g, proof, s')`. -/
def eagerMap? (e : Expr) : ExM (Option (Expr × Expr × Expr × Expr)) := do
  for _ in [:8] do
    let some f ← producerHead? e | return none
    if let some (rhs, proof) ← producerMap? f then
      return some (f, rhs, proof, replaceConstTerm e f rhs)
  return none

/-- Abandon every template created after `stamp` (restart bookkeeping). -/
def undoTo (stamp : Nat) : SearchM Unit := do
  while (← get).created.size > stamp do
    let id := (← get).created.back!
    modify fun s => {s with created := s.created.pop}
    abandon id

/-- The key of the template of exactly the state `s` (in context). -/
def exactKey (ctx : Ctx) (s : Expr) : UInt64 × Expr := (ctxKey ctx 0, s)

/-- Do `tpl` and `s` differ only in closed subterms (no hole of the
generalization involves a variable)? -/
def closedDiff? (tpl s : Expr) : ExM Bool := do
  let vars ← patternVars tpl
  let (_, st) ← (lgg vars tpl s).run {multi := ← templateMulti vars tpl}
  return !st.holes.isEmpty && st.codeHoles == 0 &&
    st.holes.all fun (a, b, _) => !a.hasFVar && !b.hasFVar

/-- Does the generalization `body'` of `tpl` abstract the continuation (a new
pattern variable of the state's continuation type)? Only procedures abstract
continuations (by `κ`); a template parameter standing for one makes its
frames, and the program code they hold, unknown. -/
def abstractsStack (tpl body' : Expr) : SearchM Bool := do
  let some i ← stackArg? body' | return false
  let sty ← liftCore <| inCtx (inferType body'.getAppArgs[i]!)
  let old ← liftCore (patternVars tpl)
  for v in (← liftCore (patternVars body')).toList do
    if old.contains v then continue
    if ← liftCore <| inCtx (do isDefEq (← inferType (.fvar v)) sty) then return true
  return false

/-! ## The search -/

mutual

/-- Explore template `id` and every straight-line successor. -/
partial def exploreSeg (id0 : Nat) (path0 : Path) (ctx0 : Ctx) : SearchM Unit := do
  -- per segment position: template, creation stamp, context before entering it
  let mut segTpls : Array Nat := #[id0]
  let mut segStamps : Array Nat := #[(← get).created.size]
  let mut segCtxs : Array Ctx := #[ctx0]
  let mut ctx ← enter id0 ctx0
  let mut path := path0
  let mut id := id0
  repeat
    let r ← try
        pure (Sum.inl (← stepOnce id path ctx))
      catch ex =>
        let restart := match ex with
          | .internal id _ => id == restartExceptionId
          | _ => false
        let some rs := (← get).pendingRestart | throw ex
        if restart && segTpls.contains rs.tpl then pure (Sum.inr rs) else throw ex
    match r with
    | .inl none =>
      for t in segTpls do markDone t
      return
    | .inl (some (next, path')) =>
      segTpls := segTpls.push next
      segStamps := segStamps.push (← get).created.size
      segCtxs := segCtxs.push ctx
      ctx ← enter next ctx
      path := path'
      id := next
    | .inr rs =>
      modify fun s => {s with pendingRestart := none}
      bump fun st => {st with restarts := st.restarts + 1}
      let idx := segTpls.findIdx? (· == rs.tpl) |>.getD 0
      let old := (← get).tpls[rs.tpl]!
      undoTo segStamps[idx]!
      ctx := segCtxs[idx]!
      segTpls := segTpls.extract 0 idx
      segStamps := segStamps.extract 0 idx
      segCtxs := segCtxs.extract 0 idx
      match rs with
      | .widen _ body decisions =>
        abandon rs.tpl
        let nid ← newTpl old.key body decisions ctx
        segTpls := segTpls.push nid
        segStamps := segStamps.push (← get).created.size
        segCtxs := segCtxs.push ctx
        ctx ← enter nid ctx
        path := {path with decisions := decisions}
        id := nid
      | .reArrive _ =>
        -- the state is now a call of a designated procedure
        let (node, cont) ← handleCall old.body path ctx
        modify fun s => {s with tpls := s.tpls.modify rs.tpl fun t => {t with node? := some node}}
        markDone rs.tpl
        match cont with
        | none =>
          for t in segTpls do markDone t
          return
        | some (next, path') =>
          segTpls := segTpls.push next
          segStamps := segStamps.push (← get).created.size
          segCtxs := segCtxs.push ctx
          ctx ← enter next ctx
          path := path'
          id := next

/-- Register template `id` as an ancestor. -/
partial def enter (id : Nat) (ctx : Ctx) : SearchM Ctx := do
  let t := (← get).tpls[id]!
  let mut ctx := {ctx with ancs := ctx.ancs.insert t.key id}
  if let some i ← stackArg? t.body then
    let ck ← liftCore (codeKeyOf t.body i)
    let (fk, bk) ← liftCore (frameKeys t.body.getAppArgs[i]!)
    ctx := {ctx with ancCode := ctx.ancCode.insert ck ((ctx.ancCode.findD ck #[]).push (fk, bk, id))}
  return ctx

/-- One step from template `id`. Returns a straight-line successor template. -/
partial def stepOnce (id : Nat) (path : Path) (ctx : Ctx) : SearchM (Option (Nat × Path)) := do
  let s := (← get).tpls[id]!.body
  let path := {path with depth := 0}
  if (← get).budget == 0 then
    let n ← addNode (.abort "state budget")
    modify fun st => {st with tpls := st.tpls.modify id fun t => {t with node? := some n}}
    return none
  modify fun st => {st with budget := st.budget - 1}
  bump fun st => {st with states := st.states + 1}
  let M := (← getThe Core).machine
  let some r ← liftCore (inCtx (M.step s)) | do
    let n ← addNode (.abort "step budget")
    modify fun st => {st with tpls := st.tpls.modify id fun t => {t with node? := some n}}
    return none
  match r with
  | .next s' =>
    let (node, cont) ← arrive s' path ctx
    modify fun st => {st with tpls := st.tpls.modify id fun t => {t with node? := some node}}
    return cont
  | _ =>
    let node ← resolve r path ctx s
    modify fun st => {st with tpls := st.tpls.modify id fun t => {t with node? := some node}}
    return none

/-- Classify a newly reached state. Returns its node and, for a fresh
template, the template to explore next (in the same segment). -/
partial def arrive (s0 : Expr) (path : Path) (ctx : Ctx) : SearchM (Nat × Option (Nat × Path)) := do
  let s ← liftCore (normState s0)
  -- procedure calls and growth
  if let some i ← stackArg? s then
    let ck ← liftCore (codeKeyOf s i)
    if (← get).procByCode.contains ck then
      let (node, cont) ← handleCall s path ctx
      return (node, cont)
    if let some anc := ctx.ancCode.find? ck then
      let (fk, bk) ← liftCore (frameKeys s.getAppArgs[i]!)
      if let some (_, _, t0) := anc.find? (fun (fk0, bk0, _) => bk0 == bk && isPrefixArr fk0 fk) then
        if ← kappaParametric s i then
          let stTy ← liftCore <| inCtx (inferType s.getAppArgs[i]!)
          let kappa ← liftCore (mkVar `κ stTy .kappa false)
          let pid := (← get).procs.size
          modify fun st => {st with
            procs := st.procs.push {codeKey := ck, kappa, stackArg := i}
            procByCode := st.procByCode.insert ck pid
            pendingRestart := some (.reArrive t0)}
          bump fun st => {st with growths := st.growths + 1}
          throw (.internal restartExceptionId)
  let k := ctxKey ctx (← liftCore (stateKey s))
  -- loops: an ancestor with the same key
  if let some a := ctx.ancs.find? k then
    let t := (← get).tpls[a]!
    let inst ← liftCore (instanceOf? t.body s)
    if let some σ := inst then
      if let some hs := matchFacts t.decisions σ path then
        useHyps hs
        bump fun st => {st with loops := st.loops + 1}
        return (← addNode (.goto s k), none)
    -- a loop driven by closed data (a computation on program constants):
    -- execute it rather than abstract the constants, within a budget
    if t.unrolled < maxUnrolled then
      if ← liftCore (closedDiff? t.body s) then
        let id ← newTpl k s (relevantDecisions path s) ctx
        modify fun st => {st with
          tpls := st.tpls.modify id fun x => {x with unrolled := t.unrolled + 1}
          exact := st.exact.insert (exactKey ctx s) id}
        return (← addNode (.goto s k), some (id, path))
    let decided : Std.HashSet FVarId := path.decisions.foldl
      (fun acc d => (collectFVars {} d.prop).fvarIds.foldl (·.insert ·) acc) {}
    let widened? ← liftCore (antiUnifyData? t.body s (noReuse := decided))
    let widened? ← match widened? with
      | some (b, _) => do if ← abstractsStack t.body b then pure none else pure widened?
      | none => pure none
    -- a key collision between different program points is not a loop
    if let some (body', _) := widened? then
      let decisions := t.decisions.filter fun d =>
        path.decisions.contains d && (collectFVars {} d.prop).fvarIds.all body'.containsFVar
      bump fun st => {st with widenings := st.widenings + 1}
      modify fun st => {st with pendingRestart := some (.widen a body' decisions)}
      throw (.internal restartExceptionId)
  let xk := exactKey ctx s
  if let some t := (← get).exact[xk]? then
    let tpl := (← get).tpls[t]!
    if !tpl.abandoned then
      if let some hs := matchFacts (joinFacts tpl) {} path then
        useHyps hs
        bump fun st => {st with joins := st.joins + 1}
        return (← addNode (.goto s k), none)
  let versions := (← get).byKey.getD k #[]
  -- versions only grow more general: the newest one is the candidate. Versions
  -- holding a different constructor of some non-recursive type (a sibling
  -- branch of a case split) are kept apart: the newest compatible one is used.
  let mut target? : Option Nat := none
  for v in versions.reverse do
    -- a conflict on a recursive type (an empty against a non-empty list)
    -- keeps versions apart only while the key has few of them
    if !(← liftCore (ctorConflict (← get).tpls[v]!.body s (allowRec := versions.size < 2))) then
      target? := some v
      break
  for v in target?.toArray do
    let t := (← get).tpls[v]!
    if let some σ ← liftCore (instanceOf? t.body s) then
      if let some hs := matchFacts (joinFacts t) σ path then
        useHyps hs
        bump fun st => {st with joins := st.joins + 1}
        return (← addNode (.goto s k), none)
  let decisions := relevantDecisions path s
  let body ← match target? with
    | some v =>
      bump fun st => {st with crossWidenings := st.crossWidenings + 1}
      let decided : Std.HashSet FVarId := path.decisions.foldl
        (fun acc d => (collectFVars {} d.prop).fvarIds.foldl (·.insert ·) acc) {}
      let b? ← liftCore (antiUnifyData? (← get).tpls[v]!.body s (noReuse := decided))
      let b? ← match b? with
        | some (b, _) => do if ← abstractsStack (← get).tpls[v]!.body b then pure none else pure b?
        | none => pure none
      pure (b?.map (·.1) |>.getD s)
    | none => pure s
  let decisions := if body == s then decisions else
    decisions.filter fun d => (collectFVars {} d.prop).fvarIds.all body.containsFVar
  -- a new version generalizes its target: its facts too (only those the
  -- target also assumes), and its exploration continues under those facts
  let tpls := (← get).tpls
  let decisions := match target? with
    | some v => let tds := tpls[v]!.decisions; decisions.filter tds.contains
    | none => decisions
  let path := match target? with
    | some _ =>
      let dropped := (relevantDecisions path s).filter (!decisions.contains ·)
      {path with decisions := path.decisions.filter (!dropped.contains ·)}
    | none => path
  let id ← newTpl k body decisions ctx
  if body == s then modify fun st => {st with exact := st.exact.insert xk id}
  return (← addNode (.goto s k), some (id, path))

/-- Does the step of `s` avoid inspecting its continuation (first stuck point)? -/
partial def kappaParametric (s : Expr) (i : Nat) : SearchM Bool := do
  let stTy ← liftCore <| inCtx (inferType s.getAppArgs[i]!)
  let probe ← liftCore (mkVar `κprobe stTy .kappa false)
  let s' := mkAppN s.getAppFn (s.getAppArgs.set! i probe)
  let M := (← getThe Core).machine
  let some r ← liftCore (inCtx (M.step s')) | return false
  match r with
  | .stuck e =>
    match ← liftCore (findStuck e) with
    | .data atom _ => return atom != probe
    | _ => return true
  | _ => return true

/-- A call of a designated procedure: explore its body once, then continue at
the return state. -/
partial def handleCall (s : Expr) (path : Path) (ctx : Ctx) : SearchM (Nat × Option (Nat × Path)) := do
  let i := (← stackArg? s).get!
  let ck ← liftCore (codeKeyOf s i)
  bump fun st => {st with calls := st.calls + 1}
  let pid := (← get).procByCode[ck]!
  let p := (← get).procs[pid]!
  let stack := s.getAppArgs[i]!
  let callBody := mkAppN s.getAppFn (s.getAppArgs.set! i p.kappa)
  let body ← match p.body? with
    | none => pure callBody
    | some t =>
      match ← liftCore (instanceOf? t callBody #[p.kappa.fvarId!]) with
      | some _ => pure t
      | none => do
        let (t', _) ← liftCore (antiUnify t callBody #[p.kappa.fvarId!])
        modify fun st => {st with procs := st.procs.modify pid fun q =>
          {q with status := .fresh, version := q.version + 1}}
        pure t'
  modify fun st => {st with procs := st.procs.modify pid fun q => {q with body? := some body}}
  let p := (← get).procs[pid]!
  if p.status == .fresh then
    -- explore the body until its exit shape is stable: recursive calls return
    -- at the seeded shape, which must equal the shape of every exit found
    let saved := (← get).created
    let mut seed : Option Expr := none
    let mut first := true
    repeat
      unless first do
        modify fun st => {st with procs := st.procs.modify pid fun q => {q with version := q.version + 1}}
      first := false
      modify fun st => {st with procs := st.procs.modify pid fun q =>
        {q with status := .exploring, exits := #[], shape? := seed, seed? := seed, pending := #[]}}
      let p := (← get).procs[pid]!
      let pctx0 : Ctx := {proc? := some (pid, p.kappa), procVersion := p.version}
      let k0 := ctxKey pctx0 (← liftCore (stateKey body))
      let entry ← newTpl k0 body #[] pctx0
      let pctx := {pctx0 with entry? := some entry}
      modify fun st => {st with
        procs := st.procs.modify pid fun q => {q with entry? := some entry}
        tpls := st.tpls.modify entry fun t => {t with entry? := some entry}}
      exploreSeg entry {} pctx
      -- deferred return points (no seed yet): explore them at the current shape
      let q := (← get).procs[pid]!
      if let some sh := q.shape? then
        modify fun st => {st with procs := st.procs.modify pid fun q => {q with pending := #[]}}
        for (callNode, st) in q.pending do
          let r ← instReturn sh q.kappa st
          let (retNode, cont) ← arrive r {} pctx
          if let some (nid, path') := cont then exploreSeg nid path' pctx
          match (← get).nodes[callNode]! with
          | .call cs pr en _ _ => setNode callNode (.call cs pr en (some sh) (some retNode))
          | _ => pure ()
      let final := (← get).procs[pid]!.shape?
      let pendingNow := (← get).procs[pid]!.pending.isEmpty
      let stable : Bool := match final, seed with
        | none, _ => true
        | some f, some sd => f == sd
        | some _, none => pendingNow && q.pending.isEmpty
      if stable then break
      seed := final
    modify fun st => {st with created := saved, procs := st.procs.modify pid fun q => {q with status := .explored}}
  let p := (← get).procs[pid]!
  let entry := p.entry?.get!
  -- inside its own exploration, a recursive call returns at the seed
  let shape? := if p.status == .exploring then p.seed? else p.shape?
  match shape? with
  | none =>
    let node ← addNode (.call s pid entry none none)
    if p.status == .exploring then
      modify fun st => {st with procs := st.procs.modify pid fun q =>
        {q with pending := q.pending.push (node, stack)}}
    return (node, none)
  | some sh =>
    let r ← instReturn sh p.kappa stack
    let (retNode, cont) ← arrive r path ctx
    return (← addNode (.call s pid entry (some sh) (some retNode)), cont)

/-- Instantiate an exit shape at a return point: the caller's continuation for
`κ` and fresh variables for the shape's holes. -/
partial def instReturn (shape kappa stack : Expr) : SearchM Expr := do
  let holes ← liftCore (patternVars shape)
  let mut v := shape.replaceFVar kappa stack
  for fv in holes.toList do
    if fv == kappa.fvarId! then continue
    let ty ← liftCore <| inCtx (inferType (.fvar fv))
    let nv ← liftCore (mkVar `r ty .ret false)
    v := v.replaceFVar (.fvar fv) nv
  return v

/-- Resolve a step result into a transition tree node. -/
partial def resolve (r : StepResult) (path : Path) (ctx : Ctx) (pre : Expr) : SearchM Nat := do
  match r with
  | .accept => bump (fun st => {st with accepts := st.accepts + 1}); addNode .accept
  | .reject => bump (fun st => {st with rejects := st.rejects + 1}); addNode .reject
  | .leaf p => bump (fun st => {st with leaves := st.leaves + 1}); addNode (.leaf p)
  | .next s =>
    -- keep encoded lists in mapped form before the state meets a template
    -- (where an unrecognized producer application would be generalized)
    if let some (f, rhs, proof, s') ← liftCore (eagerMap? s) then
      let next ← resolve (.next s') path ctx pre
      return ← addNode (.rewrite f rhs proof next)
    let (node, cont) ← arrive s path ctx
    if let some (id, path') := cont then exploreSeg id path' ctx
    return node
  | .stuck e => resolveStuck e path ctx pre

/-- Continue the step that reduced to `e` (from the state `pre`). -/
partial def continueWith (e : Expr) (path : Path) (ctx : Ctx) (pre : Expr) : SearchM Nat := do
  -- an encoded list computed by an element-wise producer is kept in its
  -- mapped form (`List.map element source`, checked equality), so that the
  -- typed source list is what later splits and templates generalize
  if let some (f, rhs, proof, e') ← liftCore (eagerMap? e) then
    let next ← continueWith e' path ctx (replaceConstTerm pre f rhs)
    return ← addNode (.rewrite f rhs proof next)
  let M := (← getThe Core).machine
  let some r ← liftCore (inCtx (M.resume e)) | abortNode "resume budget"
  resolve r path ctx pre

/-- An `abort` node. -/
partial def abortNode (why : String) : SearchM Nat := do
  bump fun st => {st with aborts := st.aborts + 1}
  addNode (.abort why)

/-- An `unreachable` node. -/
partial def unreachableNode (why : String) : SearchM Nat := do
  bump fun st => {st with unreachables := st.unreachables + 1}
  addNode (.unreachable why)

/-- Resolve a step stuck at `e`: split, generalize, decide or rewrite what it
is stuck on (`findStuck`), and continue in each case. -/
partial def resolveStuck (e : Expr) (path : Path) (ctx : Ctx) (pre : Expr) : SearchM Nat := do
  -- one machine step resolves finitely many stuck points: an unbounded chain
  -- (a recursive computation on symbolic data inside one step) must be refuted
  let path := {path with depth := path.depth + 1}
  if path.depth > maxStuckDepth then
    return ← unreachableNode "split depth"
  let why ← liftCore (findStuck e)
  match why with
  | .data atom motive =>
    -- the stuck expression with the scrutinized discriminant in reduced form
    let e := motive.beta #[atom]
    if let some (pid, kappa) := ctx.proc? then
      if atom == kappa then
        -- a procedure exit: the pre-step state needs the continuation
        bump fun st => {st with exits := st.exits + 1}
        let p := (← get).procs[pid]!
        let sh ← match p.shape? with
          | none => pure pre
          | some sh => do
            match ← liftCore (instanceOf? sh pre #[kappa.fvarId!]) with
            | some _ => pure sh
            | none => pure (← liftCore (antiUnify sh pre #[kappa.fvarId!])).1
        modify fun st => {st with procs := st.procs.modify pid fun q =>
          {q with exits := q.exits.push pre, shape? := some sh}}
        return ← addNode (.exit pre)
    if !atom.isFVar then
      bump fun st => {st with gens := st.gens + 1}
      if let some (_, g) := path.defs.find? (·.1 == atom) then
        let e' := replaceTerm e atom g
        let pre' := replaceTerm pre atom g
        if let some (_, v) := path.splits.find? (·.1 == g) then
          let next ← continueWith (replaceTerm e' g v) path ctx (replaceTerm pre' g v)
          let inner ← addNode (.known g v next)
          return ← addNode (.gen atom g false inner)
        let next ← resolveStuck e' path ctx pre'
        return ← addNode (.gen atom g false next)
      let g ← liftCore (genVar atom)
      let path' := {path with defs := path.defs.push (atom, g)}
      let next ← resolveStuck (replaceTerm e atom g) path' ctx (replaceTerm pre atom g)
      return ← addNode (.gen atom g true next)
    let (ty, info?) ← liftCore <| inCtx do
      let ty ← whnf (← inferType atom)
      pure (ty, ← inductiveType? ty)
    let some info := info? | abortNode "split on non-inductive"
    if info.numIndices != 0 then return ← abortNode "split on indexed family"
    -- a variable standing for program code: the program run from here is
    -- unknown (an over-general template or summary), so this point must be
    -- refuted rather than explored
    if (← getThe Core).machine.codeType? == some ty then return ← unreachableNode "symbolic code"
    bump fun st => {st with splits := st.splits + 1}
    let ls := ty.getAppFn.constLevels!
    let params := ty.getAppArgs.extract 0 info.numParams
    let isGen := match (← getThe Core).vars[atom.fvarId!]? with
      | some {origin := .gen _, ..} => true
      | _ => false
    let mut alts := #[]
    for c in info.ctors do
      let cinfo ← getConstInfo c
      let cty ← liftCore <| inCtx <|
        instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params
      let fields ← liftCore (splitFields atom c cty)
      let app := mkAppN (mkAppN (mkConst c ls) params) fields
      let sub := fun (x : Expr) => x.replaceFVar atom app
      let path' : Path := {
        decisions := path.decisions.map fun d => {d with prop := sub d.prop}
        defs := path.defs.map fun (a, b) => (sub a, b)
        splits := (path.splits.map fun (a, b) => (a, sub b)) ++
          (if isGen then #[(atom, app)] else #[])
        depth := path.depth }
      let next ← continueWith (sub e) path' ctx (sub pre)
      alts := alts.push (c, fields, next)
    addNode (.split atom alts)
  | .cond inst prop motive =>
    let e := motive.beta #[inst]
    if let some d := path.decisions.find? (·.prop == prop) then
      useHyps #[d.hyp]
      let inst' ← liftCore <| inCtx do
        if d.positive then mkAppOptM ``Decidable.isTrue #[prop, d.hyp]
        else mkAppOptM ``Decidable.isFalse #[prop, d.hyp]
      let next ← continueWith (replaceTerm e inst inst') path ctx pre
      return ← addNode (.knownCond inst prop d.positive d.hyp next)
    bump fun st => {st with conds := st.conds + 1}
    let hT ← liftCore (hypVar prop true)
    let hF ← liftCore (hypVar prop false)
    let instT ← liftCore <| inCtx (mkAppOptM ``Decidable.isTrue #[prop, hT])
    let instF ← liftCore <| inCtx (mkAppOptM ``Decidable.isFalse #[prop, hF])
    let t ← continueWith (replaceTerm e inst instT)
      {path with decisions := path.decisions.push {prop, positive := true, hyp := hT}} ctx pre
    let f ← continueWith (replaceTerm e inst instF)
      {path with decisions := path.decisions.push {prop, positive := false, hyp := hF}} ctx pre
    addNode (.cond inst prop hT hF t f)
  | .rewrite lhs rhs proof focus motive =>
    let e := replaceTerm (motive.beta #[focus]) lhs rhs
    let pre' := replaceTerm pre lhs rhs
    let next ← continueWith e path ctx pre'
    addNode (.rewrite lhs rhs proof next)
  | .other e' why =>
    let str ← liftCore <| inCtx do return toString (← ppExpr e') |>.take 300
    abortNode s!"{why}: {str}"

end

/-! ## Results -/

/-- An exploration: its variables, its search, and the state it started from. -/
structure Result where
  core : Core
  search : Search
  initial : Expr

/-- Explore from `initial` (a fuel-less machine state in the current local
context; its free variables are the roots). -/
def run (M : Machine) (initial : Expr) : MetaM Result := M.withOpaque do
  let lctx ← getLCtx
  let mut vars : Std.HashMap FVarId VarInfo := {}
  for d in lctx do vars := vars.insert d.fvarId {origin := .root, rootish := true}
  let budget := blaster.explore.maxStates.get (← getOptions)
  let go : SearchM Unit := do
    let s ← liftCore (normState initial)
    let k ← liftCore (stateKey s)
    exploreSeg (← newTpl k s #[] {}) {} {}
  let ((_, search), core) ← (go.run {budget}).run {lctx, machine := M, vars}
  return {core, search, initial}

/-- The statistics of an exploration, for the progress reports. -/
def Result.summary (r : Result) : String :=
  let st := r.search.stats
  s!"states={st.states} templates={st.templates} joins={st.joins} loops={st.loops} widenings={st.widenings} cross={st.crossWidenings} restarts={st.restarts} splits={st.splits} gens={st.gens} conds={st.conds} accepts={st.accepts} rejects={st.rejects} leaves={st.leaves} aborts={st.aborts} unreachables={st.unreachables} procs={r.search.procs.size} calls={st.calls} exits={st.exits} growths={st.growths} nodes={r.search.nodes.size}"

end Blaster.Proof.Explore
