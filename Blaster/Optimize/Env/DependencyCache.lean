import Blaster.Optimize.Env.ContextMap

/-! Context-dependent caching of the optimizer's rewrites. A rewrite made under
hypotheses records the assumption scopes (contexts) it consulted; it is reused
in another context only where those scopes are active and no newer fact
concerns the variables of its result (which could enable further rewrites). -/

open Lean Blaster.Data.HashMap Blaster.Data.HashSet
namespace Blaster.Optimize

/-- A normalization result together with the assumption scopes it consulted. -/
structure CachedRewrite where
  value : Expr
  /-- The scopes whose facts the rewrite consulted. -/
  dependencies : Array CtxId := #[]
  /-- The scope it was made in, and the fact generation then. -/
  origin : CtxId := 0
  generation : Nat := 0
  /-- The variables (and field paths) of `value`. -/
  variables : Array Expr := #[]

/-- What the facts of one scope are about. -/
structure ScopeFacts where
  /-- The generation of its newest fact. -/
  generation : Nat := 0
  /-- The variables and field paths its facts mention, and their prefixes. -/
  variables : HashSet PtrExpr := HashSet.emptyWithCapacity
  prefixes : HashSet PtrExpr := HashSet.emptyWithCapacity

/-- The dependency tracking of a translation (see the module documentation). -/
structure RewriteDependencies where
  /-- Counts the consultations of scopes. -/
  clock : Nat := 0
  /-- When each scope was last consulted. -/
  lastUsed : HashMap CtxId Nat := HashMap.emptyWithCapacity
  /-- The last 64 consultations (a ring indexed by the clock). -/
  recentUses : Array CtxId := #[]
  /-- Rewrites shared across contexts, with their dependencies. -/
  shared : HashMap PtrExpr CachedRewrite := HashMap.emptyWithCapacity
  /-- Context-independent recursive rewrites, closed over their free variables. -/
  alpha : HashMap PtrExpr Expr := HashMap.emptyWithCapacity
  /-- Counts the facts added. -/
  generation : Nat := 0
  scopes : HashMap CtxId ScopeFacts := HashMap.emptyWithCapacity
  /-- Invert the scope footprint so lookup visits only facts about a result's
      atoms. Histories retain inactive scopes for later context reuse. -/
  variableOwners : HashMap PtrExpr (ContextEntries Unit) := HashMap.emptyWithCapacity
  prefixOwners : HashMap PtrExpr (ContextEntries Unit) := HashMap.emptyWithCapacity
  /-- The variables of each expression (`variablesOf`), memoized. -/
  variables : HashMap PtrExpr (Array Expr) := HashMap.emptyWithCapacity
  /-- The ancestors of each scope (itself included). -/
  paths : HashMap CtxId (Lean.PersistentHashMap CtxId Unit) := HashMap.emptyWithCapacity
  /-- Pointer-keyed memo tables over maximally shared expressions: free
      variable occurrences and watermarks (`Abstract.lean`), list spines
      (`OptimizeList.lean`) and instance applications (`Telescope.lean`).
      `PtrExpr` retains its expression, so an address is never reused while
      its entry exists; the tables live as long as the translation. -/
  fvarOccurs : Lean.PersistentHashMap (PtrExpr × FVarId) Bool := {}
  fvarMax : Lean.PersistentHashMap PtrExpr Nat := {}
  listSpines : Lean.PersistentHashMap PtrExpr (Option (List Expr)) := {}
  instApps : Lean.PersistentHashMap (PtrExpr × Array (PtrExpr × Bool × Bool)) Expr := {}

/-- The optimizer's rewrite caches: one per context, and the dependency tracking. -/
structure RewriteCacheMap where
  contexts : HashMap CtxId (IO.Ref (HashMap PtrExpr CachedRewrite))
  dependencies : Option (IO.Ref RewriteDependencies) := none

/-- No cache yet, with room for `capacity` contexts. -/
def RewriteCacheMap.emptyWithCapacity (capacity : Nat) : RewriteCacheMap :=
  ⟨HashMap.emptyWithCapacity capacity, none⟩

/-- The cache of context `ctx`, if any. -/
def RewriteCacheMap.get? (cache : RewriteCacheMap) (ctx : CtxId) :=
  cache.contexts.get? ctx

/-- Set the cache of context `ctx`. -/
def RewriteCacheMap.insert (cache : RewriteCacheMap) (ctx : CtxId)
    (entries : IO.Ref (HashMap PtrExpr CachedRewrite)) : RewriteCacheMap :=
  {cache with contexts := cache.contexts.insert ctx entries}

/-- Drop the cache of context `ctx`. -/
def RewriteCacheMap.erase (cache : RewriteCacheMap) (ctx : CtxId) : RewriteCacheMap :=
  {cache with contexts := cache.contexts.erase ctx}

/-- Record that a fact of scope `ctx` was consulted (the global scope `0` is always valid). -/
def RewriteDependencies.use (ref : IO.Ref RewriteDependencies) (ctx : CtxId) : IO Unit := do
  if ctx == 0 then return
  ref.modify fun state =>
    { state with
      clock := state.clock + 1
      lastUsed := state.lastUsed.insert ctx (state.clock + 1)
      recentUses := if state.recentUses.size < 64 then state.recentUses.push ctx
        else state.recentUses.set! (state.clock % 64) ctx }

/-- The variables of `expression`, a variable's field paths counting as
variables (`x.1.2`), memoized. -/
def RewriteDependencies.variablesOf (ref : IO.Ref RewriteDependencies)
    (expression : Expr) : IO (Array Expr) := do
  if !expression.hasFVar then return #[]
  if let some variables := (← ref.get).variables.get? expression then return variables
  -- Move the table out while extending it. Keeping the old table in the ref
  -- forces a full copy-on-write on the first insertion of every new parent.
  let mut cache ← ref.modifyGet fun state =>
    (state.variables, {state with variables := HashMap.emptyWithCapacity})
  let mut pending := #[(expression, false)]
  while !pending.isEmpty do
    let (e, ready) := pending.back!
    pending := pending.pop
    if !e.hasFVar || (cache.get? e).isSome then continue
    match e with
    | .fvar _ => cache := cache.insert e #[e]
    | .proj _ _ base =>
        let mut root := base
        while root.isProj do root := root.projExpr!
        if root.isFVar then cache := cache.insert e #[e]
        else if ready then cache := cache.insert e (cache.getD base #[])
        else pending := pending.push (e, true) |>.push (base, false)
    | _ =>
        let children := match e with
          | .app f a => #[f, a]
          | .lam _ t b _ | .forallE _ t b _ => #[t, b]
          | .letE _ t v b _ => #[t, v, b]
          | .mdata _ b => #[b]
          | _ => #[]
        if ready then
          let support := children.foldl
            (fun acc (child : Expr) => mergeSupport acc (cache.getD child #[])) #[]
          cache := cache.insert e support
        else
          pending := pending.push (e, true)
          for child in children do pending := pending.push (child, false)
  ref.modify fun state => {state with variables := cache}
  return cache.getD expression #[]
where
  /-- Reuse a child's support array when the parent adds no new dependency.
      Growing expression spines otherwise copy/scan their entire old subtree. -/
  mergeSupport (left right : Array Expr) : Array Expr := Id.run do
    -- Constructor DAGs often expose the same support through several fields.
    -- Rechecking every member against that same array is quadratic in the
    -- number of captured variables, despite adding no dependency at all.
    if (unsafe ptrEq left right) || left == right then return left
    let (large, small) := if left.size ≥ right.size then (left, right) else (right, left)
    let mut result := large
    if small.size ≤ 8 then
      for atom in small do
        unless result.contains atom do result := result.push atom
    else
      -- Keep small supports allocation-free, but index wide unions. Structural
      -- Expr equality is intentional: not every footprint caller hash-conses
      -- separately allocated but equal field paths before querying this cache.
      let mut seen : Std.HashSet Expr := Std.HashSet.ofArray large
      for atom in small do
        unless seen.contains atom do
          seen := seen.insert atom
          result := result.push atom
    return result

/-- Share ancestor paths structurally. Retaining a flat active-set snapshot at
    every rewrite duplicates a large hash table whenever a scope is opened. -/
def RewriteDependencies.enter (ref : IO.Ref RewriteDependencies)
    (parent current : CtxId) : IO Unit := do
  ref.modify fun state =>
    let path := ((state.paths.get? parent).getD {}).insert current ()
    {state with paths := state.paths.insert current path}

/-- A new fact can enable additional rewrites even when a previous answer
    remains valid. Conservatively invalidate sharing for overlapping variables. -/
def RewriteDependencies.addFact (ref : IO.Ref RewriteDependencies)
    (ctx : CtxId) (expression : Expr) : IO Unit := do
  let variables ← RewriteDependencies.variablesOf ref expression
  ref.modify fun state =>
    let old := (state.scopes.get? ctx).getD {}
    let generation := state.generation + 1
    let (scope, variableOwners, prefixOwners) := Id.run do
      let mut paths := old.variables
      let mut prefixes := old.prefixes
      let mut variableOwners := state.variableOwners
      let mut prefixOwners := state.prefixOwners
      for atom in variables do
        unless paths.contains atom do
          paths := paths.insert atom
          variableOwners := addOwner variableOwners atom ctx
        let mut pathPart := atom
        unless prefixes.contains pathPart do
          prefixes := prefixes.insert pathPart
          prefixOwners := addOwner prefixOwners pathPart ctx
        while pathPart.isProj do
          pathPart := pathPart.projExpr!
          unless prefixes.contains pathPart do
            prefixes := prefixes.insert pathPart
            prefixOwners := addOwner prefixOwners pathPart ctx
      return (ScopeFacts.mk generation paths prefixes, variableOwners, prefixOwners)
    {state with
      generation := generation
      variableOwners := variableOwners
      prefixOwners := prefixOwners
      scopes := state.scopes.insert ctx scope}
where
  addOwner (index : HashMap PtrExpr (ContextEntries Unit)) (atom : Expr)
      (ctx : CtxId) : HashMap PtrExpr (ContextEntries Unit) :=
    let owners := match index.get? atom with
      | none => ContextEntries.singleton ctx ()
      | some history => history.insert ctx ()
    index.insert atom owners

/-- Record the consultations of a reused rewrite, as if it were made again. -/
def RewriteDependencies.replay (ref : IO.Ref RewriteDependencies)
    (entry : CachedRewrite) : IO Unit := do
  for ctx in entry.dependencies do RewriteDependencies.use ref ctx

/-- Branch-local facts discharged before return are not external dependencies
    of the enclosing match/lambda. Retain only scopes still active at return. -/
def RewriteDependencies.since (ref : IO.Ref RewriteDependencies) (start : Nat)
    (active : HashSet CtxId) : IO (Array CtxId) := do
  let state ← ref.get
  if state.clock == start then return #[]
  let mut result := #[]
  -- Most rewrites consult only one or two facts. Avoid scanning the whole
  -- active context for these; a bounded ring retains every recent read.
  if state.clock - start ≤ 64 then
    for stamp in [start:state.clock] do
      let ctx := state.recentUses[stamp % 64]!
      if active.contains ctx && !result.contains ctx then result := result.push ctx
    return result
  for i in [:active.ctrl.size] do
    if active.ctrl.get! i &&& 0x80 == 0 then continue
    let ctx := active.data[i]!
    if (state.lastUsed.get? ctx).getD 0 > start then result := result.push ctx
  return result

/-- Share the rewrite of `source` made in context `current` with the other
contexts (a rewrite of `source` shared already stays if its dependencies are
among this one's: it is valid wherever this one is). -/
def RewriteDependencies.publish (ref : IO.Ref RewriteDependencies)
    (source : Expr) (entry : CachedRewrite)
    (current : CtxId := 0) : IO Unit := do
  -- Most publications repeat an existing result. Check that before collecting
  -- its free variables, not after allocating the same footprint again.
  if let some old := (← ref.get).shared.get? source then
    if old.dependencies.all (entry.dependencies.contains ·) then return
  let outputVariables ← RewriteDependencies.variablesOf ref entry.value
  let generation := (← ref.get).generation
  let entry := {entry with
    origin := current
    generation := generation
    variables := outputVariables}
  ref.modify fun state =>
    match state.shared.get? source with
    | some old =>
        if old.dependencies.all (entry.dependencies.contains ·) then state
        else {state with shared := state.shared.insert source entry}
    | none => {state with shared := state.shared.insert source entry}

/-- Whether an active scope has facts about `variables` that are newer than
`generation` or outside the path `origin` (all of them without a path). -/
private def RewriteDependencies.relevantAtoms (state : RewriteDependencies)
    (variables : Array Expr) (active : HashSet CtxId)
    (origin : Option (Lean.PersistentHashMap CtxId Unit)) (generation : Nat) : Bool := Id.run do
  for atom in variables do
    if let some owners := state.prefixOwners.get? atom then
      if relevantOwner owners then return true
    let mut pathPart := atom
    while pathPart.isProj do
      pathPart := pathPart.projExpr!
      if let some owners := state.variableOwners.get? pathPart then
        if relevantOwner owners then return true
  return false
where
  relevantContext (ctx : CtxId) : Bool :=
    active.contains ctx && match state.scopes.get? ctx with
      | none => false
      | some scope => match origin with
        | none => true
        | some path => !path.contains ctx || scope.generation > generation

  -- Small histories are bounded. Once indexed, scan active contexts instead
  -- of an unbounded collection of retired siblings. Any relevant owner must
  -- invalidate: the newest active owner alone is not sufficient.
  relevantOwner (owners : ContextEntries Unit) : Bool := Id.run do
    let recent := match owners with
      | .small _ entries => entries
      | .indexed _ entries _ => entries
    if recent.any (fun entry => relevantContext entry.1) then return true
    let .indexed _ _ entries := owners | return false
    for i in [:active.ctrl.size] do
      if active.ctrl.get! i &&& 0x80 == 0 then continue
      let ctx := active.data[i]!
      if (entries.get? ctx).isSome && relevantContext ctx then return true
    return false

/-- A shared rewrite of `source` valid in the active contexts: its dependencies
active, and no fact it could not see about the variables of its result. -/
def RewriteDependencies.find? (ref : IO.Ref RewriteDependencies) (source : Expr)
    (active : HashSet CtxId) : IO (Option CachedRewrite) := do
  let some entry := (← ref.get).shared.get? source | return none
  unless entry.dependencies.all active.contains do return none
  let state ← ref.get
  let origin := (state.paths.get? entry.origin).getD {}
  if state.relevantAtoms entry.variables active (some origin) entry.generation then return none
  RewriteDependencies.replay ref entry
  return some entry

/-- A renamed template is valid without assumptions, but must not hide new
    simplifications enabled by facts about its instantiated result. -/
def RewriteDependencies.hasRelevantFacts (ref : IO.Ref RewriteDependencies)
    (expression : Expr) (active : HashSet CtxId) : IO Bool := do
  let variables ← RewriteDependencies.variablesOf ref expression
  let state ← ref.get
  return state.relevantAtoms variables active none 0

end Blaster.Optimize
