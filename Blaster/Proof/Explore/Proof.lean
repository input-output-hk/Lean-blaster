import Blaster.Proof.Explore.Search

/-!
# Symbolic exploration: proof replay

Turn a recorded exploration into a proof of `G` from `Obs(initial) N`.

* *Cut points* are the root template, the templates entered by more than one
  edge (loop heads, joins) or through a proper instance, and procedure
  entries. Other templates are inlined into their unique predecessor.
* Each cut point `c` gets a statement `Stmt_c n`:
  `∀ x̄, Facts_c x̄ → Inv_c x̄ → Obs(T_c x̄) n → G` in the main region, and in a
  procedure region the exit summary
  `… → ∃ m, m ≤ n ∧ ∃ h̄, Post h̄ ∧ Obs(Shape h̄) m`.
  All statements are proved together by strong induction on the fuel.
* Long inlined regions are *lambda-lifted*: after `liftDepth` inlined
  templates the replay stops at an extra statement whose premises are exactly
  the logical facts collected on the path. Every proof term therefore stays
  small (building one deep term costs quadratic time in binder abstraction).
* A statement's proof replays the recorded transition trees: predicates are
  unfolded with their checked equations; the fuel is split whenever a
  reduction needs it; recorded variables are split with an equation; recorded
  subterms are generalized with an equation; recorded decisions are
  case-analysed; recorded rewrites use their checked equations. Every
  reduction is re-checked by the kernel.
* Leaves produce verification conditions (closed propositions over data only):
  acceptance must imply `G`, an edge into a cut point must establish its facts
  and invariant, and a procedure exit its postcondition. A caller-supplied
  prover discharges them.

Invariants and postconditions are inputs: ordinary propositions checked by the
verification conditions. A wrong one makes a condition fail, never a proof.
-/
namespace Blaster.Proof.Explore
open Lean Meta

register_option blaster.explore.liftDepth : Nat := {
  defValue := 24
  descr := "Inlined templates after which a replay region is lambda-lifted" }

/-- A variable or hypothesis introduced along a replay path. -/
structure Local where
  fvar : Expr
  /-- Included in verification conditions (data variables and data facts). -/
  logical : Bool
deriving Inhabited

/-- A cut point of a plan: a template with a statement of its own. -/
structure CutInfo where
  tpl : Nat
  /-- Entry template of the enclosing procedure region, if any. -/
  entry? : Option Nat := none
  /-- Quantified variables of the statement (non-root free variables). -/
  vars : Array Expr
  /-- Premises over `vars` that hold whenever the template is reached. -/
  facts : Array Expr
  /-- The invariant: a proposition over `vars` and the roots. -/
  inv : Expr
deriving Inhabited

/-- Values of exploration variables. -/
abbrev Subst := Std.HashMap FVarId Expr

/-- `e` with the variables of `σ` replaced by their values. -/
def Subst.apply (σ : Subst) (e : Expr) : Expr :=
  if σ.isEmpty then e else
  e.replace fun t => match t with
    | .fvar id => σ[id]?
    | _ => none

/-- Whether `σ` maps each variable to itself. -/
def isIdentity (σ : Subst) : Bool :=
  σ.toList.all fun (id, e) => e == .fvar id

/-- The resolved transition graph of an exploration (`planGraph`). -/
structure Graph where
  /-- The template of the initial state, and the instance of it that state is. -/
  rootTpl : Nat
  rootSubst : Subst
  /-- Resolved edges: goto node ↦ target template and substitution. -/
  targets : Std.HashMap Nat (Nat × Subst)
  /-- The templates of the cut points: the root first. -/
  cuts : Array Nat
  /-- Procedure entry templates and their exit shapes. -/
  shapes : Std.HashMap Nat Expr := {}

/-! ## Planning -/

/-- The newest non-abandoned template for `key` of which `s` is an instance. -/
def resolveState (r : Result) (key : UInt64) (s : Expr) : ExM (Option (Nat × Subst)) := do
  let versions := r.search.byKey.getD key #[]
  for v in versions.reverse do
    let t := r.search.tpls[v]!
    if t.abandoned || !t.done then continue
    if let some σ ← instanceOf? t.body s then return some (v, σ)
  return none

/-- Goto nodes of a transition tree. -/
partial def gotosOf (r : Result) (node : Nat) (acc : Array Nat := #[]) : Array Nat :=
  match r.search.nodes[node]! with
  | .split _ alts => alts.foldl (fun acc (_, _, n) => gotosOf r n acc) acc
  | .gen _ _ _ n | .known _ _ n | .knownCond _ _ _ _ n | .rewrite _ _ _ n => gotosOf r n acc
  | .cond _ _ _ _ t f => gotosOf r f (gotosOf r t acc)
  | .goto .. => acc.push node
  | .call _ _ _ _ (some n) => gotosOf r n acc
  | _ => acc

/-- Call nodes of a transition tree. -/
partial def callsOf (r : Result) (node : Nat) (acc : Array Nat := #[]) : Array Nat :=
  match r.search.nodes[node]! with
  | .split _ alts => alts.foldl (fun acc (_, _, n) => callsOf r n acc) acc
  | .gen _ _ _ n | .known _ _ n | .knownCond _ _ _ _ n | .rewrite _ _ _ n => callsOf r n acc
  | .cond _ _ _ _ t f => callsOf r f (callsOf r t acc)
  | .call _ _ _ _ ret =>
    let acc := acc.push node
    match ret with
    | some n => callsOf r n acc
    | none => acc
  | _ => acc

/-- Resolve every edge reachable from the root (and from every procedure entry
it calls) and choose the cut points. -/
def planGraph (r : Result) : ExM Graph := do
  let initial ← normState r.initial
  let rootKey ← stateKey initial
  let some (rootTpl, rootSubst) ← resolveState r rootKey initial
    | throwError "explore: the initial state matches no explored template"
  let mut targets : Std.HashMap Nat (Nat × Subst) := {}
  let mut indeg : Std.HashMap Nat Nat := {}
  let mut proper : Std.HashSet Nat := {}
  let mut shapes : Std.HashMap Nat Expr := {}
  let mut seen : Std.HashSet Nat := {rootTpl}
  let mut todo := #[rootTpl]
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    let some node := r.search.tpls[t]!.node? | throwError "explore: template {t} has no transition"
    for g in gotosOf r node do
      let .goto s key := r.search.nodes[g]! | unreachable!
      let some (v, σ) ← resolveState r key s
        | throwError "explore: an edge matches no explored template"
      targets := targets.insert g (v, σ)
      indeg := indeg.insert v (indeg.getD v 0 + 1)
      unless isIdentity σ do proper := proper.insert v
      unless seen.contains v do
        seen := seen.insert v
        todo := todo.push v
    for c in callsOf r node do
      let .call _ _ entry shape? _ := r.search.nodes[c]! | unreachable!
      let some shape := shape? | throwError "explore: a call without an exit shape"
      match shapes[entry]? with
      | some sh => unless sh == shape do throwError "explore: calls disagree on an exit shape"
      | none => shapes := shapes.insert entry shape
      unless seen.contains entry do
        seen := seen.insert entry
        todo := todo.push entry
  let mut cuts := #[rootTpl]
  for v in seen.toArray.qsort (· < ·) do
    if v == rootTpl then continue
    if indeg.getD v 0 ≥ 2 || proper.contains v || shapes.contains v then cuts := cuts.push v
  return {rootTpl, rootSubst, targets, cuts, shapes}

/-! ## Statements -/

/-- What a proof replays: an exploration, its graph, the goal, and the
statement of each cut point. -/
structure Plan where
  result : Result
  graph : Graph
  goal : Expr
  /-- Roots and original hypotheses closing every verification condition. -/
  context : Array Expr
  cuts : Array CutInfo
  /-- The cut point of each cut template. -/
  cutOf : Std.HashMap Nat Nat
  /-- Procedure summaries: entry template ↦ exit holes and postcondition. -/
  holes : Std.HashMap Nat (Array Expr) := {}
  posts : Std.HashMap Nat Expr := {}
  /-- Ghost placeholders (one per entry observation) that postconditions and
  inner invariants mention, and the entry observations they stand for. -/
  ghostVars : Std.HashMap Nat (Array Expr) := {}
  ghostVals : Std.HashMap Nat (Array Expr) := {}

/-- Holes of an exit shape (context order), excluding the continuation. -/
def shapeHoles (shape : Expr) (kappa? : Option Expr) : ExM (Array Expr) := do
  let vars := (← get).vars
  let lctx := (← get).lctx
  let fvs := (collectFVars {} shape).fvarIds.filter fun id =>
    kappa?.all (·.fvarId! != id) && !(vars[id]?.any (·.rootish))
  for id in fvs do
    unless lctx.contains id do throwError "explore: exit shape mentions an unknown variable {id.name}"
  return (fvs.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map (.fvar ·)

/-- `∃ m, m ≤ n ∧ ∃ h̄, post ∧ Obs(shape) m`. -/
def exitConcl (shape post : Expr) (holes : Array Expr) (n : Expr) : ExM Expr := inCtx do
  withLocalDeclD `m (mkConst ``Nat) fun m => do
    let mut body := mkAnd post (mkApp shape m)
    for h in holes.reverse do body ← mkAppM ``Exists #[← mkLambdaFVars #[h] body]
    let le ← mkAppM ``LE.le #[m, n]
    mkAppM ``Exists #[← mkLambdaFVars #[m] (mkAnd le body)]

/-- The conclusion of a statement in region `entry?` at fuel `n`, with the
region's ghost placeholders instantiated by `ghosts`. -/
def regionConcl (plan : Plan) (entry? : Option Nat) (n : Expr) (ghosts : Array Expr := #[]) :
    ExM Expr := do
  match entry? with
  | none => return plan.goal
  | some e =>
    let shape := plan.graph.shapes[e]!
    let gv := plan.ghostVars.getD e #[]
    let post := (plan.posts.getD e (mkConst ``True)).replaceFVars gv (if ghosts.size == gv.size then ghosts else gv)
    exitConcl shape post (plan.holes.getD e #[]) n

/-- Is `c` an inner cut point of a procedure region (not its entry)? -/
def CutInfo.inner (c : CutInfo) : Bool := c.entry?.any (· != c.tpl)

/-- Ghost binders of a cut statement and the ghost values its conclusion uses. -/
def cutGhosts (plan : Plan) (c : CutInfo) : Array Expr × Array Expr :=
  match c.entry? with
  | none => (#[], #[])
  | some e =>
    if c.inner then (plan.ghostVars.getD e #[], plan.ghostVars.getD e #[])
    else (#[], (plan.ghostVals.getD e #[]))

/-- The statement `Stmt_c n` of a planned cut point. -/
def cutStmt (plan : Plan) (c : CutInfo) (n : Expr) : ExM Expr := do
  let body := plan.result.search.tpls[c.tpl]!.body
  let (binders, ghosts) := cutGhosts plan c
  let concl ← regionConcl plan c.entry? n ghosts
  inCtx do
    let mut ty := mkForall `hobs .default (mkApp body n) concl
    ty := mkForall `inv .default c.inv ty
    for f in c.facts.reverse do ty := mkForall `fact .default f ty
    mkForallFVars (binders ++ c.vars) ty

/-! ### Statements in a heap-shaped conjunction

Statement `i` lives at heap node `i + 1`; node `k` is
`S_{k-1} ∧ (node 2k ∧ node 2k+1)` and nodes beyond the last statement are
`True`. Projections cost `O(log i)` and do not depend on the final count, so
lifted statements can be added while proofs are being built. -/

/-- Heap node `k` of the conjunction of `stmts` (node 1 is all of it). -/
partial def heapConj (stmts : Array Expr) (k : Nat := 1) : Expr :=
  if k - 1 ≥ stmts.size then mkConst ``True
  else mkAnd stmts[k - 1]! (mkAnd (heapConj stmts (2 * k)) (heapConj stmts (2 * k + 1)))

/-- A proof of `heapConj stmts k` from a proof of each statement. -/
partial def heapIntro (stmts proofs : Array Expr) (k : Nat := 1) : Expr :=
  if k - 1 ≥ stmts.size then mkConst ``True.intro
  else
    let l := heapConj stmts (2 * k)
    let r := heapConj stmts (2 * k + 1)
    let rest := mkApp4 (mkConst ``And.intro) l r (heapIntro stmts proofs (2 * k))
      (heapIntro stmts proofs (2 * k + 1))
    mkApp4 (mkConst ``And.intro) stmts[k - 1]! (mkAnd l r) proofs[k - 1]! rest

/-- Project statement `i` out of a proof of the heap conjunction. -/
def heapProj (i : Nat) (h : Expr) : Expr := Id.run do
  let mut bits := #[]
  let mut x := i + 1
  while x > 1 do
    bits := bits.push (x % 2)
    x := x / 2
  let mut h := h
  for b in bits.reverse do
    h := Expr.proj ``And 1 h
    h := Expr.proj ``And b h
  return Expr.proj ``And 0 h

/-! ## Replay monad -/

/-- Proves a verification condition (a closed proposition), or fails. -/
abbrev VCProver := Expr → MetaM Expr

/-- A lambda-lifted region: its premises are the logical locals of the path. -/
structure Lifted where
  tpl : Nat
  entry? : Option Nat
  /-- `fun n => ∀ locals, Obs(T) n → concl n`. -/
  stmtFn : Expr
  /-- The path's logical locals (the statement's premises). -/
  locals : Array Expr
  ghosts : Array Expr := #[]
deriving Inhabited

/-- What the replay of one statement's proof works with. -/
structure ReplayCtx where
  plan : Plan
  prove : VCProver
  /-- The fuel of the statement: the variable of the strong induction. -/
  n0 : Expr
  /-- The induction hypothesis: every statement at every smaller fuel. -/
  ih : Expr
  /-- The statement being proved (at fuel `n0`). -/
  concl : Expr
  /-- Entry template of the procedure region, if any. -/
  entry? : Option Nat := none
  /-- Ghost values of the region (the entry observations being summarized). -/
  ghosts : Array Expr := #[]
  /-- The lifted statements of the whole plan (shared by concurrent replays). -/
  lifted : IO.Ref (Array Lifted)
  /-- The lifted statements of this replay, by template. -/
  liftedOf : IO.Ref (Std.HashMap Nat Nat)
  /-- `blaster.explore.liftDepth`. -/
  liftDepth : Nat

abbrev ReplayM := ReaderT ReplayCtx ExM

/-- Run `k` with a new local of type `ty`. -/
def withLocal (name : Name) (ty : Expr) (k : Expr → ReplayM α) : ReplayM α := do
  let fv ← mkFreshFVarId
  modify fun c => {c with lctx := c.lctx.mkLocalDecl fv name ty}
  k (.fvar fv)

def inMeta (k : MetaM α) : ReplayM α := liftM (inCtx k : ExM α)

/-- `fun xs => body` (each of `xs` a local of the replay). -/
def lam (xs : Array Expr) (body : Expr) : ReplayM Expr := do
  let lctx := (← getThe Core).lctx
  for x in xs do
    unless lctx.contains x.fvarId! do
      throwError "explore proof: abstracting a variable outside the context ({x.fvarId!.name})"
  inMeta (mkLambdaFVars xs body)

/-- `∀ xs, body`. -/
def forallE (xs : Array Expr) (body : Expr) : ReplayM Expr := inMeta (mkForallFVars xs body)

/-- Transport an observation across path equalities. Splitting a root changes
the replayed state, while a shared template can still mention the original
root. Such states are propositionally, rather than definitionally, equal. -/
def transportEqualities (proof source target : Expr) (equalities : Array Expr) : MetaM Expr := do
  let mut proof ← mkExpectedTypeHint proof source
  let mut source := source
  let mut target := target
  let mut back : Array (Expr × Expr) := #[]
  for equality in equalities do
    let some (_, left, right) := (← inferType equality).eq? | continue
    let (left, right, equality) ←
      if left.isFVar && !right.containsFVar left.fvarId! then pure (left, right, equality)
      else if right.isFVar && !left.containsFVar right.fvarId! then
        pure (right, left, ← mkEqSymm equality)
      else continue
    if source.containsFVar left.fvarId! then
      let motive ← withLocalDeclD `x (← inferType left) fun x =>
        mkLambdaFVars #[x] (source.replaceFVar left x)
      proof ← mkEqNDRec motive proof equality
      source := source.replaceFVar left right
    if target.containsFVar left.fvarId! then
      let motive ← withLocalDeclD `x (← inferType left) fun x =>
        mkLambdaFVars #[x] (target.replaceFVar left x)
      back := back.push (motive, equality)
      target := target.replaceFVar left right
  unless ← isDefEq source target do
    throwError "explore proof: path equalities do not connect the observation to its target"
  proof ← mkExpectedTypeHint proof target
  for (motive, equality) in back.reverse do
    proof ← mkEqNDRec motive proof (← mkEqSymm equality)
  return proof

/-- `h` at type `ty` (a conversion checked by the kernel). -/
def hint (h ty : Expr) : ReplayM Expr := do
  inMeta (mkExpectedTypeHint h ty)

/-! ## Fuel

`k` is the innermost fuel variable. At a statement's entry `k` is the
induction variable itself; after the first fuel split it is strictly below. -/

/-- The fuel at a point of a replay, and what is known of it. -/
structure Fuel where
  k : Expr
  /-- `k ≤ n0` (absent when `k` is `n0`). -/
  le? : Option Expr := none
  /-- `k < n0`. -/
  lt? : Option Expr := none
  /-- `k + 1 < n0`. -/
  ltSucc? : Option Expr := none
  /-- Inlined templates since the statement's entry. -/
  depth : Nat := 0

/-- A proof that fuel expression `f` is below `n0`. -/
def Fuel.below? (fuel : Fuel) (f : Expr) : Option Expr :=
  if f == fuel.k then fuel.lt?
  else if f == mkApp (mkConst ``Nat.succ) fuel.k then fuel.ltSucc?
  else if f.isAppOfArity ``HAdd.hAdd 6 && f.appFn!.appArg! == fuel.k &&
      (f.appArg!.rawNatLit? == some 1 ||
        (f.appArg!.isAppOfArity ``OfNat.ofNat 3 && f.appArg!.appFn!.appArg!.rawNatLit? == some 1)) then
    fuel.ltSucc?
  else none

/-! ## Replay -/

/-- Close a verification condition over the context and the logical locals. -/
def discharge (locals : Array Local) (target : Expr) : ReplayM Expr := do
  let ctx ← read
  if target.isConstOf ``True then return mkConst ``True.intro
  let lctx := (← getThe Core).lctx
  if let some l := locals.find? fun l => (lctx.find? l.fvar.fvarId!).any (·.type == target) then
    return l.fvar
  let xs := locals.filter (·.logical) |>.map (·.fvar)
  let vc ← forallE (ctx.plan.context ++ xs) target
  if vc.hasFVar || vc.hasMVar then
    let fvs := (collectFVars {} vc).fvarIds
    let names ← inMeta do fvs.toList.take 8 |>.mapM fun id => do
      let t ← try ppExpr (← inferType (.fvar id)) catch _ => pure "?"
      return s!"{(← id.getUserName)} : {(toString t).take 60}"
    let d ← inMeta do return (toString (← ppExpr target)).take 2500
    throwError "explore proof: verification condition is not closed (free: {names}; mvars: {vc.hasMVar})\ntarget: {d}"
  -- conditions are closed: prove them without any ambient hypothesis
  let proof ← liftM (withLCtx {} {} (ctx.prove vc) : MetaM Expr)
  -- A closed metavariable can defer this obligation for batch proving. The
  -- frontend must instantiate every obligation and audit the assembled term
  -- before publishing its theorem.
  if proof.hasFVar then
    throwError "explore proof: verification condition proof is not closed"
  return mkAppN proof (ctx.plan.context ++ xs)

/-- Instantiate logical ancestors omitted from the machine state. For example,
when an edge carries the fields of `some x`, its enclosing value can be supplied
as `some x` itself. Every defining equation is still discharged afterwards.
Existing state bindings remain simultaneous: applying them recursively would
incorrectly unfold a loop binding such as `xs := x :: xs`. -/
def completeCutSubst (c : CutInfo) (σ : Subst) (locals : Array Local) : ReplayM Subst := do
  let ctx ← read
  let bound := Std.HashSet.ofArray <|
    (ctx.plan.context ++ locals.map (·.fvar) ++ ctx.ghosts).filterMap Expr.fvarId?
  let mut σ := σ
  let mut changed := true
  while changed do
    changed := false
    for f in c.facts do
      let some (_, lhs, rhs) := f.eq? | continue
      -- Constructor equations give witnesses first; a generalized expression
      -- also gives a witness once all its arguments are available.
      let candidates := #[(lhs, rhs), (rhs, lhs)]
      for (v, value) in candidates do
        let .fvar id := v | continue
        if σ.contains id || bound.contains id then continue
        let value := Subst.apply σ value
        unless (collectFVars {} value).fvarIds.all bound.contains do continue
        σ := σ.insert id value
        changed := true
  return σ

/-- A proof of `False` from `h : p`, for a closed proposition `p` that is
`False` or that decides to `false` (the rejection of a Boolean-valued machine
observed as `run … = true` is `false = true`); checked by the kernel. -/
def refute (p h : Expr) : MetaM Expr := do
  if p.isConstOf ``False then return h
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let decision ← whnfD (mkApp2 (mkConst ``Decidable.decide) p inst)
  unless decision.isConstOf ``Bool.false do throwError "explore proof: zero fuel does not reject"
  let decided := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.false)
  return mkApp (mkApp3 (mkConst ``of_decide_eq_false) p inst decided) h

/-- Is the reduced expression stuck on the fuel variable? -/
def stuckOnFuel (r k : Expr) : ReplayM Bool := do
  if let some m ← inMeta (matchMatcherApp? r (alsoCasesOn := true)) then
    for d in m.discrs do
      if (← inMeta (whnf d)) == k then return true
  return false

/-- A proof of `∃ h̄, body` from witnesses and a proof of `body[h̄ := w̄]`. -/
def existsIntro (holes witnesses : Array Expr) (body proof : Expr) : MetaM Expr := do
  let n := holes.size
  let mut bodies := Array.replicate (n + 1) body
  for i' in [0:n] do
    let i := n - 1 - i'
    bodies := bodies.set! i (← mkAppM ``Exists #[← mkLambdaFVars #[holes[i]!] bodies[i+1]!])
  let mut prf := proof
  for i' in [0:n] do
    let i := n - 1 - i'
    let outer := holes.extract 0 i
    let ws := witnesses.extract 0 i
    let motive := (← mkLambdaFVars #[holes[i]!] bodies[i+1]!).replaceFVars outer ws
    let ty := (← inferType holes[i]!).replaceFVars outer ws
    let lvl ← getLevel ty
    prf := mkApp4 (mkConst ``Exists.intro [lvl]) ty motive witnesses[i]! prf
  return prf

/-- The IH instance for statement `idx` at fuel `k` (with `lt : k < n0`). -/
def ihAt (idx : Nat) (k lt : Expr) : ReplayM Expr := do
  return heapProj idx (mkApp2 (← read).ih k lt)

/-- `h : ∃ m, m ≤ k ∧ R m` (a region conclusion at `k`) gives `∃ m, m ≤ n0 ∧ R m`. -/
def weakenExit (h : Expr) (hTy : Expr) (lt : Expr) : ReplayM Expr := do
  let ctx ← read
  inMeta do
    let_expr Exists _ p := hTy | throwError "explore proof: expected an exit summary"
    let hle ← mkAppM ``Nat.le_of_lt #[lt]
    let f ← withLocalDeclD `m (mkConst ``Nat) fun m => do
      let pm := p.beta #[m]
      withLocalDeclD `hm pm fun hm => do
        let le' ← mkAppM ``Nat.le_trans #[Expr.proj ``And 0 hm, hle]
        let_expr And _ rest := pm | throwError "explore proof: malformed exit summary"
        let body := mkApp4 (mkConst ``And.intro) (← mkAppM ``LE.le #[m, ctx.n0]) rest le'
          (Expr.proj ``And 1 hm)
        mkLambdaFVars #[m, hm] body
    let q ← withLocalDeclD `m (mkConst ``Nat) fun m => do
      let_expr And _ rest := p.beta #[m] | throwError "explore proof: malformed exit summary"
      mkLambdaFVars #[m] (mkAnd (← mkAppM ``LE.le #[m, ctx.n0]) rest)
    return mkApp5 (mkConst ``Exists.imp [levelOne]) (mkConst ``Nat) p q f h

mutual

/-- Prove the current statement from `hobs : cur`, following node `node`. -/
partial def replay (cur hobs : Expr) (fuel : Fuel) (node : Nat) (locals : Array Local) : ReplayM Expr := do
  let ctx ← read
  let M := (← getThe Core).machine
  -- a procedure exit: this state witnesses the summary
  if let .exit _ := ctx.plan.result.search.nodes[node]! then
    return ← exitWitness cur hobs fuel locals
  -- a machine state: unfold it with its checked equation
  if let some (heq, body) ← inMeta (M.unfoldProof? cur) then
    let hobs' ← inMeta (mkEqMP heq hobs)
    return ← replay body hobs' fuel node locals
  let some r ← inMeta (M.whnf cur) | throwError "explore proof: reduction budget"
  if ← stuckOnFuel r fuel.k then
    return ← splitFuel cur hobs fuel node locals
  match ctx.plan.result.search.nodes[node]! with
  | .accept =>
    unless r.isConstOf ``True do throwError "explore proof: expected acceptance"
    if ctx.entry?.isSome then throwError "explore proof: acceptance inside a procedure"
    discharge locals ctx.plan.goal
  | .reject =>
    unless r.isConstOf ``False do
      let d ← inMeta do return (toString (← ppExpr r)).take 600
      throwError "explore proof: expected rejection, got\n{d}"
    let hr ← hint hobs r
    inMeta (mkFalseElim ctx.concl hr)
  | .leaf _ =>
    if ctx.entry?.isSome then throwError "explore proof: leaf inside a procedure"
    withLocal `leaf r fun h => do
      let body ← discharge (locals.push {fvar := h, logical := true}) ctx.plan.goal
      inMeta (do return mkApp (← mkLambdaFVars #[h] body) (← mkExpectedTypeHint hobs r))
  | .goto _ _ =>
    let some (v, σ) := ctx.plan.graph.targets[node]? | throwError "explore proof: unresolved edge"
    gotoTarget r hobs fuel v σ locals
  | .call _ _ entry _ ret => callSummary r hobs fuel entry ret locals
  | .split .. | .gen .. | .known .. | .cond .. | .knownCond .. | .rewrite .. =>
    if let .rewrite lhs rhs proof next := ctx.plan.result.search.nodes[node]! then
      if lhs.isConst then
        -- an eager producer rewrite of the whole state (`f = List.map g`)
        let hTy ← inMeta do instantiateMVars (← inferType hobs)
        let motive ← withLocal `x (← inMeta (inferType lhs)) fun x => do lam #[x] (replaceConstTerm hTy lhs x)
        let hobs' ← inMeta (mkEqNDRec motive hobs proof)
        return ← replay (replaceConstTerm cur lhs rhs) hobs' fuel next locals
    -- mirror the exploration: rewrite inside the rebuilt stuck expression
    let why ← liftM (findStuck r : ExM Stuck)
    let (e, atom) ← match why with
      | .data a m => pure (m.beta #[a], a)
      | .cond i _ m => pure (m.beta #[i], i)
      | .rewrite l _ _ f m => pure (m.beta #[f], l)
      | .other _ w => throwError "explore proof: reduction is not stuck on data ({w})"
    let hobsE ← hint hobs e
    match ctx.plan.result.search.nodes[node]! with
    | .split a alts =>
      unless a == atom do throwError "explore proof: split atom mismatch"
      splitAtom e hobsE fuel a alts locals
    | .gen x g fresh next =>
      unless x == atom do throwError "explore proof: generalization mismatch"
      if fresh && !(locals.any (·.fvar == g)) then genAtom e hobsE fuel x g next locals
      else reuseGen e hobsE fuel x g next locals
    | .known g v next => knownValue e hobsE fuel g v next locals
    | .cond i prop hT hF t f =>
      unless i == atom do throwError "explore proof: decision mismatch"
      if locals.any (·.fvar == hT) then knownDecision e hobsE fuel i prop true hT t locals
      else if locals.any (·.fvar == hF) then knownDecision e hobsE fuel i prop false hF f locals
      else decide e hobsE fuel i prop hT hF t f locals
    | .knownCond i prop pos h next => knownDecision e hobsE fuel i prop pos h next locals
    | .rewrite lhs rhs proof next =>
      unless lhs == atom do throwError "explore proof: rewrite mismatch"
      let e' := replaceTerm e lhs rhs
      let motive ← withLocal `x (← inMeta (inferType lhs)) fun x => do lam #[x] (replaceTerm e lhs x)
      let hobs' ← inMeta (mkEqNDRec motive hobsE proof)
      replay e' hobs' fuel next locals
    | _ => unreachable!
  | .exit _ => throwError "explore proof: unexpected procedure exit"
  | .abort why => throwError "explore proof: exploration was incomplete ({why})"
  | .unreachable _ =>
    -- the path's facts are contradictory: a verification condition `… → False`
    let hf ← discharge locals (mkConst ``False)
    inMeta (mkFalseElim ctx.concl hf)

/-- The fuel `k` is needed (the reduction of `cur` is stuck on it): case
analysis of `k`. At `0` the state is refuted (by reduction, or else by a
verification condition); at `k' + 1` the replay of `node` continues, with
`k' < n0`. -/
partial def splitFuel (cur hobs : Expr) (fuel : Fuel) (node : Nat) (locals : Array Local) :
    ReplayM Expr := do
  let ctx ← read
  let goal := ctx.concl
  let k := fuel.k
  let nat := mkConst ``Nat
  let motive ← withLocal `x nat fun x => do
    lam #[x] (← inMeta (do mkArrow (← mkEq k x) (← mkArrow (cur.replaceFVar k x) goal)))
  let zero := mkNatLit 0
  let zeroCase ← withLocal `h (← inMeta (mkEq k zero)) fun h => do
    withLocal `hz (cur.replaceFVar k zero) fun hz => do
      let some z ← inMeta (whnfB (cur.replaceFVar k zero)) | throwError "explore proof: budget"
      -- reduction decides the zero-fuel state of most machines; one whose
      -- match inspects data before the fuel leaves a verification condition
      let contradiction ← try inMeta do refute z (← mkExpectedTypeHint hz z)
        catch _ => discharge (locals.push {fvar := hz, logical := true}) (mkConst ``False)
      lam #[h, hz] (← inMeta (mkFalseElim goal contradiction))
  let succCase ← withLocal `k nat fun k' => do
    let succ := mkApp (mkConst ``Nat.succ) k'
    withLocal `h (← inMeta (mkEq k succ)) fun h => do
      withLocal `hs (cur.replaceFVar k succ) fun hs => do
        let (lt, le, ltSucc) ← inMeta do
          let motive ← withLocalDeclD `y nat fun y => do mkLambdaFVars #[y] (← mkAppM ``LT.lt #[k', y])
          let ltk ← mkEqNDRec motive (← mkAppM ``Nat.lt_succ_self #[k']) (← mkEqSymm h)
          let lt ← match fuel.le? with
            | none => pure ltk
            | some le => mkAppM ``Nat.lt_of_lt_of_le #[ltk, le]
          let le ← mkAppM ``Nat.le_of_lt #[lt]
          let ltSucc ← match fuel.lt? with
            | none => pure none
            | some ltk0 =>
              let motive ← withLocalDeclD `y nat fun y => do
                mkLambdaFVars #[y] (← mkAppM ``LT.lt #[y, ctx.n0])
              pure (some (← mkEqNDRec motive ltk0 h))
          pure (lt, le, ltSucc)
        let body ← replay (cur.replaceFVar k succ) hs
          {k := k', le? := some le, lt? := some lt, ltSucc? := ltSucc, depth := fuel.depth} node locals
        lam #[k', h, hs] body
  let lvl ← inMeta (getLevel goal)
  let casesOn := mkApp4 (mkConst ``Nat.casesOn [lvl]) motive k zeroCase succCase
  inMeta (do return mkApp2 casesOn (← mkEqRefl k) hobs)

/-- Split variable `atom` (all occurrences in the reduced expression), with an equation. -/
partial def splitAtom (r hobs : Expr) (fuel : Fuel) (atom : Expr) (alts : Array (Name × Array Expr × Nat))
    (locals : Array Local) : ReplayM Expr := do
  let ctx ← read
  let goal := ctx.concl
  let ty ← inMeta (do whnf (← inferType atom))
  let .const tn ls := ty.getAppFn | throwError "explore proof: split on non-inductive"
  let info ← inMeta (getConstInfoInduct tn)
  let params := ty.getAppArgs.extract 0 info.numParams
  let motive ← withLocal `x ty fun x => do
    lam #[x] (← inMeta (do mkArrow (← mkEq atom x) (← mkArrow (r.replaceFVar atom x) goal)))
  let mut minors := #[]
  for (c, fields, next) in alts do
    let app := mkAppN (mkAppN (mkConst c ls) params) fields
    let minor ← withLocal `h (← inMeta (mkEq atom app)) fun h => do
      withLocal `hr (r.replaceFVar atom app) fun hr => do
        let locals := (locals ++ fields.map (fun f => ({fvar := f, logical := true} : Local))).push
          {fvar := h, logical := true}
        let body ← replay (r.replaceFVar atom app) hr fuel next locals
        lam (fields ++ #[h, hr]) body
    minors := minors.push minor
  let lvl ← inMeta (getLevel goal)
  let casesOn := mkAppN (mkConst (tn ++ `casesOn) (lvl :: ls)) (params.push motive |>.push atom)
  let casesOn := mkAppN casesOn minors
  inMeta (do return mkApp2 casesOn (← mkEqRefl atom) hobs)

/-- Generalize subterm `e` as `g` (all occurrences), with `e = g`. -/
partial def genAtom (r hobs : Expr) (fuel : Fuel) (e g : Expr) (next : Nat) (locals : Array Local) :
    ReplayM Expr := do
  let r' := replaceTerm r e g
  withLocal `hg (← inMeta (mkEq e g)) fun hg => do
    withLocal `hr r' fun hr => do
      let locals := locals ++ #[{fvar := g, logical := true}, {fvar := hg, logical := true}]
      let body ← replay r' hr fuel next locals
      let f ← lam #[g, hg, hr] body
      inMeta (do return mkApp3 f e (← mkEqRefl e) hobs)

/-- A subterm generalized earlier on this path: rewrite with the existing equation. -/
partial def reuseGen (r hobs : Expr) (fuel : Fuel) (e g : Expr) (next : Nat) (locals : Array Local) :
    ReplayM Expr := do
  let lctx := (← getThe Core).lctx
  let heq? := locals.findSome? fun l =>
    match (lctx.find? l.fvar.fvarId!).bind (·.type.eq?) with
    | some (_, a, b) => if a == e && b == g then some l.fvar else none
    | none => none
  let some heq := heq? | throwError "explore proof: reused generalization without an equation"
  let r' := replaceTerm r e g
  let motive ← withLocal `x (← inMeta (inferType e)) fun x => do lam #[x] (replaceTerm r e x)
  let hr' ← inMeta (mkEqNDRec motive hobs heq)
  match (← read).plan.result.search.nodes[next]! with
  | .known g' v next' => knownValue r' hr' fuel g' v next' locals
  | _ => replay r' hr' fuel next locals

/-- A generalized variable whose constructor value is already known on this path. -/
partial def knownValue (r hobs : Expr) (fuel : Fuel) (g v : Expr) (next : Nat) (locals : Array Local) :
    ReplayM Expr := do
  let lctx := (← getThe Core).lctx
  let heq? := locals.findSome? fun l =>
    match (lctx.find? l.fvar.fvarId!).bind (·.type.eq?) with
    | some (_, a, b) => if a == g && b == v then some l.fvar else none
    | none => none
  let some heq := heq? | throwError "explore proof: known value without an equation"
  let motive ← withLocal `x (← inMeta (inferType g)) fun x => do lam #[x] (r.replaceFVar g x)
  let hr' ← inMeta (mkEqNDRec motive hobs heq)
  replay (r.replaceFVar g v) hr' fuel next locals

/-- Case analysis of the decision `inst : Decidable prop`: the replay of `t`
under `hT : prop`, of `f` under `hF : ¬prop`. -/
partial def decide (r hobs : Expr) (fuel : Fuel) (inst prop hT hF : Expr) (t f : Nat)
    (locals : Array Local) : ReplayM Expr := do
  let ctx ← read
  let goal := ctx.concl
  let decTy ← inMeta (mkAppM ``Decidable #[prop])
  let motive ← withLocal `i decTy fun i => do
    lam #[i] (← inMeta (mkArrow (replaceTerm r inst i) goal))
  let instF ← inMeta (mkAppOptM ``Decidable.isFalse #[prop, hF])
  let instT ← inMeta (mkAppOptM ``Decidable.isTrue #[prop, hT])
  let caseF ← withLocal `hr (replaceTerm r inst instF) fun hr => do
    let body ← replay (replaceTerm r inst instF) hr fuel f (locals.push {fvar := hF, logical := true})
    lam #[hF, hr] body
  let caseT ← withLocal `hr (replaceTerm r inst instT) fun hr => do
    let body ← replay (replaceTerm r inst instT) hr fuel t (locals.push {fvar := hT, logical := true})
    lam #[hT, hr] body
  let lvl ← inMeta (getLevel goal)
  let casesOn := mkApp5 (mkConst ``Decidable.casesOn [lvl]) prop motive inst caseF caseT
  inMeta (do return mkApp casesOn hobs)

/-- A decision taken earlier on the path (`h : prop`, or `h : ¬prop`): the
instance is replaced by the one `h` gives, which it equals. -/
partial def knownDecision (r hobs : Expr) (fuel : Fuel) (inst prop : Expr) (pos : Bool) (h : Expr)
    (next : Nat) (locals : Array Local) : ReplayM Expr := do
  let inst' ← inMeta do
    if pos then mkAppOptM ``Decidable.isTrue #[prop, h] else mkAppOptM ``Decidable.isFalse #[prop, h]
  let decTy ← inMeta (mkAppM ``Decidable #[prop])
  let motive ← withLocal `i decTy fun i => do lam #[i] (replaceTerm r inst i)
  let heq ← inMeta (mkAppOptM ``Subsingleton.elim #[decTy, none, inst, inst'])
  let hr' ← inMeta (mkEqNDRec motive hobs heq)
  replay (replaceTerm r inst inst') hr' fuel next locals

/-- An exit: `cur = Obs(S) k` with `S` an instance of the region's exit shape. -/
partial def exitWitness (cur hobs : Expr) (fuel : Fuel) (locals : Array Local) : ReplayM Expr := do
  let ctx ← read
  let plan := ctx.plan
  let some e := ctx.entry? | throwError "explore proof: exit outside a procedure"
  let shape := plan.graph.shapes[e]!
  let holes := plan.holes.getD e #[]
  let gv := plan.ghostVars.getD e #[]
  let post := (plan.posts.getD e (mkConst ``True)).replaceFVars gv (if ctx.ghosts.size == gv.size then ctx.ghosts else gv)
  let state := cur.appFn!
  let k := cur.appArg!
  let some σ ← liftM (instanceOf? shape state : ExM _)
    | throwError "explore proof: exit state does not match the shape"
  let ws := holes.map (Subst.apply σ)
  let postProof ← discharge locals (Subst.apply σ post)
  let obs := mkApp (Subst.apply σ shape) k
  let hobs' ← hint hobs obs
  inMeta do
    let inner ← mkAppM ``And.intro #[postProof, hobs']
    let body := mkAnd post (mkApp shape k)
    let hex ← existsIntro holes ws body inner
    let hle ← match fuel.le? with
      | some le => pure le
      | none => mkAppM ``Nat.le_refl #[k]
    let_expr Exists _ p := ctx.concl | throwError "explore proof: expected an exit conclusion"
    return mkApp4 (mkConst ``Exists.intro [levelOne]) (mkConst ``Nat) p k (← mkAppM ``And.intro #[hle, hex])

/-- A call: apply the callee's summary, then continue at the return state. -/
partial def callSummary (r hobs : Expr) (fuel : Fuel) (entry : Nat) (ret? : Option Nat)
    (locals : Array Local) : ReplayM Expr := do
  let ctx ← read
  let plan := ctx.plan
  let some ret := ret? | throwError "explore proof: call without a return point"
  let k' := r.appArg!
  let state := r.appFn!
  let some ce := plan.cutOf[entry]? | throwError "explore proof: callee entry is not a cut point"
  let c := plan.cuts[ce]!
  let tplE := plan.result.search.tpls[entry]!
  let normalized ← liftM (normState state : ExM _)
  let some σ ← liftM (instanceOf? tplE.body normalized : ExM _)
    | let (call, entryState) ← inMeta do return (← ppExpr normalized, ← ppExpr tplE.body)
      throwError "explore proof: call does not match its entry\ncall:{indentD call}\nentry:{indentD entryState}"
  let σ ← completeCutSubst c σ locals
  let some lt := fuel.below? k' | throwError "explore proof: call without progress"
  let args := c.vars.map (Subst.apply σ)
  let factProofs ← c.facts.mapM fun f => discharge locals (Subst.apply σ f)
  let invProof ← discharge locals (Subst.apply σ c.inv)
  let hobs' ← hint hobs (mkApp (Subst.apply σ tplE.body) k')
  let H := mkAppN (← ihAt ce k' lt) (args ++ factProofs ++ #[invProof, hobs'])
  let calleeGhosts := (plan.ghostVals.getD entry #[]).map (Subst.apply σ)
  let hTy := Subst.apply σ (← liftM (regionConcl plan (some entry) k' (plan.ghostVals.getD entry #[]) : ExM _))
  -- the recorded return state fixes the names of the returned values
  let shape := plan.graph.shapes[entry]!
  let holes := plan.holes.getD entry #[]
  let shapeσ := Subst.apply σ shape
  let retState := match plan.result.search.nodes[ret]! with
    | .goto s _ => s
    | .call s .. => s
    | _ => shapeσ
  let some τ ← liftM (instanceOf? shapeσ retState : ExM _)
    | throwError "explore proof: return state does not match the shape"
  let rets ← holes.mapM fun h => do
    match τ[h.fvarId!]? with
    | some x => if x.isFVar then pure x else throwError "explore proof: return value is not a variable"
    | none => throwError "explore proof: return value is not a variable"
  let post := (plan.posts.getD entry (mkConst ``True)).replaceFVars (plan.ghostVars.getD entry #[]) calleeGhosts
  let_expr Exists _ p := hTy | throwError "explore proof: expected a callee summary"
  let concl := ctx.concl
  let body ← withLocal `m (mkConst ``Nat) fun m => do
    let pm := p.beta #[m]
    withLocal `hm pm fun hm => do
      let lt' ← inMeta (do mkAppM ``Nat.lt_of_le_of_lt #[Expr.proj ``And 0 hm, lt])
      let le' ← inMeta (mkAppM ``Nat.le_of_lt #[lt'])
      let fuel' : Fuel := {k := m, le? := some le', lt? := some lt', depth := fuel.depth}
      let_expr And _ restTy := pm | throwError "explore proof: malformed summary"
      let inner ← elimHoles (Expr.proj ``And 1 hm) restTy rets 0 fun hk hkTy => do
        let_expr And _ _ := hkTy | throwError "explore proof: malformed summary body"
        let hpost := Expr.proj ``And 0 hk
        let hobsRet := Expr.proj ``And 1 hk
        withLocal `post (post.replaceFVars holes rets) fun hp => do
          let cur := mkApp retState m
          let hobsRet' ← hint hobsRet cur
          let locals' := (locals ++ rets.map ({fvar := ·, logical := true} : Expr → Local)).push
            {fvar := hp, logical := true}
          let cont ← match plan.result.search.nodes[ret]! with
            | .goto .. =>
              let some (v, σ') := plan.graph.targets[ret]? | throwError "explore proof: unresolved return"
              gotoTarget cur hobsRet' fuel' v σ' locals'
            | .call _ _ entry' _ ret' => callSummary cur hobsRet' fuel' entry' ret' locals'
            | _ => throwError "explore proof: unexpected return node"
          inMeta (do return mkApp (← mkLambdaFVars #[hp] cont) hpost)
      lam #[m, hm] inner
  return mkApp (mkApp4 (mkConst ``Exists.elim [levelOne]) (mkConst ``Nat) p concl H) body

/-- Eliminate `∃ h_i …, body` binding the recorded return variables. -/
partial def elimHoles (h hTy : Expr) (rets : Array Expr) (i : Nat) (k : Expr → Expr → ReplayM Expr) :
    ReplayM Expr := do
  if i ≥ rets.size then return ← k h hTy
  let ctx ← read
  let_expr Exists α p := hTy | throwError "explore proof: expected a returned value"
  let r := rets[i]!
  let pr := p.beta #[r]
  let body ← withLocal `H pr fun hr => do
    let inner ← elimHoles hr pr rets (i + 1) k
    lam #[r, hr] inner
  let lvl ← inMeta (getLevel α)
  return mkApp5 (mkConst ``Exists.elim [lvl]) α p ctx.concl h body

/-- Arrival at template `v` (the reduced expression is `P args k'`). -/
partial def gotoTarget (r hobs : Expr) (fuel : Fuel) (v : Nat) (σ : Subst) (locals : Array Local) :
    ReplayM Expr := do
  let ctx ← read
  let plan := ctx.plan
  unless r.isApp do throwError "explore proof: edge without a state"
  let k' := r.appArg!
  let tpl := plan.result.search.tpls[v]!
  let cur := mkApp (Subst.apply σ tpl.body) k'
  let hobs' ← if ← inMeta (isDefEq r cur) then hint hobs cur else do
    let core ← getThe Core
    let equalities := locals.filterMap fun l => do
      let (_, left, right) ← (core.lctx.find? l.fvar.fvarId!).bind (·.type.eq?)
      let rootish := fun e => e.isFVar && core.vars[e.fvarId!]?.any (·.rootish)
      if rootish left || rootish right then some l.fvar else none
    inMeta (transportEqualities hobs r cur equalities)
  let lifted? := (← ctx.liftedOf.get)[v]?
  match plan.cutOf[v]? with
  | some ci =>
    let c := plan.cuts[ci]!
    let σ ← completeCutSubst c σ locals
    let some lt := fuel.below? k' | do
      let d ← inMeta do return s!"k'={← ppExpr k'} k={← ppExpr fuel.k}"
      throwError "explore proof: edge into a cut point without progress ({d})"
    unless c.inner || c.entry?.isNone do
      throwError "explore proof: an edge re-enters a procedure entry without a call"
    let gargs := if c.inner then ctx.ghosts else #[]
    let args := c.vars.map (Subst.apply σ)
    let inv := if c.inner then c.inv.replaceFVars (plan.ghostVars.getD c.entry?.get! #[]) ctx.ghosts else c.inv
    let factProofs ← c.facts.mapM fun f => do
      try discharge locals (Subst.apply σ f)
      catch ex =>
        throwError "explore proof: edge into cut {ci} (template {v}) failed:\n{ex.toMessageData}"
    let invProof ← discharge locals (Subst.apply σ inv)
    let h := mkAppN (← ihAt ci k' lt) (gargs ++ args ++ factProofs ++ #[invProof, hobs'])
    match ctx.entry? with
    | none => return h
    | some _ =>
      unless c.entry? == ctx.entry? do throwError "explore proof: edge leaves its procedure"
      weakenExit h (← liftM (regionConcl plan c.entry? k' ctx.ghosts : ExM _)) lt
  | none =>
    unless isIdentity σ do throwError "explore proof: inlined template reached through an instance"
    let some node := tpl.node? | throwError "explore proof: template without transition"
    -- a template re-arrived as a procedure call records the call at its own
    -- state (`Restart.reArrive`): the arriving state is the call
    if let .call s _ entry _ ret := plan.result.search.nodes[node]! then
      if s == tpl.body then return ← callSummary cur hobs' fuel entry ret locals
    if fuel.depth < ctx.liftDepth && lifted?.isNone then
      return ← replay cur hobs' {fuel with depth := fuel.depth + 1} node locals
    -- lambda-lift: continue in a separate statement over the logical locals
    let some lt := fuel.below? k' | throwError "explore proof: lifted edge without progress"
    let xs := locals.filter (·.logical) |>.map (·.fvar)
    let idx ← match lifted? with
      | some i => pure i
      | none => do
        let n ← mkFreshFVarId
        modify fun cc => {cc with lctx := cc.lctx.mkLocalDecl n `n (mkConst ``Nat)}
        let concl ← liftM (regionConcl plan ctx.entry? (.fvar n) ctx.ghosts : ExM _)
        let stmtFn ← inMeta do
          mkLambdaFVars #[.fvar n] (← mkForallFVars xs (← mkArrow (mkApp tpl.body (.fvar n)) concl))
        let lifted := {tpl := v, entry? := ctx.entry?, stmtFn, locals := xs, ghosts := ctx.ghosts}
        let i ← ctx.lifted.modifyGet fun all => (plan.cuts.size + all.size, all.push lifted)
        ctx.liftedOf.modify (·.insert v i)
        pure i
    let h := mkAppN (← ihAt idx k' lt) (xs.push hobs')
    match ctx.entry? with
    | none => return h
    | some _ => weakenExit h (← liftM (regionConcl plan ctx.entry? k' ctx.ghosts : ExM _)) lt

end

/-! ## Assembly -/

/-- The defining fact of an exploration variable: `atom = C fields` for a split
field, `e = g` for a generalized subterm. -/
def definingFact? (v : FVarId) : ExM (Option Expr) := do
  let some info := (← get).vars[v]? | return none
  match info.origin with
  | .field atom c _ =>
    let some fields := (← get).splitVars[(atom.fvarId!, c)]? | return none
    let app ← inCtx do
      let ty ← whnf (← inferType atom)
      let .const tn ls := ty.getAppFn | throwError "explore: split on non-inductive"
      let ind ← getConstInfoInduct tn
      pure (mkAppN (mkAppN (mkConst c ls) (ty.getAppArgs.extract 0 ind.numParams)) fields)
    return some (← inCtx (mkEq atom app))
  | .gen e => return some (← inCtx (mkEq e (.fvar v)))
  | _ => return none

/-- Cut information: the template's non-root variables, closed under the
defining facts of its rootish variables (which hold whenever it is reached),
and the given invariant. -/
def mkCutInfo (r : Result) (tpl : Nat) (inv : Expr) (anchorTypes : Array Expr := #[])
    (varying : Std.HashSet FVarId := {}) :
    ExM CutInfo := do
  let t := r.search.tpls[tpl]!
  let vars := (← get).vars
  let nonRoot := fun (id : FVarId) => match vars[id]? with
    | some {origin := .root, ..} => false
    | _ => true
  -- split chains up to an element of an anchor type (an element some hypothesis
  -- quantifies over) are kept by default; replay discharges them
  let mut todo := (collectFVars {} (mkApp2 (mkConst ``Prod.mk) t.body inv)).fvarIds.filter nonRoot
  let mut seen : Std.HashSet FVarId := {}
  let mut facts : Array Expr := #[]
  while !todo.isEmpty do
    let id := todo.back!
    todo := todo.pop
    if seen.contains id then continue
    seen := seen.insert id
    let isGen := match vars[id]? with
      | some {origin := .gen _, ..} => true
      | _ => false
    -- a field of (a field of …) an element of an anchor type: keep the split
    -- chain up to that element, so what selected it stays known
    let anchored ← do
      if anchorTypes.isEmpty then pure false else
      let mut cur := id
      let mut found ← inCtx do
        let lctx ← getLCtx
        match lctx.find? id with
        | some d => anchorTypes.anyM (isDefEq d.type ·)
        | none => pure false
      for _ in [0:12] do
        if found then break
        let some {origin := .field atom _ _, ..} := vars[cur]? | break
        let .fvar a := atom | break
        let aty ← inCtx (inferType atom)
        if ← inCtx (anchorTypes.anyM (isDefEq aty ·)) then found := true; break
        cur := a
      pure found
    -- a field of (a field of …) a generalized subterm: its value is read off
    -- that subterm, so the split chain and the subterm's defining fact stay
    let fromGen := Id.run do
      let mut cur := id
      for _ in [0:8] do
        match vars[cur]? with
        | some {origin := .field (.fvar a) _ _, ..} =>
          match vars[a]? with
          | some {origin := .gen _, ..} => return true
          | _ => cur := a
        | _ => return false
      return false
    unless vars[id]?.any (·.rootish) || isGen || anchored || fromGen do continue
    if let some f ← definingFact? id then
      -- A join can use a previously split/computed value as a pattern variable.
      -- Its original defining equation does not describe other instances of
      -- that pattern. Keep such relationships only as inferred invariants,
      -- whose preservation is checked on every incoming edge.
      if (collectFVars {} f).fvarIds.any varying.contains then continue
      facts := facts.push f
      for id' in (collectFVars {} f).fvarIds do
        if nonRoot id' && !seen.contains id' then todo := todo.push id'
  let lctx := (← get).lctx
  for id in seen.toArray do
    unless lctx.contains id do
      throwError "explore: cut template {tpl} mentions an unknown variable {id.name} (facts {facts.size})"
  let sorted := seen.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index
  -- facts in dependency order (by the index of their newest variable)
  let key := fun (f : Expr) => ((collectFVars {} f).fvarIds.map fun id => (lctx.get! id).index).foldl max 0
  let ordered := facts.qsort fun a b => key a < key b
  return {tpl, entry? := t.entry?, vars := sorted.map (.fvar ·), facts := ordered, inv}

/-- Build a plan with the given invariants (`invOf`) and procedure
postconditions (`postOf`). Its graph is `graph?` when given (`planGraph r` does
not depend on the invariants). -/
def mkPlan (r : Result) (goal : Expr) (context : Array Expr)
    (invOf : Nat → ExM Expr) (postOf : Nat → ExM Expr := fun _ => pure (mkConst ``True))
    (ghostsOf : Nat → ExM (Array Expr × Array Expr) := fun _ => pure (#[], #[]))
    (anchorTypes : Array Expr := #[]) (graph? : Option Graph := none) : ExM Plan := do
  let graph ← match graph? with
    | some graph => pure graph
    | none => planGraph r
  let mut cuts := #[]
  let mut cutOf := {}
  -- Canonical exploration names are reused downstream of a join. Once a name
  -- denotes different state values, its original provenance cannot be assumed
  -- again at a later cut merely because that edge has an identity binding.
  let mut varying : Std.HashSet FVarId := {}
  for (_, (_, σ)) in graph.targets.toList do
    for (v, value) in σ.toList do
      if value != .fvar v then varying := varying.insert v
  for t in graph.cuts do
    cutOf := cutOf.insert t cuts.size
    cuts := cuts.push (← mkCutInfo r t (← invOf t) anchorTypes varying)
  let mut holes := {}
  let mut posts := {}
  let mut ghostVars := {}
  let mut ghostVals := {}
  for (e, shape) in graph.shapes.toList do
    let kappa? := r.search.tpls[e]!.proc?.map fun pid => r.search.procs[pid]!.kappa
    holes := holes.insert e (← shapeHoles shape kappa?)
    posts := posts.insert e (← postOf e)
    let (gvars, gvals) ← ghostsOf e
    ghostVars := ghostVars.insert e gvars
    ghostVals := ghostVals.insert e gvals
  -- Inner invariants mention the procedure's ghost parameters. They already
  -- have dedicated binders in `cutGhosts`, so they must not also be ordinary
  -- state parameters. In particular, an edge from the entry supplies their
  -- actual entry observations, not the unbound canonical ghost names.
  cuts := cuts.map fun c =>
    if c.inner then
      let ghosts := ghostVars.getD c.entry?.get! #[]
      {c with vars := c.vars.filter (!ghosts.contains ·)}
    else c
  return {result := r, graph, goal, context, cuts, cutOf, holes, posts, ghostVars, ghostVals}

/-- What the proof of a plan is assembled from: the statements at fuel `n0`
and their proofs, which may use the induction hypothesis `ih : ∀ m < n0, …`
(both local variables); the fuel `N` of the run; and the statement the goal is
proved from, with its arguments. The proof is statement `root` of
`Nat.strongRecOn N (fun n0 ih => ⟨proof₁, …⟩)` applied to `rootArgs`. -/
structure Parts where
  statements : Array Expr
  proofs : Array Expr
  n0 : Expr
  ih : Expr
  fuel : Expr
  root : Nat
  rootArgs : Array Expr

/-- A replayed statement (or plan): its proof, with its metavariables
instantiated except the holes of its conditions; its conditions with the terms
the prover gave them, in the order of the statements; the free variables of
the proof; and whether it mentions `sorry`. -/
structure Replayed where
  proof : Expr
  conditions : Array (Expr × Expr)
  freeVars : Array FVarId
  hasSorry : Bool
  /-- The number of statements (one per cut point, then the lifted ones). -/
  statements : Nat := 1
  /-- How a plan's proof is assembled. -/
  parts? : Option Parts := none

/-- `into` with the local declarations `other` added after its first `start`
(those it shares with `into`), in their order. -/
private def mergeLocals (into other : LocalContext) (start : Nat) : LocalContext :=
  other.foldl (start := start) (init := into) fun acc d =>
    match d with
    | .cdecl _ fvarId userName type bi kind => acc.mkLocalDecl fvarId userName type bi kind
    | .ldecl _ fvarId userName type value nondep kind =>
      acc.mkLetDecl fvarId userName type value nondep kind

/-- Prove `goal` from `hobs : Obs(initial) N` along a plan: the proof, and the
verification conditions with the terms `proveVC` gave them, in the order of
the statements. The statements are replayed in parallel (`jobs` at a time),
each from the state after the common setup: the cut points' first, then the
lifted ones, in waves (a statement's replay can lift further ones). Each
replay instantiates and shares (`ShareCommon`) its own proof: the kernel checks
the assembled term faster when its common subterms are shared, and the
abstractions that assemble it keep that sharing. -/
def provePlan (plan : Plan) (hobs N : Expr) (proveVC : VCProver) : ExM Replayed := do
  let r := plan.result
  let cuts := plan.cuts
  -- the replay mirrors the exploration's rewrites: those of the equations of
  -- the context it starts from, not of the many it adds
  let assumptions ← inCtx contextEquations
  modify fun c => {c with assumptions? := some assumptions}
  let nat := mkConst ``Nat
  let n0fv ← mkFreshFVarId
  modify fun c => {c with lctx := c.lctx.mkLocalDecl n0fv `n nat}
  let n0 := Expr.fvar n0fv
  -- the IH's type is fixed once every (lifted) statement is known
  let ihfv ← mkFreshFVarId
  modify fun c => {c with lctx := c.lctx.mkLocalDecl ihfv `ih (mkConst ``True)}
  let ih := Expr.fvar ihfv
  let lifted ← IO.mkRef (#[] : Array Lifted)
  let liftDepth := blaster.explore.liftDepth.get (← getOptions)
  let jobs ← jobCount
  -- a replay context whose prover also records the conditions it is given
  let mkCtx (concl : Expr) (entry? : Option Nat) (ghosts : Array Expr := #[]) :
      IO (ReplayCtx × IO.Ref (Array (Expr × Expr))) := do
    let vcs ← IO.mkRef #[]
    let prove : VCProver := fun vc => do
      let e ← proveVC vc
      vcs.modify (·.push (vc, e))
      return e
    let liftedOf ← IO.mkRef {}
    return ({plan, prove, n0, ih, concl, entry?, ghosts, lifted, liftedOf, liftDepth}, vcs)
  -- a replayed statement's proof: closed over its premises, its metavariables
  -- instantiated (they are this thread's), shared; and its conditions
  let finish (premises : Array Expr) (body : Expr) (vcs : IO.Ref (Array (Expr × Expr))) :
      ExM Replayed := do
    let proof ← instantiateMVars (← inCtx (mkLambdaFVars premises body))
    return {proof := ShareCommon.shareCommon' proof, conditions := ← vcs.get
            freeVars := (collectFVars {} proof).fvarIds, hasSorry := proof.hasSorry}
  let cutProof (i : Nat) : ExM Replayed := do
    let c := cuts[i]!
    let tpl := r.search.tpls[c.tpl]!
    let some node := tpl.node? | throwError "explore proof: cut without transition"
    let (gbinders, ghosts) := cutGhosts plan c
    let concl ← regionConcl plan c.entry? n0 ghosts
    let factHyps ← c.facts.mapM fun f => do
      let fv ← mkFreshFVarId
      modify fun cc => {cc with lctx := cc.lctx.mkLocalDecl fv `fact f}
      pure (Expr.fvar fv)
    let invfv ← mkFreshFVarId
    modify fun cc => {cc with lctx := cc.lctx.mkLocalDecl invfv `inv c.inv}
    let obsfv ← mkFreshFVarId
    let obs := mkApp tpl.body n0
    modify fun cc => {cc with lctx := cc.lctx.mkLocalDecl obsfv `hobs obs}
    let locals := (gbinders ++ c.vars ++ factHyps).map (fun f => ({fvar := f, logical := true} : Local)) |>.push
      {fvar := .fvar invfv, logical := true}
    let (ctx, vcs) ← mkCtx concl c.entry? ghosts
    let body ← try
      (replay obs (.fvar obsfv) {k := n0} node locals).run ctx
    catch ex =>
      throwError "explore proof: while replaying cut {i} (template {c.tpl}):\n{ex.toMessageData}"
    if (body.find? (·.isConstOf `_inhabitedExprDummy)).isSome then
      throwError "explore proof: placeholder in the proof of cut {i} (template {c.tpl}, entry {c.entry?})"
    finish (gbinders ++ c.vars ++ factHyps ++ #[.fvar invfv, .fvar obsfv]) body vcs
  let liftedProof (L : Lifted) : ExM Replayed := do
    let concl ← regionConcl plan L.entry? n0 L.ghosts
    let tpl := r.search.tpls[L.tpl]!
    let some node := tpl.node? | throwError "explore proof: lifted template without transition"
    -- the premises are the recorded locals themselves (the recorded trees
    -- refer to them); only the machine-state premise is new
    let obsfv ← mkFreshFVarId
    modify fun cc => {cc with lctx := cc.lctx.mkLocalDecl obsfv `hobs (mkApp tpl.body n0)}
    let locals := L.locals.map fun x => ({fvar := x, logical := true} : Local)
    let (ctx, vcs) ← mkCtx concl L.entry? L.ghosts
    let body ← (replay (mkApp tpl.body n0) (.fvar obsfv) {k := n0} node locals).run ctx
    if (body.find? (·.isConstOf `_inhabitedExprDummy)).isSome then
      throwError "explore proof: placeholder in lifted statement (template {L.tpl}, entry {L.entry?})"
    finish (L.locals.push (.fvar obsfv)) body vcs
  -- Replay statements on `jobs` threads, each from the current state; then
  -- keep the locals they added (the lifted statements they found refer to
  -- them) and declare their conditions' metavariables (created in their
  -- threads). A replay declares no constant: its proofs use the machine's
  -- equations and the exploration's terms, all declared before.
  let replayAll {α : Type} (xs : Array α) (prove : α → ExM Replayed) :
      ExM (Array Replayed) := do
    let core ← get
    -- (every replay extends this local context: its own locals come after)
    let shared := core.lctx.decls.size
    let results ← parallelMap jobs xs fun x => do
      let (result, core') ← (prove x).run core
      return (result, core'.lctx)
    for (statement, lctx) in results do
      modify fun c => {c with lctx := mergeLocals c.lctx lctx shared}
      for (vc, e) in statement.conditions do
        if let .mvar id := e then
          if ((← getMCtx).findDecl? id).isNone then
            modifyMCtx fun mctx => mctx.addExprMVarDecl id .anonymous {} {} vc
    return results.map (·.1)
  -- the statements of the cut points, then the lifted ones (their proofs may
  -- lift further), in waves
  let mut stmts ← cuts.mapM fun c => cutStmt plan c n0
  let mut replayed ← replayAll (Array.range cuts.size) cutProof
  let mut done := 0
  repeat
    let all ← lifted.get
    if done == all.size then break
    let wave := all.extract done all.size
    done := all.size
    stmts := stmts ++ wave.map (·.stmtFn.beta #[n0])
    replayed := replayed ++ (← replayAll wave liftedProof)
  let all ← inCtx (mkLambdaFVars #[n0] (heapConj stmts))
  let ihTy ← inCtx do
    withLocalDeclD `m nat fun m => do
      mkForallFVars #[m] (← mkArrow (← mkAppM ``LT.lt #[m, n0]) (all.beta #[m]))
  modify fun c => {c with lctx := c.lctx.modifyLocalDecl ihfv (·.setType ihTy)}
  let step ← inCtx do mkLambdaFVars #[n0, ih] (heapIntro stmts (replayed.map (·.proof)))
  let allN := mkApp3 (mkConst ``Nat.strongRecOn [levelZero]) all N step
  let graph := plan.graph
  let rootIdx := plan.cutOf[graph.rootTpl]!
  let root := cuts[rootIdx]!
  let hroot := heapProj rootIdx allN
  let (rctx0, rootVcs) ← mkCtx plan.goal none
  let rootSubst ← (completeCutSubst root graph.rootSubst #[]).run rctx0
  let args := root.vars.map (Subst.apply rootSubst)
  let factProofs ← root.facts.mapM fun f => (discharge #[] (Subst.apply rootSubst f)).run rctx0
  let invProof ← (discharge #[] (Subst.apply rootSubst root.inv)).run rctx0
  let rootBody := r.search.tpls[graph.rootTpl]!.body
  let hobs' ← inCtx (mkExpectedTypeHint hobs (mkApp (Subst.apply graph.rootSubst rootBody) N))
  -- (the statements' proofs are instantiated: only the root's parts remain)
  let rootArgs ← (args ++ factProofs ++ #[invProof, hobs']).mapM instantiateMVars
  let mut freeVars : Std.HashSet FVarId := {}
  for statement in replayed do
    for v in statement.freeVars do
      unless v == n0fv || v == ihfv do freeVars := freeVars.insert v
  for e in rootArgs do
    for v in (collectFVars {} e).fvarIds do freeVars := freeVars.insert v
  return {proof := mkAppN hroot rootArgs
          conditions := replayed.flatMap (·.conditions) ++ (← rootVcs.get)
          freeVars := freeVars.toArray
          hasSorry := replayed.any (·.hasSorry) || rootArgs.any (·.hasSorry)
          statements := stmts.size
          parts? := some {statements := stmts, proofs := replayed.map (·.proof), n0, ih,
                          fuel := N, root := rootIdx, rootArgs}}

end Blaster.Proof.Explore
