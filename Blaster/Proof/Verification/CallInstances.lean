import Lean

/-! Bounded syntactic instantiation for verification conditions. This module
does not solve implications. In particular, fuel-decrease premises remain in
the generated implication for the backend to prove. Instances are ordinary
applications of already available facts, with all unused proof premises retained.
-/
namespace Blaster.Proof.Verification.CallInstances
open Lean Meta Elab Tactic

/-- Instances of one fact generated in one round. -/
private def maxInstances : Nat := 64

/-- Trigger matches tried for one fact in one round. -/
private def maxMatches : Nat := 512

/-- Triggers matched in sequence to instantiate one fact. -/
private def searchDepth : Nat := 4

/-- Exact syntactic trigger buckets. Preserve encounter order within each
head/arity so indexing does not change the bounded search's choices. -/
private abbrev GroundIndex := Std.HashMap (Expr × Nat) (Array Expr)

/-- Constructor-reduced list views are additional instantiation candidates.
This asserts no rewrite or equation: any discovered instance remains an
application of an independently proved fact. In particular an observation
of `map f (x :: xs)` can trigger that observation's cons equation. -/
def reduceCollectionViews (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun node => do
    if node.isHeadBetaTarget then return .visit node.headBeta
    if node.isAppOfArity ``Prod.fst 3 || node.isAppOfArity ``Prod.snd 3 then
      let index := if node.isAppOf ``Prod.fst then 0 else 1
      if let some field ← projectCore? node.getAppArgs.back! index then
        return .visit field
    if let .proj _ index value := node then
      if let some field ← projectCore? value index then return .visit field
    if node.isAppOfArity ``List.map 4 then
      let rows := node.getAppArgs[3]!
      if rows.isAppOf ``List.nil || rows.isAppOf ``List.cons then
        return .visit (← withTransparency .default (whnf node))
    return .continue)

private def terms (expressions : Array Expr) : MetaM GroundIndex := do
  let found ← IO.mkRef ({} : GroundIndex)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  for expression in expressions do
    let reduced ← if (expression.find? (·.isAppOfArity ``List.map 4)).isSome then
        reduceCollectionViews expression
      else pure expression
    for variant in (if reduced == expression then #[expression] else #[expression, reduced]) do
      variant.forEach fun e => do
        if !e.isApp || e.hasLooseBVars || e.hasMVar || (← seen.get).contains e then return
        if e.getAppFn.isMVar || e.getAppFn.isBVar then return
        seen.modify (·.insert e)
        let key := (e.getAppFn, e.getAppNumArgs)
        found.modify fun index => index.insert key ((index.getD key #[]).push e)
  found.get

private partial def dischargeHoles (proof : Expr) (holes : Array Expr)
    (index : Nat := 0) (premises : Array Expr := #[]) : MetaM (Option Expr) := do
  if index == holes.size then
    let proof ← instantiateMVars proof
    if proof.hasMVar then return none
    return some (← mkLambdaFVars premises proof)
  let hole ← instantiateMVars holes[index]!
  unless hole.isMVar do return ← dischargeHoles proof holes (index + 1) premises
  let type ← instantiateMVars (← inferType hole)
  unless !type.hasMVar && (← isProp type) do return none
  withLocalDeclD `premise type fun premise => do
    hole.mvarId!.assign premise
    dischargeHoles proof holes (index + 1) (premises.push premise)

private def unresolved (args : Array Expr) : MetaM Nat := do
  let mut count := 0
  for arg in args do
    let arg ← instantiateMVars arg
    if arg.isMVar && !(← isProp (← inferType arg)) then count := count + 1
  return count

/-- `ground` indexes the goal's own terms; `groundAll` also the terms of the
instances generated so far. A conclusion pattern may match an instance's
term (an equation instance names the call the next fact is about); a premise
pattern may not, since matching premises against generated conclusions
manufactures ever new terms (`setOrPrune (setOrPrune l c m) c m'`, ...). -/
private partial def search (fact : Expr) (args : Array Expr) (patterns : Array (Expr × Bool))
    (ground groundAll : GroundIndex)
    (fuel : Nat) (results : IO.Ref (Array Expr)) (attempts : IO.Ref Nat)
    (conclusionVars : Array Expr := #[]) (anchored : Bool := false) : MetaM Unit := do
  if (← results.get).size >= maxInstances then return
  let missing ← unresolved args
  if missing == 0 then
    let saved ← getMCtx
    if let some proof ← dischargeHoles (mkAppN fact args) args then
      results.modify (·.push proof)
    setMCtx saved
    return
  if fuel == 0 then return
  -- once every value the conclusion mentions is fixed, matching the remaining
  -- premises against generated instances only selects premises; it cannot
  -- manufacture a new conclusion
  let conclusionFixed ← conclusionVars.allM fun v => do return !(← instantiateMVars v).isMVar
  for (original, fromConclusion) in patterns do
    let before := (← results.get).size
    let pattern ← instantiateMVars original
    unless pattern.hasMVar do continue
    let index := if fromConclusion || conclusionFixed then groundAll else ground
    for candidate in index.getD (pattern.getAppFn, pattern.getAppNumArgs) #[] do
      if (← results.get).size >= maxInstances then return
      if (← attempts.get) >= maxMatches then return
      attempts.modify (· + 1)
      let saved ← getMCtx
      if ← withTransparency .reducible (isDefEq pattern candidate) then
        if (← unresolved args) < missing then
          search fact args patterns ground groundAll (fuel - 1) results attempts conclusionVars true
      setMCtx saved
    -- Prefer the first complete trigger. Falling through to fragments of its
    -- conclusion invents unrelated calls (e.g. ever longer synthetic lists).
    if (← results.get).size > before then return
  -- Once an actual call has anchored a contract, its remaining universally
  -- quantified query values need not occur in an application trigger. For
  -- example, a field observer may already have reduced to an equality in
  -- the goal. Try existing, well-typed local values, with the same finite
  -- search budget. Every result is still an application of the proved fact;
  -- no premise or unification constraint is discarded.
  unless anchored do return
  for original in args do
    let arg ← instantiateMVars original
    unless arg.isMVar do continue
    -- A value the conclusion itself mentions is fixed by an actual call in
    -- the goal, never by an arbitrary local: otherwise every same-typed
    -- local yields another instance (for example `lookup k k`, `lookup k t`,
    -- ... for a lemma about `lookup c t`), and the leaf drowns in them.
    if conclusionVars.contains original then continue
    let type ← instantiateMVars (← inferType arg)
    if type.hasMVar || type.isSort || type.isForall || (← isProp type) then continue
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail || declaration.type != type then continue
      if (← results.get).size >= maxInstances || (← attempts.get) >= maxMatches then return
      attempts.modify (· + 1)
      let saved ← getMCtx
      if ← isDefEq arg declaration.toExpr then
        search fact args patterns ground groundAll (fuel - 1) results attempts conclusionVars true
      setMCtx saved
    return

/-- A symbolic natural index need not be syntactically zero or a successor.
Instantiate an equation's numeric constructor pattern with a predecessor, but
retain the equality to that constructor as an explicit premise. The resulting
proof is just congruence and transitivity applied to the original equation;
no arithmetic condition is discharged by the matcher. -/
private def guardedNaturalInstances (fact : Expr) (ground : GroundIndex) :
    MetaM (Array Expr) := do
  let saved ← getMCtx
  let (args, _, result) ← forallMetaTelescope (← inferType fact)
  let some (_, left, _) := result.eq? | setMCtx saved; return #[]
  unless left.isApp && (← args.allM fun arg => do return !(← isProp (← inferType arg))) do
    setMCtx saved
    return #[]
  let initial ← getMCtx
  let mut results := #[]
  for candidate in (ground.getD (left.getAppFn, left.getAppNumArgs) #[]).take maxInstances do
    setMCtx initial
    let mut changes : Array (Nat × Expr × Expr) := #[]
    let mut matched := true
    for ((pattern, value), position) in (left.getAppArgs.zip candidate.getAppArgs).zipIdx do
      let before ← getMCtx
      if ← withTransparency .reducible (isDefEq pattern value) then continue
      setMCtx before
      unless (← whnf (← inferType value)).isConstOf ``Nat do
        matched := false
        break
      let pattern ← instantiateMVars pattern
      let zero ← withTransparency .reducible (isDefEq pattern (mkNatLit 0))
      unless zero do
        setMCtx before
        let pattern ← withTransparency .reducible (whnf pattern)
        unless pattern.isAppOfArity ``Nat.succ 1 do
          matched := false
          break
        let predecessor := mkApp2 (mkConst ``Nat.sub) value (mkNatLit 1)
        unless ← withTransparency .reducible (isDefEq pattern.getAppArgs[0]! predecessor) do
          matched := false
          break
      changes := changes.push (position, value, ← instantiateMVars pattern)
    unless matched && !changes.isEmpty && (← unresolved args) == 0 do continue
    let some proof ← dischargeHoles (mkAppN fact args) args | continue
    let proof ← instantiateMVars proof
    let some (_, originalLeft, _) := (← inferType proof).eq? | continue
    let declarations ← changes.mapM fun (_, value, pattern) => do
      return (`indexGuard, fun (_ : Array Expr) => mkEq value pattern)
    let proof ← withLocalDeclsD declarations fun guards => do
      let mut proof := proof
      let mut current := originalLeft
      for ((position, value, _), guard) in changes.zip guards do
        let currentArgs := current.getAppArgs
        let lifted ← withLocalDeclD `index (mkConst ``Nat) fun parameter => do
          let function ← mkLambdaFVars #[parameter]
            (mkAppN current.getAppFn (currentArgs.set! position parameter))
          mkCongrArg function guard
        proof ← mkEqTrans lifted proof
        current := mkAppN current.getAppFn (currentArgs.set! position value)
      mkLambdaFVars guards proof
    unless proof.hasMVar do results := results.push proof
  setMCtx saved
  return results

private def instances (fact : Expr) (ground groundAll : GroundIndex) :
    MetaM (Array Expr) := do
  let saved ← getMCtx
  let (args, _, result) ← forallMetaTelescope (← inferType fact)
  let expressions := (← args.mapM inferType).push result
  -- Projecting a conjunction can leave an unused query parameter (for
  -- example the key of a map whose sortedness is the selected conjunct).
  -- Instantiate only genuinely vacuous data binders, and only with a checked
  -- inhabitant. An existing value in this context suffices even if the type
  -- has no Inhabited instance. An Empty parameter cannot justify a result
  -- unless such a value was already given by the theorem's assumptions.
  for arg in args do
    unless arg.isMVar do continue
    let type ← instantiateMVars (← inferType arg)
    if type.hasMVar || (← isProp type) then continue
    if expressions.any (fun expression => (expression.find? (· == arg)).isSome) then continue
    if let some existing := (← getLCtx).findDecl? (fun declaration =>
        if declaration.type == type then some declaration.toExpr else none) then
      arg.mvarId!.assign existing
      continue
    let context ← getMCtx
    try
      let value ← instantiateMVars (← mkDefault type)
      unless !value.hasMVar do throwError "vacuous binder has no closed inhabitant"
      arg.mvarId!.assign value
    catch _ => setMCtx context
  let patterns ← IO.mkRef (#[] : Array (Expr × Nat × Bool))
  -- A defining equation is useful at an existing left-hand-side call. Using
  -- fragments of its right-hand side as triggers manufactures new calls
  -- (for example f (x :: xs) from f xs), and repeated rounds grow an
  -- unbounded family of synthetic constructor terms.
  let anchor ← match result.eq? with
    | some (_, left, _) => do
      if !left.isApp || (← args.anyM fun arg => do isProp (← inferType arg)) then
        pure none
      else
        let covered ← args.allM fun arg => do
          let arg ← instantiateMVars arg
          return !arg.isMVar || (left.find? (· == arg)).isSome
        pure (if covered then some left else none)
    | none => pure none
  for (expression, expressionIndex) in expressions.zipIdx do
    expression.forEach fun e => do
      if let some anchor := anchor then
        unless e == anchor do return
      unless e.isApp && e.hasMVar && !e.hasLooseBVars do return
      let head := e.getAppFn
      unless head.isConst || head.isFVar do return
      if #[``And, ``Or, ``Not, ``Exists].any head.isConstOf then return
      -- Logical and arithmetic structure is not a trigger (`?k = ?k'` would
      -- match any equation of the goal); a complete premise `f x = y` is.
      let logical : Array Name := #[``Eq, ``Ne, ``HEq, ``Iff, ``ite, ``dite, ``Decidable.decide,
        ``cond, ``Bool.and, ``Bool.or, ``Bool.not, ``BEq.beq, ``bne, ``LE.le, ``LT.lt, ``GE.ge,
        ``GT.gt, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Neg.neg]
      if logical.any head.isConstOf && !(expressionIndex < args.size && e == expression) &&
          anchor != some e then return
      -- an instance argument (`Decidable (c = cur)`) is elaboration detail, not a call
      if (← isClass? (← inferType e)).isSome then return
      -- Match saturated calls, not partial applications or a previously
      -- generated whole equality. An equality law must also instantiate at
      -- newly exposed calls, rather than repeatedly matching only itself.
      if (← inferType e).isForall then return
      if expressionIndex == args.size && e.isAppOf ``Eq then return
      -- Anchor input/output equations before incidental observations in the
      -- conclusion. Otherwise a decoder law can be instantiated with an
      -- unrelated observed value rather than its actual returned value.
      let priority := if expressionIndex < args.size && e == expression &&
          (e.isAppOf ``Eq || head.isFVar) then 2
        else if expressionIndex < args.size && head.isFVar then 1 else 0
      patterns.modify (·.push (e, priority, expressionIndex == args.size))
  let results ← IO.mkRef #[]
  let originalPatterns ← patterns.get
  let mut ranked := #[]
  for ((pattern, priority, fromConclusion), index) in originalPatterns.zipIdx do
    let mut coverage := 0
    for arg in args do
      let arg ← instantiateMVars arg
      if arg.isMVar && !(← isProp (← inferType arg)) &&
          (pattern.find? (· == arg)).isSome then coverage := coverage + 1
    ranked := ranked.push ((pattern, fromConclusion), (priority * (args.size + 1) + coverage) *
      (originalPatterns.size + 1) + originalPatterns.size - index)
  let patterns := (ranked.qsort (fun a b => a.2 > b.2)).map (·.1)
  let conclusionVars := args.filter fun arg => arg.isMVar && (result.find? (· == arg)).isSome
  search fact args patterns ground groundAll searchDepth results (← IO.mkRef 0) conclusionVars
  let results ← results.get
  setMCtx saved
  return results ++ (← guardedNaturalInstances fact ground)

/-- A fully covered, unconditional equation can only use its left-hand-side
trigger (the same rule used by `instances`). If that head is absent, avoid
building fresh metavariables and searching this fact at all. Dependent or
propositional binders conservatively retain the ordinary matcher. -/
private def equationAnchor? (fact : Expr) : MetaM (Option (Expr × Nat)) := do
  let mut type ← inferType fact
  if type.hasMVar then return none
  let mut count := 0
  while type.isForall do
    let domain := type.bindingDomain!
    if domain.hasLooseBVars then return none
    if ← isProp domain then return none
    count := count + 1
    type := type.bindingBody!
  let some (_, left, _) := type.eq? | return none
  unless left.isApp && (left.getAppFn.isConst || left.getAppFn.isFVar) do return none
  unless (List.range count).all left.hasLooseBVar do return none
  return some (left.getAppFn, left.getAppNumArgs)

private partial def evidence (proof target : Expr) : MetaM (Option Expr) := do
  let type ← inferType proof
  if type == target then return some proof
  if type.isAppOfArity ``And 2 then
    if let some found ← evidence (← mkAppM ``And.left #[proof]) target then return some found
    evidence (← mkAppM ``And.right #[proof]) target
  else return none

/-- Apply only premises literally already present (including conjunction
projections). In particular this never proves an arithmetic fuel condition. -/
private def applyAvailable (proof : Expr) : MetaM Expr := do
  let mut proof := proof
  -- (at most as many premises as a fact plausibly has)
  for _ in [:128] do
    let .forallE _ domain _ _ ← inferType proof | break
    unless ← isProp domain do break
    let mut supplied := if domain.isConstOf ``True then some (mkConst ``True.intro) else none
    for declaration in ← getLCtx do
      if supplied.isSome then break
      if ← isProp declaration.type then supplied ← evidence declaration.toExpr domain
    let some argument := supplied | break
    proof := mkApp proof argument
  return proof

/-- Project conjunctive results without discharging any premise. In particular
`accepted → guard ∧ (∀ query, bound query)` must yield two usable contracts,
not one higher-order formula that is discarded by first-order abstraction. -/
private partial def conjunctiveFragments (fact : Expr) : MetaM (Array Expr) := do
  let mut conclusion ← inferType fact
  while conclusion.isForall do conclusion := conclusion.bindingBody!
  -- An equality cannot hide a conjunction. Avoid opening and recreating the
  -- telescope for the common defining-equation case.
  if conclusion.isAppOfArity ``Eq 3 then return #[fact]
  forallTelescope (← inferType fact) fun args result => do
    unless result.isAppOfArity ``And 2 do return #[fact]
    let applied := mkAppN fact args
    let left ← mkLambdaFVars args (← mkAppM ``And.left #[applied])
    let right ← mkLambdaFVars args (← mkAppM ``And.right #[applied])
    return (← conjunctiveFragments left) ++ (← conjunctiveFragments right)

/-- Maximal nesting of each constant head under itself (`f (… f … …)` has
nesting 2 for `f`). -/
private partial def headNesting (env : Environment) (e : Expr) (acc : Std.HashMap Name Nat := {}) :
    Std.HashMap Name Nat :=
  let rec depth (f : Name) (e : Expr) : Nat :=
    let inner := match e with
      | .app .. => e.getAppArgs.foldl (fun m a => max m (depth f a)) (depth f e.getAppFn)
      | .lam _ t b _ | .forallE _ t b _ => max (depth f t) (depth f b)
      | .letE _ t v b _ => max (depth f t) (max (depth f v) (depth f b))
      | .mdata _ b | .proj _ _ b => depth f b
      | _ => 0
    if e.isApp && e.getAppFn.isConstOf f then inner + 1 else inner
  -- only program functions and constructors: logical structure (equations
  -- under conditionals, matchers) nests freely
  let logical : Array Name := #[``Eq, ``Ne, ``HEq, ``Iff, ``And, ``Or, ``Not, ``ite, ``dite,
    ``Decidable.decide, ``cond, ``Exists, ``Bool.and, ``Bool.or, ``Bool.not, ``BEq.beq, ``bne]
  let heads := e.getUsedConstants.filter fun n =>
    !logical.contains n && !isMatcherCore env n &&
      match env.find? n with
      | some (.defnInfo _) | some (.ctorInfo _) | some (.opaqueInfo _) => true
      | _ => false
  heads.foldl (init := acc) fun acc f =>
    let d := depth f e
    acc.insert f (max d (acc.getD f 0))

/-- Does `candidate` nest some head deeper than the base expressions do?
Chained instances otherwise manufacture ever deeper synthetic calls
(`insert k v (insert k v l)`, `setOrPrune (setOrPrune acc c m) c m'`). -/
private def deeperThan (env : Environment) (base : Std.HashMap Name Nat) (candidate : Expr) :
    Option (Name × Nat × Nat) :=
  -- an instance may wrap a goal term in one more call of the same head (the
  -- fact's own conclusion), never more
  (headNesting env candidate).toList.findSome? fun (f, d) =>
    if d > base.getD f 0 + 2 then some (f, d, base.getD f 0 + 2) else none

/-- Instance types already added during a proof search. An instance a case
split has consumed (its `if` turned into two branches) is not generated again
in the branches: that would split it again, forever. -/
abbrev Generated := IO.Ref (Std.HashSet Expr)

/-- Add instances of `extraFacts` and of the goal's summaries and quantified
hypotheses at the calls of the goal, for up to `rounds` rounds. Finite
instances only: a missing instance may make verification fail; it cannot make
an invalid statement pass. Extra facts can remain polymorphic: instantiation
fixes their type and universe arguments at actual calls. -/
def instantiate (rounds : Nat) (extraFacts : Array Expr)
    (generated? : Option Generated := none)
    (virtual : TacticM (Array Expr) := pure #[]) : TacticM Unit := do
  let seen ← match generated? with
    | some ref => pure ref
    | none => IO.mkRef ({} : Std.HashSet Expr)
  let anchors ← IO.mkRef ({} : Std.HashMap Expr (Option (Expr × Nat)))
  let fragments ← IO.mkRef ({} : Std.HashMap Expr (Array Expr))
  -- Leaf normalization calls this routine more than once. Retain instances
  -- already present in this goal; otherwise every pass duplicates them and
  -- feeds the duplicates into all later matching and solver preprocessing.
  -- Inspect the current types, not a persistent cache: branch substitution
  -- and constructor normalization may have changed or removed old facts.
  withMainContext do
    for declaration in ← getLCtx do
      if declaration.userName.toString.startsWith "callInstance" then
        seen.modify (·.insert declaration.type)
  for _ in [:rounds] do
    let changed ← withMainContext do
      let mut expressions := #[(← (← getMainGoal).getType)]
      let mut instanceExpressions : Array Expr := #[]
      let env ← getEnv
      let mut base : Std.HashMap Name Nat := headNesting env (← (← getMainGoal).getType)
      let mut facts := extraFacts
      for declaration in ← getLCtx do
        if declaration.isImplementationDetail then continue
        let summary := declaration.userName.toString.startsWith "summary"
        let quantified ← if !summary && (← isProp declaration.type) && declaration.type.isForall then
            forallTelescope declaration.type fun args _ => do
              args.anyM fun arg => do return !(← isProp (← inferType arg))
          else pure false
        if summary || quantified then
          facts := facts.push declaration.toExpr
          -- a quantified hypothesis (an induction hypothesis) is part of the
          -- goal's vocabulary
          base := headNesting env declaration.type base
        else if declaration.userName.toString.startsWith "callInstance" then
          instanceExpressions := instanceExpressions.push declaration.type
        else if ← isProp declaration.type then
          expressions := expressions.push declaration.type
          base := headNesting env declaration.type base
      -- `virtual`: terms the goal does not spell out but the solver reasons
      -- through (a match alternative at a value an equation offers); index
      -- entries only, recomputed each round from the instances so far
      let virtual ← virtual
      for term in virtual do base := headNesting env term base
      let ground ← terms (expressions ++ virtual)
      let groundAll ← if instanceExpressions.isEmpty then pure ground
        else terms (expressions ++ virtual ++ instanceExpressions)
      let mut added := false
      -- A caller may pass the same summary that is also in the local
      -- context. Match each proof only once per round, preserving its first
      -- occurrence and the bounded search order. This changes no fact or
      -- instance: successful instance types were already deduplicated below.
      let mut visited : Std.HashSet Expr := {}
      for fact in facts do
        if visited.contains fact then continue
        visited := visited.insert fact
        let parts ← match (← fragments.get)[fact]? with
          | some parts => pure parts
          | none => do
            let parts ← conjunctiveFragments fact
            unless fact.hasMVar do fragments.modify (·.insert fact parts)
            pure parts
        for fragment in parts do
          let anchor ← match (← anchors.get)[fragment]? with
            | some cached => pure cached
            | none => do
              let anchor ← equationAnchor? fragment
              unless fragment.hasMVar do anchors.modify (·.insert fragment anchor)
              pure anchor
          if let some anchor := anchor then
            unless groundAll.contains anchor do continue
          for proof in ← instances fragment ground groundAll do
            let proof ← applyAvailable proof
            let type ← inferType proof
            if (← seen.get).contains type then continue
            if (deeperThan env base type).isSome then continue
            seen.modify (·.insert type)
            let goal ← getMainGoal
            let (_, goal) ← goal.note (← mkFreshUserName `callInstance) proof
            replaceMainGoal [goal]
            added := true
      pure added
    unless changed do break

end Blaster.Proof.Verification.CallInstances
