import Lean.Elab.Tactic.Induction
import Blaster.Proof.Verification.CallInstances
import Blaster.Proof.Verification.Local
import Blaster.Proof.Induction.Source
import Blaster.Proof.Induction.Observed
import Blaster.Proof.Library
import Blaster.Optimize.Uninterpreted

/-!
Verification of ordinary Lean statements using checked functional induction.

The caller supplies the goal and, optionally, ordinary proved lemmas. There
are no program-point annotations, source-number conventions, proof callbacks,
or application-specific recursion rules. Search is deliberately bounded: a
missing invariant is a failure, never permission to assume a recursive call.
-/
namespace Blaster.Proof.Induction
open Lean Meta Elab Tactic
open Blaster.Proof.Verification

register_option blaster.induction.maxGoals : Nat := {
  defValue := 64
  descr := "Maximum proof-search goals in automatic Blaster induction" }

register_option blaster.induction.maxDepth : Nat := {
  defValue := 6
  descr := "Maximum nested functional inductions or case splits" }

initialize registerTraceClass `Blaster.induction

private structure Call where
  expression : Expr
  info : FunIndInfo

private def naturalLiteral (expression : Expr) : Bool :=
  expression.isRawNatLit ||
    (expression.isAppOfArity ``OfNat.ofNat 3 &&
      expression.getAppArgs[0]!.isConstOf ``Nat && expression.getAppArgs[1]!.isRawNatLit)

/-- Arithmetic primitives already have backend semantics. Do not replace
their implementation with an unconstrained recursive function. -/
private def primitive (name : Name) : Bool :=
  #[`Nat, `Int, `Bool, `BitVec, `UInt8, `UInt16, `UInt32, `UInt64, `USize,
    `HAdd, `HSub, `HMul, `HDiv, `HMod, `HPow, `Neg, `OfNat, `LE, `LT,
    `BEq, `Decidable].any (·.isPrefixOf name)

private def expressions : TacticM (Array Expr) := withMainContext do
  -- Tactics such as `fun_induction` leave assigned metavariables in goal and
  -- hypothesis types; constants below them are part of the goal.
  let mut result := #[(← instantiateMVars (← (← getMainGoal).getType))]
  for declaration in ← getLCtx do
    if !declaration.isImplementationDetail && (← isProp declaration.type) then
      result := result.push (← instantiateMVars declaration.type)
  return result

private def calls (input : Array Expr) : MetaM (Array Call) := do
  let candidates ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  for expression in input do
    expression.forEach fun node => do
      unless node.isApp && !node.hasLooseBVars && !(← seen.get).contains node do return
      seen.modify (·.insert node)
      let .const name _ := node.getAppFn | return
      if primitive name then return
      candidates.modify (·.push node)
  let mut result : Array Call := #[]
  let mut generalizedCalls : Array Call := #[]
  for candidate in ← candidates.get do
    let some info ← getFunIndInfo? false true candidate.getAppFn.constName! | continue
    unless info.params.size == candidate.getAppNumArgs do continue
    let targets := (candidate.getAppArgs.zip info.params).filterMap fun (argument, kind) =>
      if kind == .target then some argument else none
    unless !targets.isEmpty do continue
    if targets.all (·.isFVar) then
      result := result.push {expression := candidate, info}
    else if targets.all (fun target => target.isFVar || naturalLiteral target) then
      -- Lean's functional-induction elaborator generalizes the numeral and
      -- constructs the application back to it. This proves a stronger, fully
      -- quantified lemma; it does not unroll a fixed execution budget.
      generalizedCalls := generalizedCalls.push {expression := candidate, info}
  -- Prefer the recursion carrying more changing arguments (e.g. fuel and a
  -- list) over an observation of just that list. Otherwise a fixed-budget
  -- theorem can waste its search budget inducting on the observation first.
  return (result ++ generalizedCalls).qsort fun left right =>
    (left.info.params.filter (· == .target)).size >
      (right.info.params.filter (· == .target)).size

private def recursiveNames (input : Array Expr) : MetaM (Array Name) := do
  let mut result := #[]
  let mut seen : Std.HashSet Name := {}
  for expression in input do
    for name in expression.getUsedConstants do
      if seen.contains name || primitive name then continue
      seen := seen.insert name
      if (← getFunIndInfo? false true name).isSome then result := result.push name
  return result

/-- Constructor cases can expose a recursive collection call before any
induction has happened. Reduce those equations too, but never unfold a
numeric recursion budget merely because its argument is a literal. -/
private def structuralNames (names : Array Name) : MetaM (Array Name) :=
  names.filterM fun name => do
    let some info ← getFunIndInfo? false true name | return false
    forallTelescope (← getConstInfo name).type fun arguments _ => do
      let mut found := false
      for (argument, kind) in arguments.zip info.params do
        unless kind == .target do continue
        let type ← whnf (← inferType argument)
        let .const typeName _ := type.getAppFn | return false
        if primitive typeName then return false
        let .inductInfo _ ← getConstInfo typeName | return false
        found := true
      return found

/-- Hypotheses `value = constructor …` (or symmetric) over a non-primitive type
(splitting a projected field leaves `record.field = constructor ...` rather than
substituting the record itself), with the constructor side: `true` when the
constructor is on the left (`[] = w`), so that the rewrite must run right to left. -/
private def shapeHypotheses : TacticM (Array (FVarId × Bool)) := withMainContext do
  let mut shapes := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let some (domain, left, right) := (← instantiateMVars declaration.type).eq? | continue
    let domain ← whnf domain
    if domain.isConst && primitive domain.constName! then continue
    let constructor := fun expression => do
      pure (← isConstructorApp'? (← whnf expression)).isSome
    let leftCtor ← constructor left
    if leftCtor != (← constructor right) then
      shapes := shapes.push (declaration.fvarId, leftCtor)
  return shapes

/-- Injectivity lemmas of the constructors mentioned by the goal, so that
`C a = C b` reduces to `a = b`. -/
private def injectivityLemmas : TacticM (Array Name) := withMainContext do
  let env ← getEnv
  let mut result := #[]
  for expression in ← expressions do
    for name in expression.getUsedConstants do
      let some (.ctorInfo _) := env.find? name | continue
      let lemma := name ++ `injEq
      if env.contains lemma && !result.contains lemma then result := result.push lemma
  return result

/-- `simp only [names, rules]` at the hypotheses `locations` (and the target).
Definitions unfold by their equation lemmas, theorems rewrite. -/
private def simpOnly (names : Array Name) (rules : Array (FVarId × Bool)) (locations : Array FVarId)
    (target : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let result ← goal.withContext do
    let mut theorems : SimpTheorems := {}
    for name in names do
      match ← getConstInfo name with
      | .thmInfo _ => theorems ← theorems.addConst name
      | _ => theorems ← theorems.addDeclToUnfold name
    for (hypothesis, inv) in rules do
      theorems ← theorems.add (.fvar hypothesis) #[] (mkFVar hypothesis) (inv := inv)
    let context ← Simp.mkContext (config := {failIfUnchanged := false, maxSteps := 20000})
      (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
    let (result, _) ← simpGoal goal context (simplifyTarget := target) (fvarIdsToSimp := locations)
    pure result
  match result with
  | none => replaceMainGoal []
  | some (_, goal) => replaceMainGoal [goal]

/-- Reduce `x >>= f` when `x` is a constructor application (for example
`Except.ok a >>= f` to `f a`). The replacement is definitional. -/
private def reduceBinds (expression : Expr) : MetaM Expr :=
  Meta.transform expression (post := fun node => do
    let monadic := node.isAppOfArity ``Bind.bind 6 || node.isAppOfArity ``Pure.pure 4 ||
      node.isAppOfArity ``MonadExcept.throw 5 || node.isAppOfArity ``MonadExceptOf.throw 5 ||
      node.isAppOfArity ``throwThe 5
    unless monadic do return .continue
    if node.isAppOfArity ``Bind.bind 6 then
      let value := node.getArg! 4
      if (← isConstructorApp'? (← whnfR value)).isNone then return .continue
    -- only for concrete inductive monads (`Except`, `Option`, ...), where the
    -- operation reduces to a constructor
    let .const typeName _ := (← whnf (← inferType node)).getAppFn | return .continue
    let .inductInfo _ ← getConstInfo typeName | return .continue
    let reduced ← whnfD node
    if reduced == node then return .continue
    return .visit reduced)

/-- Apply `reduceBinds` to the target and the propositional hypotheses. -/
private def reduceGoalBinds : TacticM Unit := do
  let mut goal ← getMainGoal
  let hasBind := fun (e : Expr) => (e.find? fun t => t.isAppOfArity ``Bind.bind 6 ||
    t.isAppOfArity ``Pure.pure 4 || t.isAppOfArity ``MonadExcept.throw 5 ||
    t.isAppOfArity ``MonadExceptOf.throw 5 || t.isAppOfArity ``throwThe 5).isSome
  let fvarIds ← goal.withContext do
    return (← getLCtx).foldl (init := (#[] : Array FVarId)) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.fvarId
  -- `do`-notation join points are `let`s: substitute them so that conditionals
  -- inside them become visible to case splitting.
  let hasLet := fun (e : Expr) => (e.find? (·.isLet)).isSome
  let prepare := fun (e : Expr) => do
    let e ← if hasLet e then zetaReduce e else pure e
    if hasBind e then reduceBinds e else pure e
  for fvarId in fvarIds do
    let type ← goal.withContext do instantiateMVars (← fvarId.getType)
    unless hasBind type || hasLet type do continue
    unless ← goal.withContext (isProp type) do continue
    let reduced ← goal.withContext (prepare type)
    unless reduced == type do goal ← goal.replaceLocalDeclDefEq fvarId reduced
  let target ← goal.withContext do instantiateMVars (← goal.getType)
  if hasBind target || hasLet target then
    let reduced ← goal.withContext (prepare target)
    unless reduced == target do goal ← goal.replaceTargetDefEq reduced
  replaceMainGoal [goal]

private def propositionHypotheses : TacticM (Array FVarId) := withMainContext do
  let mut result := #[]
  for declaration in ← getLCtx do
    if !declaration.isImplementationDetail && (← isProp declaration.type) then
      result := result.push declaration.fvarId
  return result

/-- Only equations of functions actually mentioned in the theorem are used.
The simplifier produces equality proofs; this is not optimizer output asserted
as a rewrite. User-provided representation equations use the same mechanism.
Checked shape hypotheses (`value = constructor …`) are propagated before calls
on the value are abstracted; a shape is never used to simplify itself (that
would turn the case fact into `True`). -/
private def normalize (names : Array Name) : TacticM Unit := do
  let names := names ++ (← injectivityLemmas)
  let shapes ← shapeHypotheses
  unless shapes.isEmpty || names.isEmpty do simpOnly names #[] (shapes.map (·.1)) false
  if (← getGoals).isEmpty then return
  -- Reduction can create shapes (`C a = C w` becomes `a = w`): iterate until
  -- the shape hypotheses are stable.
  for _ in [:3] do
    let shapes ← shapeHypotheses
    let shapeIds := shapes.map (·.1)
    let others := (← propositionHypotheses).filter (!shapeIds.contains ·)
    simpOnly names shapes others true
    if (← getGoals).isEmpty then return
    if (← shapeHypotheses) == shapes then break
  if (← getGoals).isEmpty then return
  reduceGoalBinds

private def exposeSource (discovery : Source.Discovery) (everywhere : Bool := false)
    (delta : Bool := false) : TacticM Unit := do
  let mut goal ← getMainGoal
  let premises ← goal.withContext do
    let mut result := #[]
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        result := result.push declaration.fvarId
    return result
  for premise in premises do
    let original ← goal.withContext (premise.getType)
    let type ← goal.withContext do Source.expose discovery original everywhere delta
    -- definitional replacement keeps every free variable (reverting would
    -- rename the dependents of a premise, e.g. after a case split)
    unless type == original do goal ← goal.replaceLocalDeclDefEq premise type
  let original ← goal.withContext (goal.getType)
  let target ← goal.withContext do Source.expose discovery original everywhere delta
  unless target == original do goal ← goal.replaceTargetDefEq target
  replaceMainGoal [goal]

/-- Source discovery for a goal that comes with proved summaries. A wrapper
mentioned by a summary is the summary's interface: it stays folded so that the
summary can be instantiated at its calls; the leaf falls back to exposing it. -/
private def discoverKeeping (summaries : Array Expr) (constants : Array Name) :
    TacticM Source.Discovery := do
  let discovery ← Source.discover constants
  if summaries.isEmpty then return discovery
  let mut mentioned : NameSet := {}
  for summary in summaries do
    for name in (← inferType summary).getUsedConstants do
      mentioned := mentioned.insert name
  return {discovery with wrappers := discovery.wrappers.filter (!mentioned.contains ·)}

/-- The values an expression takes when each decision in it (a conditional, a
decision recursor, a match with closed alternatives) is resolved to one of its
branches, decisions inside arguments included; bounded in number. -/
private partial def resolutions (expression : Expr) (limit : Nat := 16) : MetaM (Array Expr) := do
  let stripped := fun (e : Expr) => Id.run do
    let mut body := e
    while body.isLambda do body := body.bindingBody!
    return body
  let branches : Option (Array Expr) :=
    if expression.isAppOfArity ``ite 5 || expression.isAppOfArity ``dite 5 then
      some #[expression.getAppArgs[3]!, expression.getAppArgs[4]!]
    else if expression.isAppOfArity ``Decidable.rec 5 then
      some #[expression.getAppArgs[2]!, expression.getAppArgs[3]!]
    else if expression.isAppOfArity ``Decidable.casesOn 5 then
      some #[expression.getAppArgs[3]!, expression.getAppArgs[4]!]
    else none
  let branches ← match branches with
    | some found => pure (some found)
    | none => do
      if let some info ← matchMatcherApp? expression then pure (some info.alts) else pure none
  -- the unresolved expression is a value too (a match whose alternatives bind
  -- fields is only readable as a whole)
  if let some found := branches then
    let mut result := #[expression]
    for branch in found do
      let body := stripped branch
      unless body.hasLooseBVars do result := result ++ (← resolutions body limit)
    return result.extract 0 limit
  if expression.isApp && (expression.getAppFn.isConst || expression.getAppFn.isFVar) then
    let mut combinations := #[expression.getAppFn]
    for argument in expression.getAppArgs do
      let choices ← if argument.hasLooseBVars then pure #[argument] else resolutions argument limit
      let mut next := #[]
      for combination in combinations do
        for choice in choices do
          if next.size < limit then next := next.push (mkApp combination choice)
      combinations := next
    return combinations
  return #[expression]

/-- Constructor-headed values an expression offers, over its resolutions. -/
private def constructorValues (expression : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  return (← resolutions expression).filter fun value =>
    match value.getAppFn with
    | .const name _ => match env.find? name with
      | some (.ctorInfo _) => true
      | _ => false
    | _ => false

/-- Terms a match alternative computes at the values its discriminant's
equations offer. With `match get? c w with | some inner => getD t inner 0` and
`get? c w = if c = c0 then some (insert t0 q inner0) else get? c v`, that is
`getD t (insert t0 q inner0) 0`: a call the solver reasons through in that
alternative and whose facts it needs, while the goal spells it out nowhere.
The results are index entries for fact instantiation only; nothing is assumed. -/
private def constructorFlows : TacticM (Array Expr) := withMainContext do
  let mut expressions := #[← (← getMainGoal).getType]
  for declaration in ← getLCtx do
    if !declaration.isImplementationDetail && (← isProp declaration.type) then
      expressions := expressions.push declaration.type
  let equations ← IO.mkRef (#[] : Array (Expr × Expr))
  for expression in expressions do
    expression.forEach fun node => do
      if node.hasLooseBVars then return
      if let some (_, left, right) := node.eq? then
        equations.modify fun found => (found.push (left, right)).push (right, left)
  let mut equations ← equations.get
  if equations.isEmpty then return #[]
  -- the fields of constructor values an equation relates are equal too:
  -- `(if ok then Except.ok E else Except.error m) = Except.ok w` gives `E = w`
  let mut fields := #[]
  for (left, right) in equations do
    for valueLeft in ← constructorValues left do
      for valueRight in ← constructorValues right do
        unless valueLeft.getAppFn == valueRight.getAppFn &&
          valueLeft.getAppNumArgs == valueRight.getAppNumArgs do continue
        for (a, b) in valueLeft.getAppArgs.zip valueRight.getAppArgs do
          if a != b && !a.hasLooseBVars && !b.hasLooseBVars then
            fields := (fields.push (a, b)).push (b, a)
  equations := equations ++ fields
  -- a discriminant is looked up as written and with a variable replaced by a
  -- value the equations give it (`get? c w` as `get? c (insert c0 inner v)`)
  let variants := fun (discriminant : Expr) => Id.run do
    let mut result := #[discriminant]
    for (x, value) in equations do
      if x.isFVar && discriminant.containsFVar x.fvarId! && !value.containsFVar x.fvarId! then
        result := result.push (discriminant.replaceFVar x value)
    return result
  let discovery ← Source.discover (expressions.flatMap (·.getUsedConstants))
  let results ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  for expression in expressions do
    expression.forEach fun node => do
      if node.hasLooseBVars || (← seen.get).contains node then return
      let some info ← matchMatcherApp? node | return
      unless info.discrs.size == 1 do return
      seen.modify (·.insert node)
      let discriminant := info.discrs[0]!
      let lookups := variants discriminant
      -- an equation about the discriminant, as written or up to unfolding
      -- (`getD c0 v []` against its match)
      let related := fun (left : Expr) => do
        for lookup in lookups do
          if left == lookup then return true
          if left.getAppFn == lookup.getAppFn && left.getAppNumArgs == lookup.getAppNumArgs then
            if ← isDefEq left lookup then return true
        return false
      for (left, right) in equations do
        unless ← related left do continue
        for candidate in ← constructorValues right do
          let replaced := node.replace fun x => if x == discriminant then some candidate else none
          let reduced ← reduceMatcher? replaced
          let .reduced body := reduced | continue
          let body := body.headBeta
          results.modify (·.push body)
          let exposed ← Source.expose discovery body
          unless exposed == body do results.modify (·.push exposed)
  results.get

/-- Equations of recursive calls at constructor arguments the solver's own
case analysis produces. `get? t (match get? c0 v with | some inner => inner
| none => [])` becomes `get? t []` in the solver's `none` case; the
uninterpreted symbol knows `get? t [] = none` only if it is stated. Each
equation is a definitional unfolding, added as a hypothesis with a reflexivity
proof. -/
private def constructorEquations (recursive : Array Name) (flows : Array Expr) : TacticM Unit := do
  let mut goal ← getMainGoal
  let mut added : Std.HashSet Expr := {}
  let existing ← goal.withContext do
    (← getLCtx).foldlM (init := ({} : Std.HashSet Expr)) fun found declaration => do
      if declaration.isImplementationDetail then return found
      return found.insert declaration.type
  let mut expressions := flows
  let hypotheses ← goal.withContext do
    let mut result := #[← goal.getType]
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        result := result.push declaration.type
    return result
  expressions := expressions ++ hypotheses
  let calls ← IO.mkRef (#[] : Array Expr)
  let matched ← IO.mkRef (#[] : Array Expr)
  for expression in expressions do
    expression.forEach fun node => do
      if node.hasLooseBVars || !node.isApp then return
      if let some info ← matchMatcherApp? node then
        for discriminant in info.discrs do
          if discriminant.isFVar then matched.modify (·.push discriminant)
      let .const name _ := node.getAppFn | return
      unless recursive.contains name do return
      calls.modify (·.push node)
  let env ← getEnv
  -- a variable a match reads takes each nullary constructor of its type in
  -- some alternative (`merged = []`); the solver reasons through that case
  let mut candidates : Array (Expr × Expr) := #[]
  for matchedVariable in ← matched.get do
    let type ← goal.withContext do whnf (← inferType matchedVariable)
    let .const inductName levels := type.getAppFn | continue
    let some (.inductInfo info) := env.find? inductName | continue
    for constructor in info.ctors do
      let some (.ctorInfo constructorInfo) := env.find? constructor | continue
      if constructorInfo.numFields == 0 then
        candidates := candidates.push
          (matchedVariable, mkAppN (mkConst constructor levels) (type.getAppArgs.extract 0 constructorInfo.numParams))
  let isConstructorApp := fun (e : Expr) => match e.getAppFn with
    | .const name _ => match env.find? name with
      | some (.ctorInfo _) => true
      | _ => false
    | _ => false
  for call in ← calls.get do
    let mut variants ← goal.withContext (resolutions call)
    for (x, value) in candidates do
      if call.containsFVar x.fvarId! then
        variants := variants ++ (← goal.withContext (resolutions (call.replaceFVar x value)))
    for resolved in variants do
      unless resolved.getAppArgs.any isConstructorApp do continue
      let value ← goal.withContext (whnf resolved)
      if value == resolved || value.hasLooseBVars then continue
      let equation ← goal.withContext (mkEq resolved value)
      if added.contains equation || existing.contains equation then continue
      added := added.insert equation
      let proof ← goal.withContext do
        mkExpectedTypeHint (← mkEqRefl resolved) equation
      let (_, next) ← goal.note (← mkFreshUserName `callInstance) proof
      goal := next
  replaceMainGoal [goal]

/-- Expose the wrappers not described by a summary, until none is left. -/
private def exposeLayers (summaries : Array Expr) : TacticM Unit := do
  let mut previous : Option (Array Expr) := none
  for _ in [:4] do
    let current ← expressions
    if previous == some current then return
    previous := some current
    let discovery ← withMainContext <| discoverKeeping summaries
      (current.flatMap (·.getUsedConstants))
    if discovery.wrappers.isEmpty then return
    exposeSource discovery

private def replaceObserved (entries : Array Observed.Entry) : TacticM Unit := do
  let mut goal ← getMainGoal
  let premises ← goal.withContext do
    let mut result := #[]
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        result := result.push declaration.fvarId
    return result
  for premise in premises do
    let original ← goal.withContext (premise.getType)
    let type := Observed.replace entries original
    unless type == original do goal ← goal.replaceLocalDeclDefEq premise type
  let original ← goal.withContext (goal.getType)
  let target := Observed.replace entries original
  unless target == original do goal ← goal.replaceTargetDefEq target
  replaceMainGoal [goal]

/-- Quantified induction hypotheses are instantiated before a leaf. A
quantified proposition used as another premise's antecedent is still higher
order; sending that whole implication to scalar call abstraction both hides
the useful instances and leaves recursive calls under binders. Omitting it
asks for a stronger leaf, never assumes its antecedent. -/
private partial def finitePremise (type : Expr) : MetaM Bool := do
  if type.isForall then
    return ← forallTelescope type fun arguments body => do
      for argument in arguments do
        let domain ← inferType argument
        unless (← isProp domain) && (← finitePremise domain) do return false
      finitePremise body
  if type.isAppOf ``Exists then return false
  if #[``And, ``Or, ``Not, ``Iff].any type.isAppOf then
    return ← type.getAppArgs.allM finitePremise
  return true

/-- One-step defining equations of the recursive definitions at the calls a
leaf contains (`ascending p l = match l with | [] => true | (k, _) :: r =>
above p k && ascending (some k) r`), instantiated from Lean's unfolding
theorems. The solver keeps each recursive definition uninterpreted; unfolded
by the solver itself, a definition over symbolic data recurses without bound.
Nothing is assumed: each hypothesis is an instance of a proved theorem. -/
private def unfoldingEquations (names : Array Name) (limit : Nat := 48) : TacticM Unit := do
  let mut goal ← getMainGoal
  let expressions ← goal.withContext do
    let mut result := #[← goal.getType]
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        result := result.push declaration.type
    return result
  let calls ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  for expression in expressions do
    expression.forEach fun node => do
      if node.hasLooseBVars || !node.isApp || (← seen.get).contains node then return
      let .const name _ := node.getAppFn | return
      unless names.contains name do return
      seen.modify (·.insert node)
      calls.modify (·.push node)
  let mut added := 0
  for call in ← calls.get do
    if added ≥ limit then break
    let .const name _ := call.getAppFn | continue
    let some equation ← getUnfoldEqnFor? name (nonRec := true) | continue
    let proof? ← goal.withContext do
      try
        let theorem_ ← mkConstWithFreshMVarLevels equation
        let (args, _, type) ← forallMetaTelescope (← inferType theorem_)
        let some (_, left, _) := type.eq? | return none
        unless ← isDefEq left call do return none
        let proof ← instantiateMVars (mkAppN theorem_ args)
        if proof.hasMVar then return none
        return some proof
      catch _ => return none
    let some proof := proof? | continue
    let (_, next) ← goal.note (← mkFreshUserName `callInstance) proof
    goal := next
    added := added + 1
  replaceMainGoal [goal]

private def leafCore (config : Blaster.Options.BlasterOptions)
    (recursive : Array Name) : TacticM Unit := do
  -- one-step meanings of every recursive definition the leaf calls
  let used ← withMainContext do
    let mut names : Std.HashSet Name := {}
    let goal ← getMainGoal
    let mut expressions := #[← goal.getType]
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        expressions := expressions.push declaration.type
    for expression in expressions do
      for name in expression.getUsedConstants do
        if primitive name || names.contains name then continue
        if (← getFunIndInfo? false true name).isSome || (← isRecursiveDefinition name) then
          names := names.insert name
    return names.toArray
  unfoldingEquations used
  withMainContext do
  let goal ← getMainGoal
  let mut hypotheses := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || !(← isProp declaration.type) then continue
    trace[Blaster.induction] "available {declaration.userName}: {declaration.type}"
    let finite ← finitePremise declaration.type
    -- An equation between decidability instances (left by a case split on a
    -- lowered `if`) carries no first-order content.
    let instanceEquation ← match declaration.type.eq? with
      | some (type, _, _) => do pure ((← whnf type).isAppOf ``Decidable)
      | none => pure false
    if finite && !instanceEquation then hypotheses := hypotheses.push declaration.toExpr
  -- Local definitions (for example `do`-notation join points introduced by
  -- `intros`) are not hypotheses: substitute their values so that the solver
  -- sees the definitions instead of arbitrary functions.
  let target ← zetaReduce (← instantiateMVars (← mkForallFVars hypotheses (← goal.getType)))
  trace[Blaster.induction] "leaf: {target}"
  let functions ← IO.mkRef (#[] : Array Expr)
  target.forEach fun expression => do
    if expression.isFVar then
      if (← inferType expression).isForall && !(← isProp (← inferType expression)) then
        functions.modify (·.push expression)
    if let .const name _ := expression then
      if recursive.contains name then
        functions.modify (·.push expression)
  -- every recursive definition the leaf mentions, not only the ones the
  -- search tracks: a recursive definition left to the translation is unfolded
  -- by the solver over symbolic data without bound (`ascending prev l` alone
  -- exhausts memory while the goal is being asserted)
  for name in target.getUsedConstants do
    if (← getFunIndInfo? false true name).isSome || (← isRecursiveDefinition name) then
      if !primitive name then functions.modify (·.push (mkConst name))
  let functions := (Std.HashSet.ofArray (← functions.get)).toArray
  -- Recursive (and opaque) definitions are uninterpreted for the solver: one
  -- symbol per function, shared by its closed calls and by the calls under
  -- binders (a match alternative reading a lookup result). Abstracting only
  -- the closed calls, while the translation defines the function recursively
  -- for the others, gives one function two unrelated symbols, and every
  -- countermodel that separates them is spurious. The symbol keeps the
  -- definition's constructor equations: a case split inside the solver may
  -- turn `get? t merged` into `get? t []`. Local function variables are
  -- still abstracted call by call.
  let (constants, locals) := functions.partition (·.isConst)
  let names := constants.map (·.constName!)
  -- plain uninterpreted symbols: the constructor equations the solver
  -- needs are stated as hypotheses (`constructorEquations`); reducing
  -- them inside the optimizer would only erase those hypotheses
  let proof ← Local.abstractApplications target locals
    (fun abstracted => Optimize.withUninterpretedFunctions names
      (Solver.prove abstracted config)) true
  goal.assign (mkAppN proof hypotheses)
  replaceMainGoal []

/-- Failures of the leaf that no solver call was involved in: the abstraction
(`Local.abstractApplications`) or the translation (`translateApp`) rejected the
goal's shape. Recognized by their messages, which these modules own. -/
private def staticFailure (error : Exception) : IO Bool := do
  let message ← error.toMessageData.toString
  return (message.splitOn "escapes as a value").length > 1 ||
    (message.splitOn "translateApp").length > 1 ||
    (message.splitOn "external call abstraction").length > 1

private def leaf (config : Blaster.Options.BlasterOptions) (summaries : Array Expr)
    (recursive : Array Name) : TacticM Unit := do
  -- Summaries are instantiated while the calls they describe are visible
  -- (`exposeLayers` keeps those wrappers folded); the solver then gets every
  -- closed wrapper call unfolded, with the recursive calls this reveals on
  -- constructors reduced by their equations.
  -- (the leaf's own instances are discarded with the leaf's state on failure,
  -- so they are not recorded as generated)
  exposeLayers summaries
  CallInstances.instantiate 4 summaries (virtual := constructorFlows)
  let discovery ← withMainContext <| Source.discover
    ((← expressions).flatMap (·.getUsedConstants))
  let mut recursive := recursive
  unless discovery.wrappers.isEmpty do
    exposeSource discovery (delta := true)
    CallInstances.instantiate 2 summaries (virtual := constructorFlows)
    recursive ← withMainContext <| recursiveNames (← expressions)
    normalize recursive
    if (← getGoals).isEmpty then return
  constructorEquations (recursive ++ discovery.recursive) (← constructorFlows)
  leafCore config recursive

private def induct (call : Call) : TacticM Unit := withMainContext do
  let expression ← Term.exprToSyntax call.expression
  let mut fixed : FVarIdSet := {}
  for argument in call.expression.getAppArgs do
    for localId in (collectFVars {} argument).fvarIds do fixed := fixed.insert localId
  let mut generalized := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || fixed.contains declaration.fvarId ||
        (← isProp declaration.type) || declaration.isLet then continue
    if declaration.binderInfo == .instImplicit then continue
    generalized := generalized.push (mkIdent declaration.userName)
  trace[Blaster.induction] "inducting on {call.expression}"
  if generalized.isEmpty then
    evalTactic (← `(tactic| fun_induction $expression))
  else
    evalTactic (← `(tactic| fun_induction $expression generalizing $generalized:ident*))

private def splitOne : TacticM Unit := do
  let saved ← saveState
  try
    if let some goals ← splitTarget? (← getMainGoal) then
      replaceMainGoal goals
      return
  catch _ => pure ()
  saved.restore
  withMainContext do
    -- A monadic bind on an unknown value of an inductive monad (`Except`,
    -- `Option`, ...) hides the continuation, often including recursive calls,
    -- under a binder. Split on the bound value first: the matches inside
    -- hypotheses (instantiated facts) would otherwise be split forever.
    let binds ← IO.mkRef (#[] : Array Expr)
    for expression in ← expressions do
      expression.forEach fun node => do
        if node.hasLooseBVars || !node.isAppOfArity ``Bind.bind 6 then return
        let value := node.getArg! 4
        unless value.hasFVar && !value.hasMVar do return
        if (← isConstructorApp'? (← whnfR value)).isSome then return
        let .const typeName _ := (← whnf (← inferType value)).getAppFn | return
        let .inductInfo _ ← getConstInfo typeName | return
        binds.modify (·.push value)
    let casesOn := fun (major : Expr) => do
      let goal ← getMainGoal
      let (major, goal) ← if major.isFVar then pure (major.fvarId!, goal) else do
        let hypotheses ← (← getLCtx).foldlM (init := #[]) fun hypotheses declaration => do
          return if ← isProp declaration.type then hypotheses.push declaration.fvarId else hypotheses
        let (_, variables, goal) ← goal.generalizeHyp
          #[{expr := major, hName? := some (← mkFreshUserName `caseValue)}] hypotheses
        pure (variables[0]!, goal)
      let branches ← goal.cases major
      replaceMainGoal (branches.toList.map (·.mvarId))
    for major in ← binds.get do
      let saved ← saveState
      try
        casesOn major
        return
      catch _ => saved.restore
    for declaration in ← getLCtx do
      unless !declaration.isImplementationDetail && (← isProp declaration.type) do continue
      let saved ← saveState
      try
        -- Generated arrows have inaccessible binder names. Address the
        -- actual local declaration, not a re-elaborated spelling of its name.
        if let some goals ← splitLocalDecl? (← getMainGoal) declaration.fvarId then
          replaceMainGoal goals
          return
      catch _ => pure ()
      saved.restore
    -- Definitional exposure may lower a surface match to `casesOn`/`rec`.
    -- Lean's `split` searches matcher declarations only. Recover the major
    -- premise from the recursor metadata and use ordinary checked cases.
    let candidates ← IO.mkRef (#[] : Array Expr)
    for expression in ← expressions do
      expression.forEach fun node => do
        if node.hasLooseBVars then return
        let .const name _ := node.getAppFn | return
        let major? ← if let some matcher ← matchMatcherApp? node (alsoCasesOn := true) then
            pure matcher.discrs[0]?
          else match ← getConstInfo name with
            | .recInfo info => pure node.getAppArgs[info.getMajorIdx]?
            | _ => pure none
        if let some major := major? then
          if major.hasFVar && !major.hasMVar then candidates.modify (·.push major)
    for major in ← candidates.get do
      let saved ← saveState
      try
        casesOn major
        return
      catch _ => saved.restore
    throwError "no conditional or match to split"

private partial def solve (config : Blaster.Options.BlasterOptions)
    (summaries : Array Expr) (used : Array Name)
    (remaining : Nat) (budget : IO.Ref Nat) (generated : CallInstances.Generated) : TacticM Unit := do
  if (← budget.get) == 0 then throwError "blaster induction: proof-search goal limit reached"
  budget.modify (· - 1)
  evalTactic (← `(tactic| intros))
  let input ← expressions
  let recursive ← withMainContext <| recursiveNames input
  let reducible ← withMainContext do
    if used.isEmpty then structuralNames recursive else pure recursive
  normalize reducible
  if (← getGoals).isEmpty then return
  -- Induction and constructor reduction can reveal wrappers absent from the
  -- original goal (for example a per-row check inside a list traversal).
  -- Expose these ordinary nonrecursive definitions before abstracting their
  -- recursive callees; otherwise their input constraints remain hidden.
  exposeLayers summaries
  -- Exposure can reveal recursive calls on constructors (for example a
  -- lookup wrapper applied to a cons cell): reduce them by their equations.
  let recursive ← withMainContext <| recursiveNames (← expressions)
  let reducible ← withMainContext do
    if used.isEmpty then structuralNames recursive else pure recursive
  normalize reducible
  if (← getGoals).isEmpty then return
  let recursive ← withMainContext <| recursiveNames (← expressions)
  -- Instances of the summaries at the calls visible now persist into the case
  -- splits and inductions below (a wrapper fact instantiated before the
  -- wrapper's call is unfolded and split).
  unless summaries.isEmpty do
    let discovery ← withMainContext <| Source.discover ((← expressions).flatMap (·.getUsedConstants))
    let wrapperFacts ← withMainContext <| summaries.filterM fun summary => do
      return (← inferType summary).getUsedConstants.any discovery.wrappers.contains
    unless wrapperFacts.isEmpty do
      CallInstances.instantiate 2 wrapperFacts (generated? := some generated)
  let saved ← saveState
  let failure ← try
      leaf config summaries recursive
      return
    catch error =>
      saved.restore
      pure error
  if remaining == 0 then throw failure
  -- A nonrecursive wrapper can constrain the input to a concrete constructor.
  -- Expose that constraint before choosing an induction: inducting on a
  -- downstream lookup first invents an unnecessarily weak tail hypothesis.
  let splitAndRecurse : TacticM Bool := do
    let saved ← saveState
    try
      splitOne
      let goals ← getGoals
      for goal in goals do
        setGoals [goal]
        solve config summaries used (remaining - 1) budget generated
      setGoals []
      return true
    catch _ =>
      saved.restore
      return false
  if ← splitAndRecurse then return
  -- The leaf rejected the goal's shape (a recursive call hidden under a
  -- binder) and nothing visible can be split: the wrappers kept folded for
  -- the summaries must be unfolded now, so that a case split can reach that
  -- binder. Splitting what is visible came first, so that a summary's call
  -- closed by such a split is instantiated before its wrapper disappears.
  if ← staticFailure failure then
    let saved ← saveState
    let full ← withMainContext <| Source.discover ((← expressions).flatMap (·.getUsedConstants))
    unless full.wrappers.isEmpty do
      exposeSource full
      let recursive ← withMainContext <| recursiveNames (← expressions)
      normalize recursive
      if (← getGoals).isEmpty then return
      if ← splitAndRecurse then return
      saved.restore
  let candidates ← withMainContext <| calls (← expressions)
  for call in candidates do
    let name := call.expression.getAppFn.constName!
    if used.contains name then continue
    let saved ← saveState
    try
      induct call
      let goals ← getGoals
      for goal in goals do
        setGoals [goal]
        solve config summaries (used.push name) (remaining - 1) budget generated
      setGoals []
      return
    catch error =>
      trace[Blaster.induction] "candidate {name} failed: {error.toMessageData}"
      saved.restore
  throwError "blaster induction could not prove the goal from ordinary facts.\n\
    No program-specific invariant or recursive-call property was assumed.\n{failure.toMessageData}"

/-- Prove the existing goal. Unlike annotated verification this takes no
program description and no externally constructed invariant candidates. -/
def run (summaries : Array Expr) (config : Blaster.Options.BlasterOptions) : TacticM Unit := focus do
  if config.onlyOptimize || config.onlySmtLib || config.solveResult != .ExpectedValid then
    throwError "blaster induction requires solving with expected result Valid"
  for summary in summaries do
    unless !summary.hasExprMVar && !summary.hasSorry && (← isProp (← inferType summary)) do
      throwError "blaster induction summaries must be ordinary, fully elaborated proofs"
  let budget ← IO.mkRef (blaster.induction.maxGoals.get (← getOptions))
  normalize #[]
  if (← getGoals).isEmpty then return
  let discovery ← withMainContext do
    Source.discover ((← expressions).flatMap Expr.getUsedConstants)
  -- Registered library facts about the definitions this goal reaches join the
  -- supplied summaries. They were audited when registered.
  -- one step into the recursive definitions the goal reaches: a fact about
  -- `valueOf` concerns a goal about a recursive sum of `valueOf`s (a full
  -- closure would make nearly every registered fact relevant)
  let reachable ← discovery.recursive.foldlM (init := #[]) fun acc name => do
    match (← getEnv).find? name with
    | some (.defnInfo info) => return acc ++ info.value.getUsedConstants
    | _ => return acc
  let direct := discovery.recursive ++ discovery.wrappers ++ discovery.predicates
  let library ← Library.relevant direct
  let library := library ++ (← Library.relevantCovered (direct ++ reachable)).filter (!library.contains ·)
  let summaries := summaries ++ library.filter (!summaries.contains ·)
  prependError m!"while exposing recursive source calls:\n" <| exposeLayers summaries
  evalTactic (← `(tactic| intros))
  let observed ← prependError m!"while discovering execution observations:\n" <| withMainContext do
    Observed.discover (← expressions) discovery.recursive
  prependError m!"while replacing execution observations:\n" <| replaceObserved observed.entries
  Term.withoutErrToSorry <| solve config summaries #[]
    (blaster.induction.maxDepth.get (← getOptions)) budget (← IO.mkRef {})

end Blaster.Proof.Induction
