import Lean

/-!
# Decomposing success hypotheses

A hypothesis `f args = C fields` whose right side is a data constructor (for
example `lookup ctx = some (key, value)`) says that a computation succeeded.
Unfolding the non-recursive definitions it mentions, and inverting the
option/list/constructor steps of that computation, turns it into equations
about the inputs: the shape a decoded argument must have, the element a list
lookup returns, the fields a record carries. Exploration can then use those
equations (substituted, or as rewrites) instead of rediscovering the facts
along the program's own path, where the correlation with the hypothesis is
otherwise lost.

Every step is an ordinary tactic on the goal (`simp only` with standard
lemmas, `cases`, `split`, `subst`), so the result is checked by Lean; a step
that does not apply leaves the goal unchanged.
-/
namespace Blaster.Proof.Explore.Success
open Lean Meta Elab Tactic

/-- Is `type` an equation whose right side is a constructor carrying data
(not a Boolean or proposition)? -/
def successEquation? (type : Expr) : MetaM Bool := do
  let some (ty, _, rhs) := type.eq? | return false
  let ty ← whnf ty
  if ty.isConstOf ``Bool || ty.isSort then return false
  let .const c _ := rhs.getAppFn | return false
  let some (.ctorInfo info) := (← getEnv).find? c | return false
  return info.numFields > 0

private def unfoldable (name : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? name | return false
  -- the program's definitions, not the core library's (`Int.toNat` stays folded,
  -- as the program's own terms spell it)
  if let some idx := env.getModuleIdxFor? name then
    let module := env.header.moduleNames[idx.toNat]!
    if #[`Init, `Std, `Lean].any (·.isPrefixOf module) then return false
  if isMatcherCore env name then return false
  if (← isRecursiveDefinition name) then return false
  let body := info.type.getForallBody
  if body.isSort then return false
  if let .const cls _ := body.getAppFn then
    if isClass env cls then return false
  return true

private def simpAt (h : FVarId) (extra : Array Name) : TacticM Bool := do
  let goal ← getMainGoal
  let before ← goal.withContext do instantiateMVars (← h.getType)
  let name ← goal.withContext do return (← h.getDecl).userName
  let lemmas : Array Name := #[``Option.bind_eq_some_iff, ``List.head?_eq_some_iff,
    ``Option.map_eq_some_iff, ``Option.some.injEq, ``Prod.mk.injEq, `bind, `reduceCtorEq]
  let lemmas ← (extra ++ lemmas).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let stx ← `(tactic| set_option linter.unusedSimpArgs false in
    simp only [$lemmas,*] at $(mkIdent name):ident)
  try
    evalTactic stx
  catch _ => return false
  if (← getGoals).isEmpty then return true
  let after? ← (← getMainGoal).withContext do
    match (← getLCtx).findFromUserName? name with
    | some d => return some (← instantiateMVars d.type)
    | none => return none
  return after? != some before

/-- One decomposition step on some success hypothesis; `false` when nothing applies. -/
private partial def step (protected_ : Array Name) : TacticM Bool := do
  let goal ← getMainGoal
  let candidates ← goal.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || protected_.contains d.userName then continue
      let type ← instantiateMVars d.type
      if !(← isProp type) then continue
      out := out.push (d.fvarId, d.userName, type)
    return out
  for (h0, name0, type) in candidates do
    -- tactic text needs an accessible name
    let (h, name) ← if name0.hasMacroScopes || (toString name0).any (· == '✝') then do
        let g ← getMainGoal
        let used ← g.withContext do
          return (← getLCtx).foldl (init := ({} : NameSet)) fun acc d => acc.insert d.userName
        let mut k := 0
        while used.contains (Name.mkSimple s!"hSuccess{k}") do k := k + 1
        let plain := Name.mkSimple s!"hSuccess{k}"
        replaceMainGoal [← g.rename h0 plain]
        pure (h0, plain)
      else pure (h0, name0)
    let goal ← getMainGoal
    -- existentials and conjunctions: destructure
    if type.isAppOf ``Exists || type.isAppOf ``And then
      let goals ← goal.cases h
      if h1 : goals.size = 1 then
        replaceMainGoal [goals[0].mvarId]
        return true
    let some (_, lhs, rhs) := type.eq? | continue
    -- `x = e` or `e = x` with a variable: substitute
    if lhs.isFVar && !rhs.containsFVar lhs.fvarId! then
      try replaceMainGoal [← goal.withContext (subst goal h)]; return true catch _ => pure ()
    if rhs.isFVar && !lhs.containsFVar rhs.fvarId! then
      try replaceMainGoal [← goal.withContext (subst goal h)]; return true catch _ => pure ()
    unless ← goal.withContext (successEquation? type) do continue
    -- a match on the left: split it, closing the impossible alternatives
    if (← goal.withContext (matchMatcherApp? lhs)).isSome then
      let saved ← saveState
      try
        evalTactic (← `(tactic| split at $(mkIdent name):ident))
        let mut remaining := #[]
        for g in ← getGoals do
          setGoals [g]
          let hNew ← g.withContext do return (← getLCtx).findFromUserName? name
          if let some d := hNew then discard <| simpAt d.fvarId #[]
          remaining := remaining ++ (← getGoals)
        if remaining.size == 1 then
          setGoals remaining.toList
          return true
        saved.restore
      catch _ => saved.restore
      continue
    -- unfold the non-recursive definitions it mentions
    let defs ← goal.withContext do
      lhs.getUsedConstants.filterM fun n => unfoldable n
    if !defs.isEmpty then
      if ← simpAt h defs then return true
    -- a record variable whose field the left side reads: split the record
    let record? ← goal.withContext do
      let found ← IO.mkRef (none : Option FVarId)
      lhs.forEach fun t => do
        if (← found.get).isSome then return
        let s? : Option Expr ← match t with
          | .proj _ _ s => pure (some s)
          | .app .. => do
            let .const fn _ := t.getAppFn | pure none
            let some info := (← getEnv).getProjectionFnInfo? fn | pure none
            let args := t.getAppArgs
            pure (if args.size == info.numParams + 1 then some args[info.numParams]! else none)
          | _ => pure none
        let some s := s? | return
        unless s.isFVar do return
        let ty ← whnf (← inferType s)
        let .const n _ := ty.getAppFn | return
        if isStructure (← getEnv) n then found.set (some s.fvarId!)
      found.get
    if let some r := record? then
      let goals ← goal.cases r
      if h1 : goals.size = 1 then
        replaceMainGoal [goals[0].mvarId]
        return true
  return false

/-- Decompose the success hypotheses of the main goal, leaving `protected_`
hypotheses untouched. Stops when no step applies (or after `fuel` steps). -/
def decompose (protected_ : Array Name) (fuel : Nat := 64) : TacticM Unit := do
  for _ in [:fuel] do
    if (← getGoals).length != 1 then return
    unless ← step protected_ do return

end Blaster.Proof.Explore.Success
