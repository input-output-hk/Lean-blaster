import Blaster.Proof.Verification.Solver

/-! Strengthen a goal before it is sent to the solver: drop premises that are
disconnected from the conclusion, and replace external calls by arbitrary
values. Each proves a stronger statement and instantiates it; nothing about
the calls is assumed. -/
namespace Blaster.Proof.Verification.Local
open Lean Meta Elab

/-- First try the stronger implication obtained by discarding assumptions in
components disconnected from the conclusion. This is particularly useful
after call abstraction: irrelevant bookkeeping arguments no longer connect to
the result. No premise is proved by this pass. If the stronger goal fails (an
independent contradictory component can matter), restore and use all premises. -/
def solveConnected (target : Expr) (solve : Expr → TermElabM Expr) : TermElabM Expr := do
  let reduced ← forallTelescope target fun arguments body => do
    unless ← arguments.allM (fun argument => do isProp (← inferType argument)) do return none
    let types ← arguments.mapM fun argument => inferType argument
    let dependencies := types.map fun type => (collectFVars {} type).fvarIds
    let mut relevant := (collectFVars {} body).fvarSet
    let mut selected := Array.replicate arguments.size false
    let mut changed := true
    while changed do
      changed := false
      for index in [:arguments.size] do
        if selected[index]! then continue
        if dependencies[index]!.isEmpty || relevant.contains arguments[index]!.fvarId! ||
            dependencies[index]!.any relevant.contains then
          selected := selected.set! index true
          for dependency in dependencies[index]! do relevant := relevant.insert dependency
          changed := true
    let kept := arguments.zipIdx.filterMap fun (argument, index) =>
      if selected[index]! then some argument else none
    if kept.size == arguments.size then return none
    let saved ← saveState
    try
      let filtered ← mkForallFVars kept body
      -- Opening the telescope put every original premise in the ambient
      -- context. Remove them all before asking the solver to prove the new
      -- implication; otherwise a supposedly omitted premise could leak in.
      let mut context ← getLCtx
      for argument in arguments do context := context.erase argument.fvarId!
      let instances := (← getLocalInstances).filter fun instance_ =>
        !arguments.contains instance_.fvar
      let proof ← withLCtx context instances (solve filtered)
      if proof.hasSorry || (← MonadLog.hasErrors) then throwError "connected implication did not close"
      return some (← mkLambdaFVars arguments (mkAppN proof kept))
    catch _ =>
      saved.restore
      return none
  if let some proof := reduced then return proof
  solve target

/-- Replace closed-under-binders external applications with arbitrary local
values, prove the stronger formula, then instantiate those values with the real
applications. Identical calls share one variable. With `congruent`, finite
argument-equality implications are proved in Lean and supplied to the solver;
otherwise different calls need not even satisfy congruence. Neither mode
assumes application-specific behavior. No higher-order continuation is sent to SMT. -/
def abstractApplications (target : Expr) (functions : Array Expr)
    (solve : Expr → TermElabM Expr) (congruent : Bool := false) : TermElabM Expr := do
  let mut calls := #[]
  let mut types := #[]
  let mut seen : Std.HashSet Expr := {}
  let candidates ← IO.mkRef (#[] : Array Expr)
  target.forEach fun expression => do
    if expression.isApp && functions.contains expression.getAppFn && !expression.hasLooseBVars then
      candidates.modify (·.push expression)
  -- calls that differ only in implicit arguments (an abbreviation against its
  -- unfolding, say) denote the same value: they share one result
  let mut aliases : Std.HashMap Expr Expr := {}
  for expression in ← candidates.get do
    if seen.contains expression then continue
    seen := seen.insert expression
    let type ← inferType expression
    if type.isForall then continue
    if type.hasFVar || type.hasLooseBVars || (type.isSort && type != mkSort levelZero) then
      throwError "external call abstraction requires a closed value type or Prop"
    let mut representative? := none
    for call in calls do
      if call.getAppFn == expression.getAppFn && call.getAppNumArgs == expression.getAppNumArgs then
        if ← withTransparency .instances (isDefEq call expression) then
          representative? := some call
          break
    match representative? with
    | some call => aliases := aliases.insert expression call
    | none =>
      calls := calls.push expression
      types := types.push type
  let mut congruences := #[]
  if congruent then
    for leftIndex in [:calls.size] do
      for rightIndex in [:leftIndex] do
        let left := calls[leftIndex]!
        let right := calls[rightIndex]!
        unless left.getAppFn == right.getAppFn && left.getAppNumArgs == right.getAppNumArgs do continue
        -- Instances of a polymorphic function at different types are unrelated.
        unless ← isDefEq (← inferType left) (← inferType right) do continue
        let mut equalities := #[]
        let mut supported := true
        for (a, b) in left.getAppArgs.zip right.getAppArgs do
          if a == b then continue
          let type ← inferType a
          -- A differing type (or other sort-valued) argument cannot be related by
          -- a first-order congruence: later arguments depend on it.
          if (← whnf type).isSort then supported := false; break
          unless ← isDefEq type (← inferType b) do supported := false; break
          equalities := equalities.push (← mkEq a b)
        unless supported do continue
        let declarations := equalities.mapIdx fun index type =>
          (Name.num `sameArgument index, fun (_ : Array Expr) => pure type)
        let proof ← withLocalDeclsD declarations fun argumentsEqual => do
          let mut equality ← mkEqRefl left.getAppFn
          let mut index := 0
          for (a, b) in left.getAppArgs.zip right.getAppArgs do
            if a == b then equality ← mkAppM ``congrFun #[equality, a]
            else
              equality ← mkAppM ``congr #[equality, argumentsEqual[index]!]
              index := index + 1
          mkLambdaFVars argumentsEqual equality
        congruences := congruences.push proof
  let mut target := target
  for proof in congruences.reverse do target ← mkArrow (← inferType proof) target
  let declarations := types.mapIdx fun index type =>
    (Name.num `externalResult index, fun (_ : Array Expr) => pure type)
  let proof ← withLocalDeclsD declarations fun results => do
    let mut replacements := Std.HashMap.ofList (calls.zip results).toList
    for (alias, call) in aliases.toList do
      if let some result := replacements[call]? then replacements := replacements.insert alias result
    let abstracted := target.replace fun expression => replacements.get? expression
    if let some escaped := abstracted.find? functions.contains then
      throwError "external function escapes as a value or under a binder; expose its call first: {escaped}"
    -- Captured environments can contain large unrelated datatypes. They are
    -- not part of this obligation once their calls have been abstracted.
    let mut dependencies := collectFVars {} abstracted
    let instances ← getLocalInstances
    for localInstance in instances do
      dependencies := collectFVars dependencies localInstance.fvar
    let mut next := 0
    while next < dependencies.fvarIds.size do
      let declaration ← dependencies.fvarIds[next]!.getDecl
      dependencies := collectFVars dependencies declaration.type
      if let some value := declaration.value? then dependencies := collectFVars dependencies value
      next := next + 1
    let mut context ← getLCtx
    for declaration in ← getLCtx do
      unless dependencies.fvarSet.contains declaration.fvarId do
        context := context.erase declaration.fvarId
    let proof ← withLCtx context instances (solve abstracted)
    mkLambdaFVars results proof
  return mkAppN (proof.beta calls) congruences

end Blaster.Proof.Verification.Local
