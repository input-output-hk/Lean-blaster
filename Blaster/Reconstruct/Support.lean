import Lean
import Blaster.Reconstruct.Lemmas
import Blaster.Reconstruct.Profile
import Blaster.Reconstruct.SmtProof.Local

/-!
Shared proof-elaboration utilities extracted from Seungheon Oh's reconstruction work.
This module contains no optimizer evidence types or optimizer proof reconstruction.
-/
open Lean Meta Elab Term Tactic
namespace Blaster.Reconstruct
def dischargeHeartbeats : Nat := 50000

/-- Return `true` if an attempt that consumed `used` heartbeats exhausted its budget of `budget` thousand heartbeats
    (at least 90%, see `withHeartbeatBudget`). -/
def budgetExhausted (budget used : Nat) : Bool := 10 * used ≥ 9 * budget * 1000

/-- Execute `x` with a fresh heartbeat budget of `n` thousand heartbeats. -/
@[inline] def withHeartbeatBudget [Monad m] [MonadWithReaderOf Core.Context m] [MonadLiftT BaseIO m]
  [MonadControlT CoreM m] (n : Nat) (x : m α) : m α :=
  withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n * 1000 }) x

/-- Maximum recursion depth allowed for each discharge attempt. -/
def dischargeMaxRecDepth : Nat := 8192

/-- Execute `x` within a bounded resource budget (heartbeats and recursion depth) and return `none`
    on any exception, including runtime exceptions (e.g., heartbeats or maximum recursion depth).
    The state is restored on failure.
-/
def attempt [Monad m] [MonadBacktrack s m] [MonadExcept Exception m] [MonadRuntimeException m]
  [MonadWithReaderOf Core.Context m] [MonadLiftT BaseIO m] [MonadControlT CoreM m]
  [MonadStateOf Core.State m]
  (budget : Nat) (x : m (Option α)) : m (Option α) := do
  let st ← saveState
  -- NOTE: asynchronous subtasks spawned by a failed attempt (e.g., the on-demand generation of
  -- auxiliary lemmas) are discarded, such that their errors are not reported.
  let tasks := (← getThe Core.State).snapshotTasks
  let failed : m (Option α) := do
    restoreState st
    modifyThe Core.State fun s => { s with snapshotTasks := tasks }
    return none
  tryCatchRuntimeEx
    (do
      let r ← withHeartbeatBudget budget <|
        withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := dischargeMaxRecDepth }) x
      if r.isNone then failed else return r)
    (fun _ => failed)

/-- `x`, with its interrupt exceptions (not caught by `try`/`catch`, see `Core.tryCatch`) handled by `h`. -/
def catchInterrupt (x h : CoreM α) : CoreM α := fun ctx s => do
  try x ctx s catch ex => if ex.isInterrupt then h ctx s else throw ex

/-- `x` interrupted after `ms` milliseconds (checked by `checkSystem`, e.g., in `whnf`, `isDefEq` and `simp`):
    `none` when interrupted, with the state restored. It is also interrupted when the cancellation token of the context
    is set (e.g., the attempts of a parallel portfolio, see `SmtProof.portfolioPar`). -/
def withTimeLimit (ms : Nat) (x : TermElabM (Option α)) : TermElabM (Option α) := do
  let tk ← IO.CancelToken.new
  let outer? := (← readThe Core.Context).cancelTk?
  let finished ← IO.mkRef false
  let deadline := (← IO.monoMsNow) + ms
  let _ ← IO.asTask (prio := .dedicated) do
    repeat
      let now ← IO.monoMsNow
      if now ≥ deadline || (← finished.get) then break
      if let some outer := outer? then
        if ← outer.isSet then break
      IO.sleep (min 10 (deadline - now)).toUInt32
    tk.set
  let s ← saveState
  let info ← getInfoState
  let tasks := (← getThe Core.State).snapshotTasks
  let interrupted : TermElabM (Option α) := do
    s.restore
    setInfoState info
    modifyThe Core.State fun st => { st with snapshotTasks := tasks }
    return none
  try
    controlAt CoreM fun runInBase =>
      catchInterrupt (withReader (fun ctx => { ctx with cancelTk? := some tk }) (runInBase x)) (runInBase interrupted)
  finally finished.set true

/-- Implementation of `dependsOnSorry`.
    NOTE: Each expression is traversed by the native `Expr.findExt?` (whose cache of visited shared subterms is
    much more efficient than the one of `Expr.getUsedConstants`, i.e., on large proofs), the constants of the
    current module being recorded on the fly.
-/
unsafe def dependsOnSorryImpl (env : Environment) (prf : Expr) (checked : Array (Name × Expr)) : BaseIO Bool := do
  let checkedValues : Std.HashMap Name Expr := checked.foldl (fun m (n, v) => m.insert n v) {}
  let found ← IO.mkRef (#[] : Array Name)
  let step (s : Expr) : Expr.FindStep :=
    match s with
    | .const c _ =>
        if c == ``sorryAx then .found
        else if (env.getModuleIdxFor? c).isSome then .done
        else unsafeBaseIO do found.modify (·.push c); return .done
    | _ => .visit
  let mut visited : NameHashSet := {}
  let mut todo : Array Expr := #[prf]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if (e.findExt? step).isSome then return true
    for c in ← found.swap #[] do
      if visited.contains c then continue
      visited := visited.insert c
      let some info := env.find? c | continue
      let value? := info.value? (allowOpaque := true)
      if let some v := value? then
        if checkedValues.get? c |>.any (ptrEq v ·) then continue
        todo := todo.push v
      todo := todo.push info.type
  return false

@[implemented_by dependsOnSorryImpl]
private opaque dependsOnSorryAux (env : Environment) (prf : Expr) (checked : Array (Name × Expr)) : BaseIO Bool

/-- Return `true` if `prf` depends on `sorryAx`, directly or through an auxiliary declaration of the current
    module (e.g., a matcher created by `nomatch` after an elaboration error). The declarations of `checked`
    (with their values) are known not to depend on `sorryAx` (see `Blaster.Reconstruct.checkedProof`).
    NOTE: Imported declarations are not traversed.
-/
def dependsOnSorry (prf : Expr) (checked : Array (Name × Expr) := #[]) : MetaM Bool := do
  dependsOnSorryAux (← getEnv) prf checked

/-- Try to close goal `type` with tactic `tac`. The elaboration state is restored on failure. -/
def proveWithTactic (type : Expr) (tac : TSyntax `tactic) (budget := dischargeHeartbeats) : TermElabM (Option Expr) := do
  let s ← saveState
  -- NOTE: info trees and messages produced by internal tactic runs are discarded (e.g., linters
  -- would process the info trees).
  let infoState ← getInfoState
  let msgs ← Core.getMessageLog
  -- NOTE: Diagnostics reported asynchronously during an attempt (e.g., failures when generating the
  -- equations of a matcher via `realizeConst`) are discarded, as they don't affect the resulting proof.
  let tasks := (← getThe Core.State).snapshotTasks
  -- NOTE: an attempt logging an error (e.g., an elaboration error recovered with `sorry`) is rejected
  Core.setMessageLog {}
  let r ← try
      attempt budget do
        let mvar ← mkFreshExprMVar type
        -- NOTE: asynchronous elaboration is disabled such that kernel errors on auxiliary declarations
        -- created by tactics are reported as exceptions instead of messages.
        let gs ← withOptions (fun o => Elab.async.set o false) <|
                   withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
        let prf ← instantiateMVars mvar
        if !gs.isEmpty || prf.hasMVar || prf.hasSorry then return none
        if ← dependsOnSorry prf then return none
        if (← Core.getMessageLog).hasErrors then return none
        return some prf
    finally modifyThe Core.State fun st => { st with snapshotTasks := tasks }
  if r.isNone then s.restore
  setInfoState infoState
  Core.setMessageLog msgs
  return r

def isUserDefinition (env : Environment) (n : Name) : Bool := Id.run do
  let some info := env.find? n | return false
  if !info.isDefinition || isAuxRecursor env n || isMatcherCore env n then return false
  match env.getModuleIdxFor? n with
  | none => return true
  | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      return !([`Init, `Lean, `Std, `Lake, `Blaster].contains mod.getRoot)

syntax (name := blasterUnfoldUser) "blaster_unfold_user" : tactic

/-- Unfold (up to 5 rounds) the user definitions occurring in the main goal and its hypotheses. -/
@[tactic blasterUnfoldUser] def evalBlasterUnfoldUser : Tactic := fun _ => do
  let env ← getEnv
  for _ in [0:5] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let mut t ← instantiateMVars (← g.getType)
    for d in ← g.withContext getLCtx do
      if !d.isImplementationDetail then t := mkApp t (← instantiateMVars d.type)
    let consts := t.getUsedConstants.filter (isUserDefinition env)
    if consts.isEmpty then return
    -- NOTE: `simp` does not rewrite instance arguments, user instances (e.g., derived `BEq`
    -- instances) are unfolded with `delta` instead.
    let mut insts := #[]
    let mut defs := #[]
    for n in consts do
      if ← isInstance n then insts := insts.push n else defs := defs.push n
    let mut progress := false
    if !insts.isEmpty then
      let ids := insts.map mkIdent
      try
        evalTactic (← `(tactic| delta $ids* at *))
        progress := true
      catch _ => pure ()
    if !defs.isEmpty then
      let lemmas ← defs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      try
        evalTactic (← `(tactic| simp only [$lemmas,*] at *))
        progress := true
      catch _ => pure ()
    if !progress then return

/-- Maximum number of goals produced by `blaster_cases_vars`. -/
def maxCaseGoals : Nat := 128

syntax (name := blasterCasesVars) "blaster_cases_vars" (num)? : tactic
/-- Same as `blaster_cases_vars` but only for variables of non-recursive types (e.g., structures, enumerations). -/
syntax (name := blasterCasesNonRec) "blaster_cases_nonrec" (num)? : tactic

/-- Return the variables of (non-indexed) inductive types in the local context of `g`, together
    with their number of constructors.
-/
def inductiveVars (g : MVarId) (nonRec := false) : MetaM (Array (FVarId × Nat)) := g.withContext do
  let mut vars := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR d.type
    let .const n _ := t.getAppFn | continue
    let .inductInfo info ← getConstInfo n | continue
    if info.numIndices != 0 || (← isProp d.type) then continue
    -- NOTE: integers are handled by arithmetic decision procedures instead
    if nonRec && (info.isRec || n == ``Int) then continue
    vars := vars.push (d.fvarId, info.ctors.length)
  return vars

/-- Perform case analysis on the variables of inductive types (bounded by `maxCaseGoals`). The fields
    of the constructors are themselves case-analyzed (up to four rounds), e.g., for structures.
-/
def casesVars (maxCaseGoals : Nat) (nonRecOnly : Bool) : TacticM Unit := do
  let mut goals := [← getMainGoal]
  let mut done : Std.HashSet FVarId := {}
  for round in [0:4] do
    let mut progress := false
    let mut newGoals := []
    -- NOTE: goals share the free variables of their common ancestor
    let doneBefore := done
    for g in goals do
      -- NOTE: only fields of non-recursive types are case-analyzed (e.g., not `Nat` fields)
      let vars := (← inductiveVars g (nonRec := nonRecOnly || round > 0)).filter (!doneBefore.contains ·.1)
      let mut gs := [g]
      for (v, nbCtors) in vars do
        if (goals.length + newGoals.length + gs.length) * nbCtors > maxCaseGoals then break
        let mut gs' := []
        for g' in gs do
          -- the variable may have been substituted in some goals
          if !(← g'.withContext (return (← getLCtx).contains v)) then
            gs' := gs' ++ [g']
            continue
          let subgoals ← g'.cases v
          gs' := gs' ++ subgoals.toList.map (·.mvarId)
        gs := gs'
        done := done.insert v
        progress := true
      newGoals := newGoals ++ gs
    goals := newGoals
    if !progress then
      if round == 0 && nonRecOnly then throwError "blaster_cases_nonrec: no variable"
      break
  replaceMainGoal goals

@[tactic blasterCasesVars] def evalBlasterCasesVars : Tactic := fun stx =>
  casesVars (if stx[1].isNone then maxCaseGoals else stx[1][0].toNat) false

@[tactic blasterCasesNonRec] def evalBlasterCasesNonRec : Tactic := fun stx =>
  casesVars (if stx[1].isNone then maxCaseGoals else stx[1][0].toNat) true


def fvarClosure (es : Array Expr) : MetaM (Array LocalDecl) := do
  let collect (e : Expr) : Array FVarId := (Lean.CollectFVars.main e {}).fvarIds
  let mut set : FVarIdSet := {}
  let mut todo : Array FVarId := es.foldl (· ++ collect ·) #[]
  while h : todo.size > 0 do
    let fv := todo[todo.size - 1]
    todo := todo.pop
    if set.contains fv then continue
    set := set.insert fv
    let d ← fv.getDecl
    todo := todo ++ collect d.type ++ ((d.value?.map collect).getD #[])
  return (← getLCtx).decls.toArray.filterMap fun d? => d?.filter (set.contains ·.fvarId)


end Blaster.Reconstruct
