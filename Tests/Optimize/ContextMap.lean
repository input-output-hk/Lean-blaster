import Blaster.Optimize.Env.ContextMap

open Lean Elab Command Blaster.Optimize

-- Compare against the previous list semantics across updates, inactive siblings,
-- scope reactivation, repeated writes, and writes to older ancestor ids.
run_cmd liftIO do
  let key : PtrExpr := ⟨mkConst ``True⟩
  let entry ← IO.mkRef ({} : ContextEntries Nat)
  let m := (ContextMap.empty : ContextMap Nat).insert key entry
  let mut model : List (ContextEntry Nat) := []
  let mut active : ActiveContexts := {}
  for i in [:1000] do
    let id := i % 17
    entry.modify fun es => es.insert id i
    model := (id, i) :: model
    active := (active.insert ((i * 7) % 17)).erase ((i * 11) % 17)
    -- Reinsertion must keep a set rather than duplicating path entries.
    active := active.insert 0 |>.insert 0
    let expected := (model.find? fun e => active.contains e.1).map Prod.snd
    unless (← ContextMap.findRaw m active key) == expected do
      throw <| IO.userError s!"Active lookup differs from list model at {i}"
    let queryId := (i * 13) % 17
    let expectedId := (model.find? fun e => e.1 == queryId).map Prod.snd
    unless (← ContextMap.findRaw' m queryId key) == expectedId do
      throw <| IO.userError s!"Exact lookup differs from list model at {i}"
    unless active.ids.length == active.ids.eraseDups.length do
      throw <| IO.userError "Duplicate active scope"
    for id in [:17] do
      unless active.contains id == active.ids.contains id do
        throw <| IO.userError "Active path and membership set differ"
  -- An ancestor written later must beat a newer scope id, including fallback
  -- after more than four inactive sibling updates.
  let mut es := ({} : ContextEntries Nat).insert 0 1 |>.insert 100 2 |>.insert 0 3
  for id in [200:220] do es := es.insert id id
  let chosen := ({} : ActiveContexts).insert 0 |>.insert 100
  unless es.findActive? chosen == some 3 do throw <| IO.userError "Ancestor precedence lost"
  unless es.findActive? (chosen.erase 0) == some 2 do throw <| IO.userError "Dormant child lost"
  unless es.findActive? ((chosen.erase 0).insert 0) == some 3 do
    throw <| IO.userError "Reactivated ancestor lost"
  unless (← ContextMap.findRaw m chosen ⟨mkConst ``False⟩).isNone do
    throw <| IO.userError "Unexpected absent-key result"
