import Blaster.Optimize.Env.ContextMap

open Lean Elab Command Blaster.Optimize Blaster.Data.HashSet

-- Check newest-write precedence across updates, inactive siblings,
-- scope reactivation, repeated writes, and writes to older ancestor ids.
run_cmd liftIO do
  let key : PtrExpr := ⟨mkConst ``True⟩
  let entry ← IO.mkRef ([] : List (ContextEntry Nat))
  let m := (ContextMap.empty : ContextMap Nat).insert key entry
  let mut model : List (ContextEntry Nat) := []
  let mut active : HashSet CtxId := HashSet.emptyWithCapacity 17
  for i in [:1000] do
    let id := i % 17
    entry.modify fun es => (id, i) :: es
    model := (id, i) :: model
    active := (active.insert ((i * 7) % 17)).erase ((i * 11) % 17)
    active := active.insert 0 |>.insert 0
    let expected := (model.find? fun e => active.contains e.1).map Prod.snd
    unless (← ContextMap.findRaw m active key) == expected do
      throw <| IO.userError s!"Active lookup differs from list model at {i}"
    let queryId := (i * 13) % 17
    let expectedId := (model.find? fun e => e.1 == queryId).map Prod.snd
    unless (← ContextMap.findRaw' m queryId key) == expectedId do
      throw <| IO.userError s!"Exact lookup differs from list model at {i}"
  -- The latest ancestor write must beat a newer scope id even after
  -- writes to inactive siblings.
  let mut entries : List (ContextEntry Nat) := [(0, 3), (100, 2), (0, 1)]
  for id in [200:220] do entries := (id, id) :: entries
  entry.set entries
  let chosen := (HashSet.emptyWithCapacity 2 : HashSet CtxId).insert 0 |>.insert 100
  unless (← ContextMap.findRaw m chosen key) == some 3 do
    throw <| IO.userError "Ancestor precedence lost"
  unless (← ContextMap.findRaw m (chosen.erase 0) key) == some 2 do
    throw <| IO.userError "Dormant child lost"
  unless (← ContextMap.findRaw m ((chosen.erase 0).insert 0) key) == some 3 do
    throw <| IO.userError "Reactivated ancestor lost"
  unless (← ContextMap.findRaw m chosen ⟨mkConst ``False⟩).isNone do
    throw <| IO.userError "Unexpected absent-key result"
