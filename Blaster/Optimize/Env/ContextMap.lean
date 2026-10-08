import Lean
import Blaster.Data.HashSet
import Blaster.Data.HashMap
import Blaster.Optimize.Expr

open Lean Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

/-- Identifier for an optimization context (ite branch / match alternative /
    implication body). Assigned by a monotone counter; `0` is the global/root
    context. An entry tagged with a `CtxId` is visible iff that id is on the
    current root→current ancestor path (tracked by the `active` set). -/
abbrev CtxId := Nat

/-- A context-tagged entry -/
abbrev ContextEntry α := CtxId × α

/-- Small histories avoid a hash table allocation. Larger histories index the
    latest value of each context by its insertion stamp. The short recent list
    is a fast path, not a limit on the stored contexts. -/
inductive ContextEntries (α : Type) where
  | small (size : Nat) (entries : List (ContextEntry α))
  | indexed (nextStamp : Nat) (recent : List (ContextEntry α))
      (entries : HashMap CtxId (Nat × α))

def ContextEntries.singleton (ctx : CtxId) (value : α) : ContextEntries α :=
  .small 1 [(ctx, value)]

def ContextEntries.insert (history : ContextEntries α) (ctx : CtxId) (value : α) :
    ContextEntries α := Id.run do
  match history with
  | .small size entries =>
      if size < 8 then return .small (size + 1) ((ctx, value) :: entries)
      let mut table : HashMap CtxId (Nat × α) := HashMap.emptyWithCapacity
      let mut stamp := 0
      for (oldCtx, oldValue) in entries.reverse do
        table := table.insert oldCtx (stamp, oldValue)
        stamp := stamp + 1
      return .indexed (stamp + 1) [(ctx, value)] (table.insert ctx (stamp, value))
  | .indexed stamp recent entries =>
      return .indexed (stamp + 1) (((ctx, value) :: recent).take 4)
        (entries.insert ctx (stamp, value))

def ContextEntries.find? (history : ContextEntries α) (ctx : CtxId) : Option α :=
  match history with
  | .small _ entries => (entries.find? (·.1 == ctx)).map (·.2)
  | .indexed _ _ entries => (entries.get? ctx).map (·.2)

/-- Preserve newest-*inserted*-active semantics, including updates to an
    ancestor after a child was entered and reactivation of older scope ids.
    After a bounded fast path, visit only active slots, never retired siblings. -/
def ContextEntries.findActiveEntry? (history : ContextEntries α) (active : HashSet CtxId) :
    Option (ContextEntry α) := Id.run do
  let recent := match history with
    | .small _ entries => entries
    | .indexed _ entries _ => entries
  if let some entry := recent.find? (fun (ctx, _) => active.contains ctx) then
    return some entry
  let .indexed _ _ entries := history | return none
  let mut newest : Option (Nat × ContextEntry α) := none
  for i in [:active.ctrl.size] do
    if active.ctrl.get! i &&& 0x80 == 0 then continue
    let ctx := active.data[i]!
    if let some entry := entries.get? ctx then
      match newest with
      | none => newest := some (entry.1, ctx, entry.2)
      | some previous => if entry.1 > previous.1 then newest := some (entry.1, ctx, entry.2)
  return newest.map (·.2)

def ContextEntries.findActive? (history : ContextEntries α) (active : HashSet CtxId) :
    Option α := (history.findActiveEntry? active).map (·.2)

/-! ## ContextMap — context-aware map

Retired sibling scopes remain available for context reuse, but lookups must
not scan their entire history. ContextEntries switches to a context-id index
after eight insertions; insertion stamps retain the old newest-active order.
-/

abbrev ContextMap α := Lean.PersistentHashMap PtrExpr (IO.Ref (ContextEntries α))

@[always_inline, inline]
def ContextMap.empty : ContextMap α := {}

def ContextMap.findRawEntry (m : ContextMap α) (active : HashSet CtxId)
    (lhs : PtrExpr) : IO (Option (ContextEntry α)) := do
  let some entries := m.find? lhs | return none
  return (← entries.get).findActiveEntry? active

/-- Look up function for Context aware map, returning newest entry (if exists) whose `CtxId` is
    active for expression `e`.
-/
@[always_inline, inline]
def ContextMap.findRaw (m : ContextMap α) (active : HashSet CtxId) (lhs : PtrExpr) : IO (Option α) := do
  match m.find? lhs with
  | none => return none
  | some entries => return (← entries.get).findActive? active

/-- Look up function for Context aware map, returning the entry corresponding to the given CtxId (if exists). -/
@[always_inline, inline]
def ContextMap.findRaw' (m : ContextMap α) (ctxId : CtxId) (lhs : PtrExpr) : IO (Option α) := do
  match m.find? lhs with
  | none => return none
  | some entries => return (← entries.get).find? ctxId

end Blaster.Optimize
