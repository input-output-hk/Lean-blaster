import Lean
import Blaster.Data.HashSet
import Blaster.Data.HashMap
import Blaster.Optimize.Expr

open Lean Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

/-- Monotonically allocated optimization-scope identifier. A dormant scope may
    become active again through context reuse. -/
abbrev CtxId := Nat
abbrev ContextEntry α := CtxId × α

/-- The active scope set, also keeping a short iterable path. Scope insertion is
    idempotent and erasure removes the same id from both representations. -/
structure ActiveContexts where
  members : HashSet CtxId := HashSet.emptyWithCapacity 123
  ids : List CtxId := []

namespace ActiveContexts
@[inline] def contains (s : ActiveContexts) (id : CtxId) : Bool := s.members.contains id
@[inline] def insert (s : ActiveContexts) (id : CtxId) : ActiveContexts :=
  if s.contains id then s else ⟨s.members.insert id, id :: s.ids⟩
@[inline] def erase (s : ActiveContexts) (id : CtxId) : ActiveContexts :=
  ⟨s.members.erase id, s.ids.erase id⟩
end ActiveContexts

/-- Latest value per scope, with an insertion ordinal that preserves the old
    newest-active-entry semantics even when an ancestor is updated after a child.
    A bounded recent list handles the common case without scanning the path. -/
structure ContextEntries (α : Type) where
  byContext : HashMap CtxId (Nat × α) := HashMap.emptyWithCapacity 8
  recent : List (ContextEntry α) := []
  nextOrdinal : Nat := 0

namespace ContextEntries
@[inline] def insert (es : ContextEntries α) (id : CtxId) (value : α) : ContextEntries α :=
  { byContext := es.byContext.insert id (es.nextOrdinal, value)
    recent := (id, value) :: es.recent.take 3
    nextOrdinal := es.nextOrdinal + 1 }

@[inline] def singleton (id : CtxId) (value : α) : ContextEntries α :=
  ({} : ContextEntries α).insert id value

@[inline] def find? (es : ContextEntries α) (id : CtxId) : Option α :=
  (es.byContext.get? id).map Prod.snd

/-- No entries are discarded when scopes become inactive. On a recent-list miss,
    inspect the active path rather than the unbounded inactive sibling history. -/
def findActive? (es : ContextEntries α) (active : ActiveContexts) : Option α := Id.run do
  for (id, value) in es.recent do
    if active.contains id then return some value
  if es.nextOrdinal ≤ 4 then return none
  let mut best : Option (Nat × α) := none
  for id in active.ids do
    if let some candidate := es.byContext.get? id then
      match best with
      | none => best := some candidate
      | some previous => if candidate.1 > previous.1 then best := some candidate
  return best.map Prod.snd
end ContextEntries

abbrev ContextMap α := HashMap PtrExpr (IO.Ref (ContextEntries α))

@[always_inline, inline]
def ContextMap.empty : ContextMap α := HashMap.emptyWithCapacity 1024

/-- Newest entry whose scope is active, including reactivated dormant scopes. -/
@[always_inline, inline]
def ContextMap.findRaw (m : ContextMap α) (active : ActiveContexts) (lhs : PtrExpr) : IO (Option α) := do
  match m.get? lhs with
  | none => return none
  | some entry => return (← entry.get).findActive? active

@[always_inline, inline]
def ContextMap.findRaw' (m : ContextMap α) (ctxId : CtxId) (lhs : PtrExpr) : IO (Option α) := do
  match m.get? lhs with
  | none => return none
  | some entry => return (← entry.get).find? ctxId

end Blaster.Optimize
