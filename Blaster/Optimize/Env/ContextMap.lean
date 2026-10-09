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

/-! ## ContextMap — context-aware map -/

abbrev ContextMap α := HashMap PtrExpr (IO.Ref (List (ContextEntry α)))

@[always_inline, inline]
def ContextMap.empty : ContextMap α := HashMap.emptyWithCapacity 1024

/-- Look up function for Context aware map, returning newest entry (if exists) whose `CtxId` is
    active for expression `e`.
-/
@[always_inline, inline]
def ContextMap.findRaw (m : ContextMap α) (active : HashSet CtxId) (lhs : PtrExpr) : IO (Option α) := do
  match m.get? lhs with
  | none => return none
  | some arr =>
      let rec findChild (xs : List (ContextEntry α)) : Option α := do
        match xs with
        | [] => none
        | (c, v) :: xs' => if active.contains c then v else findChild xs'
      return findChild (← arr.get)

/-- Look up function for Context aware map, returning the entry corresponding to the given CtxId (if exists). -/
@[always_inline, inline]
def ContextMap.findRaw' (m : ContextMap α) (ctxId : CtxId) (lhs : PtrExpr) : IO (Option α) := do
  match m.get? lhs with
  | none => return none
  | some arr =>
      let rec findChild (xs : List (ContextEntry α)) : Option α := do
        match xs with
        | [] => none
        | (c, v) :: xs' => if c == ctxId then v else findChild xs'
      return findChild (← arr.get)

end Blaster.Optimize
