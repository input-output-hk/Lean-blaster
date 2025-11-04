import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.MatchReduce

/-! ## Test objectives to validate choice reduction on match expressions. -/

def discrAbstract (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [], _ => false
  | _, _ => true

/-! Test cases to validate when choice reduction must be applied on match expression. -/

-- ∀ (α : Type), discrAbstract ([] : List α) none = true ===> True
#testOptimize [ "MatchReduce_1" ] ∀ (α : Type), discrAbstract ([] : List α) none = true ===> True

-- ∀ (α : Type) (y : α), discrAbstract ([] : List α) (some y) = false ===> True
#testOptimize [ "MatchReduce_2" ] ∀ (α : Type) (y : α), discrAbstract ([] : List α) (some y) = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstract [x, y , z] none = false ===> True
#testOptimize [ "MatchReduce_3" ] ∀ (α : Type) (x y z : α), discrAbstract [x, y , z] none = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstract [x, y , z] (some z) = true ===> True
#testOptimize [ "MatchReduce_4" ] ∀ (α : Type) (x y z : α), discrAbstract [x, y , z] (some z) = true ===> True


/-! Test cases to validate when choice reduction must NOT be applied on match expression. -/

-- ∀ (α : Type) (x : List α), discrAbstract x none ===>
-- ∀ (α : Type) (x : List α),
--   ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
--     (fun (_ : PUnit) => True)
--     (fun (_ : List α) => False)
--     (fun (_ : Option α) => False)
--     (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_1" ]
  ∀ (α : Type) (x : List α), discrAbstract x none ===>
  ∀ (α : Type) (x : List α),
    ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
      (fun (_ : PUnit) => True)
      (fun (_ : List α) => False)
      (fun (_ : Option α) => False)
      (fun (_ : List α) (_ : Option α) => True) )

-- ∀ (α : Type) (y : Option α), discrAbstract ([] : List α) y ===>
-- ∀ (α : Type) (y : Option α),
--   ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
--     (fun (_ : PUnit) => True)
--     (fun (_ : List α) => False)
--     (fun (_ : Option α) => False)
--     (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_2" ]
  ∀ (α : Type) (y : Option α), discrAbstract ([] : List α) y ===>
  ∀ (α : Type) (y : Option α),
    ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
      (fun (_ : PUnit) => True)
      (fun (_ : List α) => False)
      (fun (_ : Option α) => False)
      (fun (_ : List α) (_ : Option α) => True) )


end Tests.MatchReduce
