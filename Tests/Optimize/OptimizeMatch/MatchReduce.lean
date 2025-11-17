import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.MatchReduce

/-! ## Test objectives to validate choice reduction on match expressions. -/

def discrAbstractOne (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [], _ => false
  | _, _ => true

/-! Test cases to validate when choice reduction must be applied on match expression. -/

-- ∀ (α : Type), discrAbstractOne ([] : List α) none = true ===> True
#testOptimize [ "MatchReduce_1" ] ∀ (α : Type), discrAbstractOne ([] : List α) none = true ===> True

-- ∀ (α : Type) (y : α), discrAbstractOne ([] : List α) (some y) = false ===> True
#testOptimize [ "MatchReduce_2" ] ∀ (α : Type) (y : α), discrAbstractOne ([] : List α) (some y) = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] none = false ===> True
#testOptimize [ "MatchReduce_3" ] ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] none = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] (some z) = true ===> True
#testOptimize [ "MatchReduce_4" ] ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] (some z) = true ===> True


/-! Test cases to validate when choice reduction must NOT be applied on match expression. -/

-- ∀ (α : Type) (x : List α), discrAbstractOne x none ===>
-- ∀ (α : Type) (x : List α), [] = x
-- NOTE: Match is normalized to ite since we are no more constrainted
-- with Decidable instance on Eq.
#testOptimize [ "MatchReduceUnchanged_1" ]
  ∀ (α : Type) (x : List α), discrAbstractOne x none ===>
  ∀ (α : Type) (x : List α), [] = x

-- ∀ (α : Type) (y : Option α), discrAbstractOne ([] : List α) y ===>
-- ∀ (α : Type) (y : Option α), none = y
-- NOTE: Match is normalized to ite since we are no more constrainted
-- with Decidable instance on Eq.
#testOptimize [ "MatchReduceUnchanged_2" ]
  ∀ (α : Type) (y : Option α), discrAbstractOne ([] : List α) y ===>
  ∀ (α : Type) (y : Option α), none = y


def discrAbstractTwo (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], some _ => true
  | _, none => false
  | _, _ => true

-- ∀ (α : Type) (x : List α), discrAbstractTwo x none ===>
-- ∀ (α : Type) (x : List α),
--  ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
--    (fun (_ : α) => True)
--    (fun (_ : List α) => False)
--    (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_3" ]
  ∀ (α : Type) (x : List α), discrAbstractTwo x none ===>
  ∀ (α : Type) (x : List α),
    ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
      (fun (_ : α) => True)
      (fun (_ : List α) => False)
      (fun (_ : List α) (_ : Option α) => True) )

-- ∀ (α : Type) (y : Option α), discrAbstractTwo ([] : List α) y ===>
-- ∀ (α : Type) (y : Option α),
--  ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
--    (fun (_ : α) => True)
--    (fun (_ : List α) => False)
--    (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_4" ]
  ∀ (α : Type) (y : Option α), discrAbstractTwo ([] : List α) y ===>
  ∀ (α : Type) (y : Option α),
    ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
      (fun (_ : α) => True)
      (fun (_ : List α) => False)
      (fun (_ : List α) (_ : Option α) => True) )

end Tests.MatchReduce
