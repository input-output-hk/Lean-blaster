import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldRelationalOp

/-! ## Test objectives to validate unfolding relational operators -/


/-! Test cases to validate unfolding of relational operators only when reduced to a constant value or via rewriting. -/

-- TODO: add test cases when simplification on relational operators are introduced


/-! Test cases to validate when relational operators must not be unfolded -/

-- ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ y < x
#testOptimize ["RelOpNotUnfolded_1"] ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ y < x

-- ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), ¬ x < y
#testOptimize ["RelOpNotUnfolded_2"] ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), ¬ x < y

-- ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), ¬ y < x
#testOptimize ["RelOpNotUnfolded_3"] ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- ∀ (x y : Nat), x ≥ y ===> ∀ (x y : Nat), ¬ x < y
#testOptimize ["RelOpNotUnfolded_4"] ∀ (x y : Nat), x ≥ y ===> ∀ (x y : Nat), ¬ x < y

-- ∀ (a b : Bool), a ≤ b ===> ∀ (a b : Bool), ¬ b < a
#testOptimize ["RelOpNotUnfolded_5"] ∀ (a b : Bool), a ≤ b ===> ∀ (a b : Bool), ¬ b < a

-- ∀ (a b : Bool), a ≥ b ===> ∀ (a b : Bool), ¬ a < b
#testOptimize ["RelOpNotUnfolded_6"] ∀ (a b : Bool), a ≥ b ===> ∀ (a b : Bool), ¬ a < b

-- ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y
#testOptimize [ "RelOpNotUnfolded_7" ]  ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y

-- ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x
#testOptimize [ "RelOpNotUnfolded_8" ]  ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x

-- ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) y x
#testOptimize [ "RelOpNotUnfolded_9" ]
  ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===>
  ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) y x

-- ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) x y
#testOptimize [ "RelOpNotUnfolded_10" ]
  ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===>
  ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) x y

-- ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y
#testOptimize ["RelOpNotUnfolded_11"] ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y

-- ∀ (x y : Int), x > y ===> ∀ (x y : Int), y < x
#testOptimize ["RelOpNotUnfolded_12"] ∀ (x y : Int), x > y ===> ∀ (x y : Int), y < x

-- ∀ (x y : Nat), x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["RelOpNotUnfolded_13"] ∀ (x y : Nat), x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), x > y ===> ∀ (x y : Nat), y < x
#testOptimize ["RelOpNotUnfolded_14"] ∀ (x y : Nat), x > y ===> ∀ (x y : Nat), y < x

-- ∀ (a b : Bool), a < b ===> ∀ (a b : Bool), a < b
#testOptimize ["RelOpNotUnfolded_15"] ∀ (a b : Bool), a < b ===> ∀ (a b : Bool), a < b

-- ∀ (a b : Bool), a > b ===> ∀ (a b : Bool), b < a
#testOptimize ["RelOpNotUnfolded_16"] ∀ (a b : Bool), a > b ===> ∀ (a b : Bool), b < a

-- ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y
#testOptimize [ "RelOpNotUnfolded_17" ]  ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y

-- ∀ (α : Type) (x y : α), [LT α] → x > y ===> ∀ (α : Type) (x y : α), [LT α] → y < x
#testOptimize [ "RelOpNotUnfolded_18" ]  ∀ (α : Type) (x y : α), [LT α] → x > y ===> ∀ (α : Type) (x y : α), [LT α] → y < x

-- ∀ (α : Type) (x y : List α), [LT α] → x < y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → List.Lex (λ a b => LT.lt a b) x y
#testOptimize [ "RelOpNotUnfolded_19" ]
  ∀ (α : Type) (x y : List α), [LT α] → x < y ===>
  ∀ (α : Type) (x y : List α), [LT α] → List.Lex (λ a b => LT.lt a b) x y

-- ∀ (α : Type) (x y : List α), [LT α] → x > y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → List.Lex (λ a b => LT.lt a b) y x
#testOptimize [ "RelOpNotUnfolded_20" ]
  ∀ (α : Type) (x y : List α), [LT α] → x > y ===>
  ∀ (α : Type) (x y : List α), [LT α] → List.Lex (λ a b => LT.lt a b) y x


end Tests.UnfoldRelationalOp
