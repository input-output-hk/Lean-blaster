import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldRelationalOp

/-! ## Test objectives to validate unfolding relational operators -/


/-! Test cases to validate unfolding of relational operators only when reduced to a constant value or via rewriting. -/

-- TODO: add test cases when simplification on relational operators are introduced


/-! Test cases to validate when relational operators must not be unfolded -/

-- ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), x ≤ y
#testOptimize ["RelOpNotUnfolded_1"] ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), x ≤ y

-- ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), y ≤ x
#testOptimize ["RelOpNotUnfolded_2"] ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), y ≤ x

-- ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), x ≤ y
#testOptimize ["RelOpNotUnfolded_3"] ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- ∀ (x y : Nat), x ≥ y ===> ∀ (x y : Nat), y ≤ x
#testOptimize ["RelOpNotUnfolded_4"] ∀ (x y : Nat), x ≥ y ===> ∀ (x y : Nat), y ≤ x

-- ∀ (a b : Bool), a ≤ b ===> ∀ (a b : Bool), a ≤ b
#testOptimize ["RelOpNotUnfolded_5"] ∀ (a b : Bool), a ≤ b ===> ∀ (a b : Bool), a ≤ b

-- ∀ (a b : Bool), a ≥ b ===> ∀ (a b : Bool), b ≤ a
#testOptimize ["RelOpNotUnfolded_6"] ∀ (a b : Bool), a ≥ b ===> ∀ (a b : Bool), b ≤ a

-- ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y
#testOptimize [ "RelOpNotUnfolded_7" ]  ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y

-- ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x
#testOptimize [ "RelOpNotUnfolded_8" ]  ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x

-- ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===> ∀ (α : Type) (x y : List α), [LT α] → x ≤ y
#testOptimize [ "RelOpNotUnfolded_9" ] ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===> ∀ (α : Type) (x y : List α), [LT α] → x ≤ y

-- ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===> ∀ (α : Type) (x y : List α), [LT α] → y ≤ x
#testOptimize [ "RelOpNotUnfolded_10" ] ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===> ∀ (α : Type) (x y : List α), [LT α] → y ≤ x


end Tests.UnfoldRelationalOp
