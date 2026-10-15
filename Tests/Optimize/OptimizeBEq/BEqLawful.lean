import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.BEqLawful

/-! ## Test objectives to validate normalization on BEq.beq with LawfulBEq instances. -/

-- ∀ (x : List Nat), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_1" ] ∀ (x : List Nat), x == x ===> True

-- ∀ (x : List Int), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_2" ] ∀ (x : List Int), x == x ===> True

-- ∀ (x : List String), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_3" ] ∀ (x : List String), x == x ===> True

-- ∀ (x y : List Nat), x == y → x = y ===> True
 #testOptimize [ "BEqLawful_6" ] ∀ (x y : List Nat), x == y → x = y ===> True

-- ∀ (x : List Int), x == x → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_7" ] ∀ (x y : List Int), x == y → x = y ===> True

-- ∀ (x y : List String), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_8" ]  ∀ (x y : List String), x == y → x = y ===> True

-- ∀ (α : Type) (x : α), [BEq α] → [LawfulBEq α] → x == x ===> True
-- NOTE: Test case to ensure that BEq with LawfulBEq constraints is also handled properly
#testOptimize [ "BEqLawful_11" ] ∀ (α : Type) (x : α), [BEq α] → [LawfulBEq α] → x == x ===> True

-- ∀ (α : Type) (x y : α), [BEq α] → [LawfulBEq α] → x == y → x = y ===> True
-- NOTE: Test case to ensure that BEq with LawfulBEq constraints is also handled properly
#testOptimize [ "BEqLawful_12" ]
  ∀ (α : Type) (x y : α), [BEq α] → [LawfulBEq α] → x == y → x = y ===> True

-- ∀ (x : List (List Int)), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types, even to nested types
#testOptimize [ "BEqLawful_13"] ∀ (x : List (List Int)), x == x ===> True

-- ∀ (x y : List (List Int)), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_14" ]  ∀ (x y : List (List Int)), x == y → x = y ===> True

-- ∀ (x : List (List Int)), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types, even to nested types
#testOptimize [ "BEqLawful_15"] ∀ (x : List (List (Option Int))), x == x ===> True

-- ∀ (x y : List (List Int)), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_16" ]  ∀ (x y : List (List (Option Int))), x == y → x = y ===> True

/-! ## Universe level of the `LawfulBEq` constraint

`LawfulBEq.{u}` takes `α : Type u`, so the constraint built to look for an instance must use the level
of `α` (level `1` for `α : Type 1`), otherwise the instance cannot be inferred (the ill-typed constraint
fails to synthesize) and `BEq.beq` is unfolded instead of being rewritten to `Eq`. The `Eq` produced by
the rewrite must be built at the level of `α` as well. -/

inductive U1 : Type 1 where
  | a | b

instance : BEq U1 where
  beq | .a, .a => true | .b, .b => true | _, _ => false

instance : LawfulBEq U1 where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | contradiction
  rfl {x} := by cases x <;> rfl

inductive U0 where
  | a | b

instance : BEq U0 where
  beq | .a, .a => true | .b, .b => true | _, _ => false

instance : LawfulBEq U0 where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | contradiction
  rfl {x} := by cases x <;> rfl

-- level 0 control: ∀ (x y : U0), (x == y) = true ===> ∀ (x y : U0), x = y
#testOptimize [ "BEqLawfulLevel_1" ] ∀ (x y : U0), (x == y) = true ===> ∀ (x y : U0), x = y

-- ∀ (x y : U1), (x == y) = true ===> ∀ (x y : U1), x = y   (with `Eq.{2}`)
#testOptimize [ "BEqLawfulLevel_2" ] ∀ (x y : U1), (x == y) = true ===> ∀ (x y : U1), x = y

-- ∀ (x y : U1), (x == y) = true → x = y ===> True
#testOptimize [ "BEqLawfulLevel_3" ] ∀ (x y : U1), (x == y) = true → x = y ===> True

-- ∀ (x : U1), (x == x) = true ===> True
#testOptimize [ "BEqLawfulLevel_4" ] ∀ (x : U1), (x == x) = true ===> True

-- ∀ (xs : List U1), (xs == xs) = true ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
#testOptimize [ "BEqLawfulLevel_5" ] ∀ (xs : List U1), (xs == xs) = true ===> True

-- level 0 control: ∀ (α : Type) [BEq α] [LawfulBEq α] (x y : α), (x == y) = true → x = y ===> True
#testOptimize [ "BEqLawfulLevel_6" ] ∀ (α : Type) [BEq α] [LawfulBEq α] (x y : α), (x == y) = true → x = y ===> True

-- ∀ (α : Type 1) [BEq α] [LawfulBEq α] (x : α), (x == x) = true ===> True
#testOptimize [ "BEqLawfulLevel_7" ] ∀ (α : Type 1) [BEq α] [LawfulBEq α] (x : α), (x == x) = true ===> True

-- ∀ (α : Type 1) [BEq α] [LawfulBEq α] (xs : List α), (xs == xs) = true ===> True
#testOptimize [ "BEqLawfulLevel_8" ] ∀ (α : Type 1) [BEq α] [LawfulBEq α] (xs : List α), (xs == xs) = true ===> True

-- ∀ (α : Type 1) [BEq α] [LawfulBEq α] (x y : α), (x == y) = true → x = y ===> True
#testOptimize [ "BEqLawfulLevel_9" ] ∀ (α : Type 1) [BEq α] [LawfulBEq α] (x y : α), (x == y) = true → x = y ===> True

end Test.BEqLawful
