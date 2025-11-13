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

end Test.BEqLawful
