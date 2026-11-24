import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.BEqLawful

/-! ## Test objectives to validate normalization on BEq.beq with LawfulBEq instances. -/

-- ∀ (x : List Nat), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_1", proof ] ∀ (x : List Nat), x == x ===> True

-- ∀ (x : List Int), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_2", proof ] ∀ (x : List Int), x == x ===> True

-- ∀ (x : List String), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_3", proof ] ∀ (x : List String), x == x ===> True

-- ∀ (x y : List Nat), x == y → x = y ===> True
 #testOptimize [ "BEqLawful_6", proof ] ∀ (x y : List Nat), x == y → x = y ===> True

-- ∀ (x : List Int), x == x → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_7", proof ] ∀ (x y : List Int), x == y → x = y ===> True

-- ∀ (x y : List String), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_8", proof ]  ∀ (x y : List String), x == y → x = y ===> True

-- ∀ (α : Type) (x : α), [BEq α] → [LawfulBEq α] → x == x ===> True
-- NOTE: Test case to ensure that BEq with LawfulBEq constraints is also handled properly
#testOptimize [ "BEqLawful_11", proof ] ∀ (α : Type) (x : α), [BEq α] → [LawfulBEq α] → x == x ===> True

-- ∀ (α : Type) (x y : α), [BEq α] → [LawfulBEq α] → x == y → x = y ===> True
-- NOTE: Test case to ensure that BEq with LawfulBEq constraints is also handled properly
#testOptimize [ "BEqLawful_12", proof ]
  ∀ (α : Type) (x y : α), [BEq α] → [LawfulBEq α] → x == y → x = y ===> True

-- ∀ (x : List (List Int)), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types, even to nested types
#testOptimize [ "BEqLawful_13", proof ] ∀ (x : List (List Int)), x == x ===> True

-- ∀ (x y : List (List Int)), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_14", proof ]  ∀ (x y : List (List Int)), x == y → x = y ===> True

-- ∀ (x : List (List Int)), x == x ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types, even to nested types
#testOptimize [ "BEqLawful_15", proof ] ∀ (x : List (List (Option Int))), x == x ===> True

-- ∀ (x y : List (List Int)), x == y → x = y ===> True
-- NOTE: LawfulBEq instance transitively extends when instantiating polymorphic data types
 #testOptimize [ "BEqLawful_16", proof ]  ∀ (x y : List (List (Option Int))), x == y → x = y ===> True

-- ∀ (x : Int), ((x, 1) == (x, 2)) = false ===> True
-- NOTE: Test case to ensure that structurally distinct operands are reduced to false
#testOptimize [ "BEqLawful_17", proof ] ∀ (x : Int), ((x, 1) == (x, 2)) = false ===> True

-- ∀ (x : Int), (some (x, 1) == some (x, 2)) = false ===> True
-- NOTE: Test case to ensure that structurally distinct operands are reduced to false
#testOptimize [ "BEqLawful_18", proof ] ∀ (x : Int), (some (x, 1) == some (x, 2)) = false ===> True

end Test.BEqLawful
