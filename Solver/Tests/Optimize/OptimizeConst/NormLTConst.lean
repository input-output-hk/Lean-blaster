import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.NormLTConst

/-! ## Test objectives to validate normalization rules on `Lt.lt` const
       obtained after unfolding `Gt.gt definition.
-/

/-! Test cases for normalization rule:
      - `app (const ``LT.lt l) e1 e2 ==> app (const ``Lt.lt us) e1 e2 (if n = ``GT.gt)`
-/

-- ∀ (x y : Int), x > y ===> ∀ (x y : Int), y < x
#testOptimize [ "ConstGT_1" ] ∀ (x y : Int), x > y ===> ∀ (x y : Int), y < x

-- ∀ (α : Type) (x y : α), [LT α] → x > y ===> ∀ (α : Type) (x y : α), [LT α] → y < x
#testOptimize [ "ConstGT_2" ] ∀ (α : Type) (x y : α), [LT α] → x > y ===> ∀ (α : Type) (x y : α), [LT α] → y < x

-- ∀ (α : Type) (x y : List α), [LT α] → x > y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → List.lt y x
#testOptimize [ "ConstGT_3" ]
  ∀ (α : Type) (x y : List α), [LT α] → x > y ===>
  ∀ (α : Type) (x y : List α), [LT α] → List.lt y x

-- ∀ (x y : Int), (x > y) = (y < x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGT_4" ] ∀ (x y : Int), (x > y) = (y < x) ===> True

-- ∀ (α : Type) (x y : α), [LT α] → (x > y) = (y < x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGT_5" ] ∀ (α : Type) (x y : α), [LT α] → (x > y) = (y < x) ===> True

-- ∀ (α : Type) (x y : List α), [LT α] → (x > y) = (y < x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGT_6" ] ∀ (α : Type) (x y : List α), [LT α] → (x > y) = (y < x) ===> True


/-! Test cases to ensure that normalization is not wrongly applied on nominal `LT.lt` expressions.
-/

-- ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y
-- LT remains unchanged
#testOptimize [ "ConstLT_1" ] ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y

-- ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y
-- LT remains unchanged
#testOptimize [ "ConstLT_2" ] ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y

-- ∀ (α : Type) (x y : List α), [LT α] → x < y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → List.lt x y
-- LT remains unchanged
#testOptimize [ "ConstLT_3" ]
  ∀ (α : Type) (x y : List α), [LT α] → x < y ===>
  ∀ (α : Type) (x y : List α), [LT α] → List.lt x y

end Test.NormLTConst
