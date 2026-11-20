import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.NormLEConst

/-! ## Test objectives to validate normalization rules on `LE.le` const
       obtained after unfolding `GE.ge definition.
-/

/-! Test cases for normalization rule:
      - `app (const ``LE.le l) e1 e2 ==> app (const ``Lt.lt us) e1 e2 (if n = ``GE.ge)`
-/

-- ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), ¬ x < y
#testOptimize [ "ConstGE_1", proof ] ∀ (x y : Int), x ≥ y ===> ∀ (x y : Int), ¬ x < y

-- ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x
#testOptimize [ "ConstGE_2", proof ] ∀ (α : Type) (x y : α), [LE α] → x ≥ y ===> ∀ (α : Type) (x y : α), [LE α] → y ≤ x

-- ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → ¬ (List.Lex (λ a b => LT.lt a b) x y)
#testOptimize [ "ConstGE_3", proof ]
  ∀ (α : Type) (x y : List α), [LT α] → x ≥ y ===>
  ∀ (α : Type) (x y : List α), [LT α] → ¬ (List.Lex (λ a b => LT.lt a b) x y)

-- ∀ (x y : Int), (x ≥ y) = (y ≤ x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGE_4", proof ] ∀ (x y : Int), (x ≥ y) = (y ≤ x) ===> True

-- ∀ (α : Type) (x y : α), [LE α] → (x ≥ y) = (y ≤ x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGE_5", proof ] ∀ (α : Type) (x y : α), [LE α] → (x ≥ y) = (y ≤ x) ===> True

-- ∀ (α : Type) (x y : List α), [LT α] → (x ≥ y) = (y ≤ x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstGE_6", proof ] ∀ (α : Type) (x y : List α), [LT α] → (x ≥ y) = (y ≤ x) ===> True


/-! Test cases to ensure that normalization is not wrongly applied on nominal `LE.le` expressions.
-/

-- ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ y < x
-- LE remains unchanged
#testOptimize [ "ConstLE_1", proof ] ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ y < x

-- ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y
-- LE remains unchanged
#testOptimize [ "ConstLE_2", proof ] ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y

-- ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===>
-- ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) y x
-- LE remains unchanged
#testOptimize [ "ConstLE_3", proof ]
  ∀ (α : Type) (x y : List α), [LT α] → x ≤ y ===>
  ∀ (α : Type) (x y : List α), [LT α] → ¬ List.Lex (λ a b => LT.lt a b) y x

end Test.NormLEConst
