import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.NormNeConst

/-! ## Test objectives to validate normalization rules on `Eq` const
       obtained after unfolding `Ne definition.
-/

/-! Test cases for normalization rule:
      - `app (const ``Not l1) (app (const ``Eq l2) e1 e2) ===> app (const ``Not l1) (app (const ``Eq us) e1 e2) (if n = ``Ne)`
-/

-- ∀ (x y : Int), x ≠ y ==> ∀ (x y : Int), ¬ x = y
#testOptimize [ "ConstNe_1" ] ∀ (x y : Int), x ≠ y ===> ∀ (x y : Int), ¬ x = y

-- ∀ (α : Type) (x y : α), x ≠ y ==> ∀ (α : Type) (x y : α), ¬ x = y
#testOptimize [ "ConstNe_2" ] ∀ (α : Type) (x y : α), x ≠ y ===> ∀ (α : Type) (x y : α), ¬ x = y

-- ∀ (α : Type) (x y : List α), x ≠ y ==> ∀ (α : Type) (x y : List α), ¬ x = y
#testOptimize [ "ConstNe_3" ] ∀ (α : Type) (x y : List α), x ≠ y ===> ∀ (α : Type) (x y : List α), ¬ x = y

-- ∀ (x y : Int), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_4" ] ∀ (x y : Int), (x ≠ y) = ¬ (x = y) ===> True

-- ∀ (α : Type) (x y : α), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_5" ] ∀ (α : Type) (x y : α), (x ≠ y) = ¬ (x = y) ===> True

-- ∀ (α : Type) (x y : List α), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_6" ] ∀ (α : Type) (x y : List α), (x ≠ y) = ¬ (x = y) ===> True


/-! Test cases to ensure that normalization is not wrongly applied on nominal `Eq` expressions. -/

-- ∀ (x y : Int), x = y ==> ∀ (x y : Int), x = y
#testOptimize [ "ConstEq_1" ] ∀ (x y : Int), x = y ===> ∀ (x y : Int), x = y

-- ∀ (x y : Int), ¬ x = y ==> ∀ (x y : Int), ¬ x = y
#testOptimize [ "ConstEq_2" ] ∀ (x y : Int), ¬ x = y ===> ∀ (x y : Int), ¬ x = y

-- ∀ (α : Type) (x y : α), x = y ==> ∀ (α : Type) (x y : α), x = y
#testOptimize [ "ConstEq_3" ] ∀ (α : Type) (x y : α), x = y ===> ∀ (α : Type) (x y : α), x = y

-- ∀ (α : Type) (x y : α), ¬ x = y ==> ∀ (α : Type) (x y : α), ¬ x = y
#testOptimize [ "ConstEq_4" ] ∀ (α : Type) (x y : α), ¬ x = y ===> ∀ (α : Type) (x y : α), ¬ x = y

-- ∀ (α : Type) (x y : List α), x = y ==> ∀ (α : Type) (x y : List α), x = y
#testOptimize [ "ConstEq_5" ] ∀ (α : Type) (x y : List α), x = y ===> ∀ (α : Type) (x y : List α), x = y

-- ∀ (α : Type) (x y : List α), ¬ x = y ==> ∀ (α : Type) (x y : List α), ¬ x = y
#testOptimize [ "ConstEq_6" ] ∀ (α : Type) (x y : List α), ¬ x = y ===> ∀ (α : Type) (x y : List α), ¬ x = y


end Test.NormNeConst
