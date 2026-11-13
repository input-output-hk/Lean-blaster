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
#testOptimize [ "ConstNe_1", proof ] ∀ (x y : Int), x ≠ y ===> ∀ (x y : Int), ¬ x = y

-- ∀ (α : Type) (x y : α), x ≠ y ==> ∀ (α : Type) (x y : α), ¬ x = y
#testOptimize [ "ConstNe_2", proof ] ∀ (α : Type) (x y : α), x ≠ y ===> ∀ (α : Type) (x y : α), ¬ x = y

-- ∀ (α : Type) (x y : List α), x ≠ y ==> ∀ (α : Type) (x y : List α), ¬ x = y
#testOptimize [ "ConstNe_3", proof ] ∀ (α : Type) (x y : List α), x ≠ y ===> ∀ (α : Type) (x y : List α), ¬ x = y

-- ∀ (x y : Int), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_4", proof ] ∀ (x y : Int), (x ≠ y) = ¬ (x = y) ===> True

-- ∀ (α : Type) (x y : α), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_5", proof ] ∀ (α : Type) (x y : α), (x ≠ y) = ¬ (x = y) ===> True

-- ∀ (α : Type) (x y : List α), x ≠ y = ¬ x = y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstNe_6", proof ] ∀ (α : Type) (x y : List α), (x ≠ y) = ¬ (x = y) ===> True


/-! Test cases where a hypothesis hides `Ne` behind a definition or a `let`. -/

def NonZero (x : Nat) : Prop := x ≠ 0
abbrev NonZeroInt (x : Int) : Prop := x ≠ 0

-- ∀ (x : Nat), NonZero x → x ≠ 0 ===> True
#testOptimize [ "ConstNeHypDef_1", proof ] ∀ (x : Nat), NonZero x → x ≠ 0 ===> True

-- ∀ (x : Nat), NonZero x → (x ≠ 0 ∧ x ≠ 0) ===> True
#testOptimize [ "ConstNeHypDef_2", proof ] ∀ (x : Nat), NonZero x → (x ≠ 0 ∧ x ≠ 0) ===> True

-- ∀ (x : Int), NonZeroInt x → (x ≠ 0 ∧ x ≠ 0) ===> True
#testOptimize [ "ConstNeHypAbbrev_1", proof ] ∀ (x : Int), NonZeroInt x → (x ≠ 0 ∧ x ≠ 0) ===> True

-- ∀ (x : Nat), (let y := x; y ≠ 0) → (x ≠ 0 ∧ x ≠ 0) ===> True
#testOptimize [ "ConstNeHypLet_1", proof ] ∀ (x : Nat), (let y := x; y ≠ 0) → (x ≠ 0 ∧ x ≠ 0) ===> True

-- ∀ (a : Bool), (let b := a; b ≠ true) → (a ≠ true ∧ a ≠ true) ===> True
#testOptimize [ "ConstNeHypLet_2", proof ] ∀ (a : Bool), (let b := a; b ≠ true) → (a ≠ true ∧ a ≠ true) ===> True


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
