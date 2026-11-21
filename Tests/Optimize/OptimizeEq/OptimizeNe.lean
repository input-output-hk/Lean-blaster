import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNe

/-! ## Test objectives to validate normalization rules on `Ne` (`optimizeNe`)
      - `e1 ≠ e2 ==> ¬ (e1 = e2)` (full application, the result is optimized again)
      - `@Ne α ==> fun (x y : α) => ¬ (x = y)` (partial application)
-/

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` on `Prop` operands. -/

-- a ≠ b ===> ¬ (a = b)
#testOptimize [ "NePropVar_1" ] ∀ (a b : Prop), a ≠ b ===> ∀ (a b : Prop), ¬ (a = b)

-- (a ≠ b) = ¬ (a = b) ===> True
#testOptimize [ "NePropVar_2" ] ∀ (a b : Prop), (a ≠ b) = ¬ (a = b) ===> True

-- ¬ (a ≠ b) ===> a = b
#testOptimize [ "NePropVar_3" ] ∀ (a b : Prop), ¬ (a ≠ b) ===> ∀ (a b : Prop), a = b

-- a ≠ a ===> False
#testOptimize [ "NePropRefl_1" ] ∀ (a : Prop), a ≠ a ===> False

-- (a ∨ a) ≠ a ===> False
#testOptimize [ "NePropRefl_2" ] ∀ (a : Prop), (a ∨ a) ≠ a ===> False

-- a ≠ ¬ a ===> True
#testOptimize [ "NePropNeg_1" ] ∀ (a : Prop), a ≠ ¬ a ===> True

-- ¬ a ≠ a ===> True
#testOptimize [ "NePropNeg_2" ] ∀ (a : Prop), (¬ a) ≠ a ===> True

-- a ≠ ¬ ¬ a ===> False
#testOptimize [ "NePropNeg_3" ] ∀ (a : Prop), a ≠ ¬ ¬ a ===> False

-- True ≠ False ===> True
#testOptimize [ "NePropConst_1" ] True ≠ False ===> True

-- False ≠ True ===> True
#testOptimize [ "NePropConst_2" ] False ≠ True ===> True

-- True ≠ True ===> False
#testOptimize [ "NePropConst_3" ] True ≠ True ===> False

-- False ≠ False ===> False
#testOptimize [ "NePropConst_4" ] False ≠ False ===> False

-- a ≠ True ===> ¬ a
#testOptimize [ "NePropConst_5" ] ∀ (a : Prop), a ≠ True ===> ∀ (a : Prop), ¬ a

-- True ≠ a ===> ¬ a
#testOptimize [ "NePropConst_6" ] ∀ (a : Prop), True ≠ a ===> ∀ (a : Prop), ¬ a

-- a ≠ False ===> a
#testOptimize [ "NePropConst_7" ] ∀ (a : Prop), a ≠ False ===> ∀ (a : Prop), a

-- False ≠ a ===> a
#testOptimize [ "NePropConst_8" ] ∀ (a : Prop), False ≠ a ===> ∀ (a : Prop), a

-- (a ≠ b) ≠ (a = b) ===> True
#testOptimize [ "NePropNested_1" ] ∀ (a b : Prop), (a ≠ b) ≠ (a = b) ===> True

-- (a ≠ b) ≠ ¬ (a = b) ===> False
#testOptimize [ "NePropNested_2" ] ∀ (a b : Prop), (a ≠ b) ≠ ¬ (a = b) ===> False

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` on `Nat` operands (the result is optimized again). -/

-- x ≠ y ===> ¬ (x = y)
#testOptimize [ "NeNatVar_1" ] ∀ (x y : Nat), x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)

-- NOTE: reordering applied on operands
-- y ≠ x ===> ¬ (x = y)
#testOptimize [ "NeNatVar_2" ] ∀ (x y : Nat), y ≠ x ===> ∀ (x y : Nat), ¬ (x = y)

-- x ≠ x ===> False
#testOptimize [ "NeNatRefl_1" ] ∀ (x : Nat), x ≠ x ===> False

-- x + y ≠ y + x ===> False
#testOptimize [ "NeNatRefl_2" ] ∀ (x y : Nat), x + y ≠ y + x ===> False

-- n ≠ 0 ===> 0 < n
#testOptimize [ "NeNatZero_1" ] (norm-result: 1) ∀ (n : Nat), n ≠ 0 ===> ∀ (n : Nat), 0 < n

-- 0 ≠ n ===> 0 < n
#testOptimize [ "NeNatZero_2" ] (norm-result: 1) ∀ (n : Nat), 0 ≠ n ===> ∀ (n : Nat), 0 < n

-- n + 1 ≠ 0 ===> True
#testOptimize [ "NeNatZero_3" ] ∀ (n : Nat), n + 1 ≠ 0 ===> True

-- n + m ≠ 0 ===> 0 < n + m
#testOptimize [ "NeNatZero_4" ] (norm-result: 1) ∀ (n m : Nat), n + m ≠ 0 ===> ∀ (n m : Nat), 0 < Nat.add n m

-- n ≠ 5 ===> ¬ (5 = n)
#testOptimize [ "NeNatLit_1" ] (norm-result: 1) ∀ (n : Nat), n ≠ 5 ===> ∀ (n : Nat), ¬ (5 = n)

-- 5 ≠ n ===> ¬ (5 = n)
#testOptimize [ "NeNatLit_2" ] (norm-result: 1) ∀ (n : Nat), 5 ≠ n ===> ∀ (n : Nat), ¬ (5 = n)

-- 5 ≠ 3 ===> True
#testOptimize [ "NeNatLit_3" ] (5 : Nat) ≠ 3 ===> True

-- 5 ≠ 5 ===> False
#testOptimize [ "NeNatLit_4" ] (5 : Nat) ≠ 5 ===> False

-- 2 + 3 ≠ 5 ===> False
#testOptimize [ "NeNatLit_5" ] (2 : Nat) + 3 ≠ 5 ===> False

-- n + 1 ≠ 1 ===> 0 < n
#testOptimize [ "NeNatLit_6" ] (norm-result: 1) ∀ (n : Nat), n + 1 ≠ 1 ===> ∀ (n : Nat), 0 < n

-- ¬ (n ≠ 0) ===> 0 = n
#testOptimize [ "NeNatNot_1" ] (norm-result: 1) ∀ (n : Nat), ¬ (n ≠ 0) ===> ∀ (n : Nat), 0 = n

-- ¬ (x ≠ y) ===> x = y
#testOptimize [ "NeNatNot_2" ] ∀ (x y : Nat), ¬ (x ≠ y) ===> ∀ (x y : Nat), x = y

-- (x ≠ y) = ¬ (x = y) ===> True
#testOptimize [ "NeNatEq_1" ] ∀ (x y : Nat), (x ≠ y) = ¬ (x = y) ===> True

-- (n ≠ 0) = (0 < n) ===> True
#testOptimize [ "NeNatEq_2" ] ∀ (n : Nat), (n ≠ 0) = (0 < n) ===> True

-- (x ≠ y) = (y ≠ x) ===> True
#testOptimize [ "NeNatEq_3" ] ∀ (x y : Nat), (x ≠ y) = (y ≠ x) ===> True

-- (x ≠ y) ↔ ¬ (y = x) ===> True
#testOptimize [ "NeNatIff_1" ] ∀ (x y : Nat), (x ≠ y) ↔ ¬ (y = x) ===> True

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` on `Int` operands. -/

-- x ≠ y ===> ¬ (x = y)
#testOptimize [ "NeIntVar_1" ] ∀ (x y : Int), x ≠ y ===> ∀ (x y : Int), ¬ (x = y)

-- x ≠ x ===> False
#testOptimize [ "NeIntRefl_1" ] ∀ (x : Int), x ≠ x ===> False

-- x ≠ 0 ===> ¬ (0 = x)
#testOptimize [ "NeIntZero_1" ] (norm-result: 1) ∀ (x : Int), x ≠ 0 ===> ∀ (x : Int), ¬ (0 = x)

-- 0 ≠ x ===> ¬ (0 = x)
#testOptimize [ "NeIntZero_2" ] (norm-result: 1) ∀ (x : Int), 0 ≠ x ===> ∀ (x : Int), ¬ (0 = x)

-- 5 ≠ 3 ===> True
#testOptimize [ "NeIntLit_1" ] (5 : Int) ≠ 3 ===> True

-- -5 ≠ 5 ===> True
#testOptimize [ "NeIntLit_2" ] (-5 : Int) ≠ 5 ===> True

-- 5 ≠ 5 ===> False
#testOptimize [ "NeIntLit_3" ] (5 : Int) ≠ 5 ===> False

-- ¬ (x ≠ y) ===> x = y
#testOptimize [ "NeIntNot_1" ] ∀ (x y : Int), ¬ (x ≠ y) ===> ∀ (x y : Int), x = y

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` on `Bool` operands. -/

-- b ≠ true ===> false = b
#testOptimize [ "NeBool_1" ] ∀ (b : Bool), b ≠ true ===> ∀ (b : Bool), false = b

-- b ≠ false ===> true = b
#testOptimize [ "NeBool_2" ] ∀ (b : Bool), b ≠ false ===> ∀ (b : Bool), true = b

-- true ≠ false ===> True
#testOptimize [ "NeBool_3" ] true ≠ false ===> True

-- b ≠ b ===> False
#testOptimize [ "NeBool_4" ] ∀ (b : Bool), b ≠ b ===> False

-- b1 ≠ b2 ===> ¬ (b1 = b2)
#testOptimize [ "NeBool_5" ] ∀ (b1 b2 : Bool), b1 ≠ b2 ===> ∀ (b1 b2 : Bool), ¬ (b1 = b2)

-- (b1 != b2) = true ===> b1 ≠ b2 ===> True
#testOptimize [ "NeBool_6" ] ∀ (b1 b2 : Bool), ((b1 != b2) = true) = (b1 ≠ b2) ===> True

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` on polymorphic and universe-polymorphic operands
    (the `Eq` operator must be built at the universe level of `Ne`). -/

-- ∀ (α : Type) (x y : α), x ≠ y ===> ∀ (α : Type) (x y : α), ¬ (x = y)
#testOptimize [ "NePoly_1" ] ∀ (α : Type) (x y : α), x ≠ y ===> ∀ (α : Type) (x y : α), ¬ (x = y)

-- ∀ (α : Type 1) (x y : α), x ≠ y ===> ∀ (α : Type 1) (x y : α), ¬ (x = y)
#testOptimize [ "NePoly_2" ] ∀ (α : Type 1) (x y : α), x ≠ y ===> ∀ (α : Type 1) (x y : α), ¬ (x = y)

-- ∀ (α : Type 2) (x y : α), x ≠ y ===> ∀ (α : Type 2) (x y : α), ¬ (x = y)
#testOptimize [ "NePoly_3" ] ∀ (α : Type 2) (x y : α), x ≠ y ===> ∀ (α : Type 2) (x y : α), ¬ (x = y)

-- ∀ (α : Type 1) (x : α), x ≠ x ===> False
#testOptimize [ "NePoly_4" ] ∀ (α : Type 1) (x : α), x ≠ x ===> False

-- ∀ (α : Type 1) (x y : α), (x ≠ y) = ¬ (x = y) ===> True
#testOptimize [ "NePoly_5" ] ∀ (α : Type 1) (x y : α), (x ≠ y) = ¬ (x = y) ===> True

-- ∀ (α β : Type), α ≠ β ===> ∀ (α β : Type), ¬ (α = β)
#testOptimize [ "NePoly_6" ] ∀ (α β : Type), α ≠ β ===> ∀ (α β : Type), ¬ (α = β)

-- ∀ (α : Type), α ≠ α ===> False
#testOptimize [ "NePoly_7" ] ∀ (α : Type), α ≠ α ===> False

-- ∀ (α : Type) (x y : List α), x ≠ y ===> ∀ (α : Type) (x y : List α), ¬ (x = y)
#testOptimize [ "NePoly_8" ] ∀ (α : Type) (x y : List α), x ≠ y ===> ∀ (α : Type) (x y : List α), ¬ (x = y)

-- ∀ (α : Type) (x : List α), x ≠ [] ===> ∀ (α : Type) (x : List α), ¬ ([] = x)
#testOptimize [ "NePoly_9" ] ∀ (α : Type) (x : List α), x ≠ [] ===> ∀ (α : Type) (x : List α), ¬ ([] = x)

-- ∀ (α : Type) (x : α) (l : List α), x :: l ≠ [] ===> True
#testOptimize [ "NePoly_10" ] ∀ (α : Type) (x : α) (l : List α), x :: l ≠ [] ===> True

-- ∀ (α : Type) (o : Option α), o ≠ none ===> ∀ (α : Type) (o : Option α), ¬ (none = o)
#testOptimize [ "NePoly_11" ] ∀ (α : Type) (o : Option α), o ≠ none ===> ∀ (α : Type) (o : Option α), ¬ (none = o)

-- ∀ (α : Type) (x : α), some x ≠ none ===> True
#testOptimize [ "NePoly_12" ] ∀ (α : Type) (x : α), some x ≠ none ===> True

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` in the context of hypotheses. -/

-- x ≠ y → ¬ (x = y) ===> True
#testOptimize [ "NeHyp_1" ] ∀ (x y : Nat), x ≠ y → ¬ (x = y) ===> True

-- ¬ (x = y) → x ≠ y ===> True
#testOptimize [ "NeHyp_2" ] ∀ (x y : Nat), ¬ (x = y) → x ≠ y ===> True

-- x ≠ y → x ≠ y ===> True
#testOptimize [ "NeHyp_3" ] ∀ (x y : Nat), x ≠ y → x ≠ y ===> True

-- x ≠ y → y ≠ x ===> True
#testOptimize [ "NeHyp_4" ] ∀ (x y : Nat), x ≠ y → y ≠ x ===> True

-- x = y → x ≠ y ===> ¬ (x = y)
#testOptimize [ "NeHyp_5" ] ∀ (x y : Nat), x = y → x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)

-- x ≠ y → x = y ===> x = y
#testOptimize [ "NeHyp_6" ] ∀ (x y : Nat), x ≠ y → x = y ===> ∀ (x y : Nat), x = y

-- n ≠ 0 → 0 < n ===> True
#testOptimize [ "NeHyp_7" ] ∀ (n : Nat), n ≠ 0 → 0 < n ===> True

-- 0 < n → n ≠ 0 ===> True
#testOptimize [ "NeHyp_8" ] ∀ (n : Nat), 0 < n → n ≠ 0 ===> True

-- n ≠ 0 → n = 0 ===> 0 = n
#testOptimize [ "NeHyp_9" ] (norm-result: 1) ∀ (n : Nat), n ≠ 0 → n = 0 ===> ∀ (n : Nat), 0 = n

-- x < y → x ≠ y ===> True
#testOptimize [ "NeHyp_10" ] ∀ (x y : Nat), x < y → x ≠ y ===> True

-- x < y → y ≠ x ===> True
#testOptimize [ "NeHyp_11" ] ∀ (x y : Int), x < y → y ≠ x ===> True

-- (x ≠ y) ∧ (x = y) ===> False
#testOptimize [ "NeHyp_12" ] ∀ (x y : Nat), (x ≠ y) ∧ (x = y) ===> False

-- (x = y) ∧ (x ≠ y) ===> False
#testOptimize [ "NeHyp_13" ] ∀ (x y : Nat), (x = y) ∧ (x ≠ y) ===> False

-- (x ≠ y) ∨ (x = y) ===> True
#testOptimize [ "NeHyp_14" ] ∀ (x y : Nat), (x ≠ y) ∨ (x = y) ===> True

-- (x = y) ∨ (x ≠ y) ===> True
#testOptimize [ "NeHyp_15" ] ∀ (x y : Nat), (x = y) ∨ (x ≠ y) ===> True

-- (x ≠ y) ∧ (x ≠ y) ===> ¬ (x = y)
#testOptimize [ "NeHyp_16" ] ∀ (x y : Nat), (x ≠ y) ∧ (x ≠ y) ===> ∀ (x y : Nat), ¬ (x = y)

-- x ≠ y → f x = f y → False ===> ¬ (x = y) → f x = f y → False
#testOptimize [ "NeHyp_17" ] ∀ (f : Nat → Nat) (x y : Nat), x ≠ y → f x = f y → False ===>
                            ∀ (f : Nat → Nat) (x y : Nat), ¬ (x = y) → ¬ (f x = f y)

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` as condition of `if then else`. -/

-- if x ≠ y then a else b ===> Blaster.dite' (x = y) (fun _ => b) (fun _ => a)
#testOptimize [ "NeIte_1" ] ∀ (x y a b : Nat), (if x ≠ y then a else b) = (if x = y then b else a) ===> True

-- if n ≠ 0 then a else b ===> Blaster.dite' (0 < n) (fun _ => a) (fun _ => b)
#testOptimize [ "NeIte_2" ] ∀ (n a b : Nat), (if n ≠ 0 then a else b) = (if 0 < n then a else b) ===> True

-- (if x ≠ x then a else b) = b ===> True
#testOptimize [ "NeIte_3" ] ∀ (x a b : Nat), (if x ≠ x then a else b) = b ===> True

-- x ≠ y → (if x ≠ y then x else y) = x ===> True
#testOptimize [ "NeIte_4" ] ∀ (x y : Nat), x ≠ y → (if x ≠ y then x else y) = x ===> True

/-! Test cases for `e1 ≠ e2 ==> ¬ (e1 = e2)` with `decide`. -/

-- decide (x ≠ y) = true ===> ¬ (x = y)
#testOptimize [ "NeDecide_1" ] ∀ (x y : Nat), decide (x ≠ y) = true ===> ∀ (x y : Nat), ¬ (x = y)

-- decide (x ≠ y) = false ===> x = y
#testOptimize [ "NeDecide_2" ] ∀ (x y : Nat), decide (x ≠ y) = false ===> ∀ (x y : Nat), x = y

-- (decide (x ≠ y)) = !(x == y) ===> True
#testOptimize [ "NeDecide_3" ] ∀ (x y : Nat), (decide (x ≠ y)) = (!(x == y)) ===> True

/-! Test cases for the partial application `@Ne α ==> fun (x y : α) => ¬ (x = y)`.
    The generated lambda must have the same normal form as the one obtained from
    `fun (x y : α) => x ≠ y` (i.e., `¬ (x = y)` with `x` the outermost binder), otherwise
    `@Ne α = fun x y => x ≠ y` is not reduced to `True`.
-/

-- ∀ (p : Nat → Nat → Prop), p = @Ne Nat ===> ∀ (p : Nat → Nat → Prop), p = fun (x y : Nat) => ¬ (x = y)
#testOptimize [ "NePartial_1" ] ∀ (p : Nat → Nat → Prop), p = @Ne Nat ===>
                               ∀ (p : Nat → Nat → Prop), p = fun (x y : Nat) => ¬ (x = y)

-- ∀ (p : Nat → Nat → Prop), @Ne Nat = p ===> ∀ (p : Nat → Nat → Prop), p = fun (x y : Nat) => ¬ (x = y)
#testOptimize [ "NePartial_2" ] ∀ (p : Nat → Nat → Prop), @Ne Nat = p ===>
                               ∀ (p : Nat → Nat → Prop), p = fun (x y : Nat) => ¬ (x = y)

-- @Ne Nat = fun (x y : Nat) => ¬ (x = y) ===> True
#testOptimize [ "NePartial_3" ] @Ne Nat = fun (x y : Nat) => ¬ (x = y) ===> True

-- @Ne Nat = fun (x y : Nat) => x ≠ y ===> True
#testOptimize [ "NePartial_4" ] @Ne Nat = fun (x y : Nat) => x ≠ y ===> True

-- universe polymorphic partial application
#testOptimize [ "NePartial_5" ]
  ∀ (α : Type 1) (p : α → α → Prop), p = @Ne α ===>
  ∀ (α : Type 1) (p : α → α → Prop), p = fun (x y : α) => ¬ (x = y)

-- ∀ (p : Type → Type → Prop), p = @Ne Type ===> ∀ (p : Type → Type → Prop), p = fun (x y : Type) => ¬ (x = y)
#testOptimize [ "NePartial_6" ]
  ∀ (p : Type → Type → Prop), p = @Ne Type ===>
  ∀ (p : Type → Type → Prop), p = fun (x y : Type) => ¬ (x = y)

-- partial application as higher-order argument
#testOptimize [ "NePartial_7" ]
  ∀ (l : List Nat), List.Pairwise Ne l ===>
  ∀ (l : List Nat), List.Pairwise (fun (x y : Nat) => ¬ (x = y)) l

-- partial application applied through a higher-order function
#testOptimize [ "NePartial_8" ] ∀ (x y : Nat), flip (@Ne Nat) x y ===> ∀ (x y : Nat), ¬ (x = y)

-- (@Ne Nat) x y ===> ¬ (x = y)
#testOptimize [ "NePartial_9" ] ∀ (x y : Nat), (@Ne Nat) x y ===> ∀ (x y : Nat), ¬ (x = y)

-- partial application with two arguments
#testOptimize [ "NePartial_10" ] (norm-result: 1) ∀ (p : Nat → Prop), p = Ne 0 ===> ∀ (p : Nat → Prop), p = fun (y : Nat) => 0 < y

end Test.OptimizeNe
