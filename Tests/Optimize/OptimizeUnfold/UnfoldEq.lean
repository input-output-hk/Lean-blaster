import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldEq

/-! ## Test objectives to validate `Eq unfolding -/


/-! Test cases to validate unfolding of `Eq only when reduced to a constant value or via rewriting. -/

-- ∀ (p : Prop), True = p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldEq_1" ] ∀ (p : Prop), True = p ===> ∀ (p : Prop), p

-- ∀ (p : Prop), False = p ===> ∀ (p : Prop), ¬ p
#testOptimize [ "UnfoldEq_2" ] ∀ (p : Prop), False = p ===> ∀ (p : Prop), ¬ p

-- ∀ (p : Prop), p ≠ True ===> ∀ (p q : Prop), ¬ p
#testOptimize [ "UnfoldEq_3", proof ] ∀ (p : Prop), p ≠ True ===> ∀ (p : Prop), ¬ p

-- ∀ (p : Prop), p ≠ False ===> ∀ (p q : Prop), p
#testOptimize [ "UnfoldEq_4", proof ] ∀ (p : Prop), p ≠ False ===> ∀ (p : Prop), p

-- true = true ===> True
#testOptimize [ "UnfoldEq_5" ] true = true ===> True

-- true = false ===> False
#testOptimize [ "UnfoldEq_6" ] true = false ===> False

-- true ≠ true ===> False
#testOptimize [ "UnfoldEq_7", proof ] true ≠ true ===> False

-- true ≠ false ===> True
#testOptimize [ "UnfoldEq_8", proof ] true ≠ false ===> True

-- ∀ (a : Bool), a = a ===> True
#testOptimize [ "UnfoldEq_9" ] ∀ (a : Bool), a = a ===> True

-- ∀ (a : Bool), a ≠ a ===> False
#testOptimize [ "UnfoldEq_10", proof ] ∀ (a : Bool), a ≠ a ===> False

-- (10 : Int) = 10 ===> True
#testOptimize [ "UnfoldEq_11" ] (10 : Int) = 10 ===> True

-- (10 : Int) ≠ 10 ===> False
#testOptimize [ "UnfoldEq_12", proof ] (10 : Int) ≠ 10 ===> False

-- (10 : Int) = 20 ===> False
#testOptimize [ "UnfoldEq_13" ] (10 : Int) = 20 ===> False

-- (10 : Int) ≠ 20 ===> True
#testOptimize [ "UnfoldEq_14", proof ] (10 : Int) ≠ 20 ===> True

-- ∀ (x : Int), x = x ===> True
#testOptimize [ "UnfoldEq_15" ] ∀ (x : Int), x = x ===> True

-- ∀ (x : Int), x ≠ x ===> False
#testOptimize [ "UnfoldEq_16", proof ] ∀ (x : Int), x ≠ x ===> False

-- (10 : Nat) = 10 ===> True
#testOptimize [ "UnfoldEq_17" ] (10 : Nat) = 10 ===> True

-- (10 : Nat) ≠ 10 ===> False
#testOptimize [ "UnfoldEq_18", proof ] (10 : Nat) ≠ 10 ===> False

-- (10 : Nat) = 20 ===> False
#testOptimize [ "UnfoldEq_19" ] (10 : Nat) = 20 ===> False

-- (10 : Nat) ≠ 20 ===> True
#testOptimize [ "UnfoldEq_20", proof ] (10 : Nat) ≠ 20 ===> True

-- ∀ (x : Nat), x = x ===> True
#testOptimize [ "UnfoldEq_21" ] ∀ (x : Nat), x = x ===> True

-- ∀ (x : Nat), x ≠ x ===> False
#testOptimize [ "UnfoldEq_22", proof ] ∀ (x : Nat), x ≠ x ===> False


-- (List.nil : List Nat) = List.nil ===> True
#testOptimize [ "UnfoldEq_23" ] (List.nil : List Nat) = List.nil ===> True

-- (List.nil : List Nat) ≠ List.nil ===> False
#testOptimize [ "UnfoldEq_24", proof ] (List.nil : List Nat) ≠ List.nil ===> False

variable (a : Nat)
variable (b : Nat)
variable (c : Nat)

-- (List.nil : List Nat) = [a, b, c] ===> False
#testOptimize [ "UnfoldEq_25" ] (List.nil : List Nat) = [a, b, c] ===> False

-- (List.nil : List Nat) ≠ [a, b, c] ===> True
#testOptimize [ "UnfoldEq_26", proof ] (List.nil : List Nat) ≠ [a, b, c] ===> True

-- ∀ (x : List Nat), x = x ===> True
#testOptimize [ "UnfoldEq_27" ] ∀ (x : List Nat), x = x ===> True

-- ∀ (x : List Nat), x ≠ x ===> False
#testOptimize [ "UnfoldEq_28", proof ] ∀ (x : List Nat), x ≠ x ===> False

-- ∀ (α : Type), (List.nil : List α) = List.nil ===> True
#testOptimize [ "UnfoldEq_29" ] ∀ (α : Type), (List.nil : List α) = List.nil ===> True

-- ∀ (α : Type), (List.nil : List α) ≠ List.nil ===> False
#testOptimize [ "UnfoldEq_30", proof ] ∀ (α : Type), (List.nil : List α) ≠ List.nil ===> False

-- ∀ (α : Type) (x y z : α), List.nil = [x, y, z] ===> False
#testOptimize [ "UnfoldEq_31" ] ∀ (α : Type) (x y z : α), List.nil = [x, y, z] ===> False

-- ∀ (α : Type) (x y z : α), List.nil ≠ [x, y, z] ===> True
#testOptimize [ "UnfoldEq_32", proof ] ∀ (α : Type) (x y z : α), List.nil ≠ [x, y, z] ===> True

-- ∀ (α : Type) (x : List α), x = x ===> True
#testOptimize [ "UnfoldEq_33" ] ∀ (α : Type) (x : List α), x = x ===> True

-- ∀ (α : Type) (x : List α), x ≠ x ===> False
#testOptimize [ "UnfoldEq_34", proof ] ∀ (α : Type) (x : List α), x ≠ x ===> False


/-! Test cases to validate when `Eq must not be unfolded -/

-- ∀ (p q : Prop), p = q ===> ∀ (p q : Prop), p = q
#testOptimize [ "EqNotUnfolded_1", proof ] ∀ (p q : Prop), p = q ===> ∀ (p q : Prop), p = q

-- ∀ (p q : Prop), p ≠ q ===> ∀ (p q : Prop), ¬ p = q
#testOptimize [ "EqNotUnfolded_2", proof ] ∀ (p q : Prop), p ≠ q ===> ∀ (p q : Prop), ¬ p = q

-- ∀ (a b : Bool), a = b ===> ∀ (a b : Bool), a = b
#testOptimize [ "EqNotUnfolded_3", proof ] ∀ (a b : Bool), a = b ===> ∀ (a b : Bool), a = b

-- ∀ (a b : Bool), a ≠ b ===> ∀ (a b : Bool), ¬ a = b
#testOptimize [ "EqNotUnfolded_4", proof ] ∀ (a b : Bool), a ≠ b ===> ∀ (a b : Bool), ¬ a = b

-- ∀ (x y : Int), x = y ===> ∀ (x y : Int), x = y
#testOptimize [ "EqNotUnfolded_5", proof ] ∀ (x y : Int), x = y ===> ∀ (x y : Int), x = y

-- ∀ (x y : Int), x ≠ y ===> ∀ (x y : Int), ¬ x = y
#testOptimize [ "EqNotUnfolded_6", proof ] ∀ (x y : Int), x ≠ y ===> ∀ (x y : Int), ¬ x = y

-- ∀ (x y : Nat), x = y ===> ∀ (x y : Nat), x = y
#testOptimize [ "EqNotUnfolded_7", proof ] ∀ (x y : Nat), x = y ===> ∀ (x y : Nat), x = y

-- ∀ (x y : Nat), x ≠ y ===> ∀ (x y : Nat), ¬ x = y
#testOptimize [ "EqNotUnfolded_8", proof ] ∀ (x y : Nat), x ≠ y ===> ∀ (x y : Nat), ¬ x = y

-- ∀ (x y : List Nat), x = y ===> ∀ (x y : List Nat), x = y
#testOptimize [ "EqNotUnfolded_9", proof ] ∀ (x y : List Nat), x = y ===> ∀ (x y : List Nat), x = y

-- ∀ (x y : List Nat), x ≠ y ===> ∀ (x y : List Nat), ¬ x = y
#testOptimize [ "EqNotUnfolded_10", proof ] ∀ (x y : List Nat), x ≠ y ===> ∀ (x y : List Nat), ¬ x = y

-- ∀ (x y : List α), x = y ===> ∀ (x y : List α), x = y
#testOptimize [ "EqNotUnfolded_11", proof ] ∀ (α : Type) (x y : List α), x = y ===> ∀ (α : Type) (x y : List α), x = y

-- ∀ (x y : List α), x ≠ y ===> ∀ (x y : List α), ¬ x = y
#testOptimize [ "EqNotUnfolded_12", proof ] ∀ (α : Type) (x y : List α), x ≠ y ===> ∀ (α : Type) (x y : List α), ¬ x = y


end Tests.UnfoldEq
