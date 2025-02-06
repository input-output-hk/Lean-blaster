import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldBEq

/-! ## Test objectives to validate `BEq.beq unfolding -/

/-! Test cases to validate unfolding of `BEq.beq only when reduced to a constant value or via rewriting. -/

-- ∀ (a : Bool), true == a ===> ∀ (a : Bool), true = a
#testOptimize [ "UnfoldBEq_1" ] ∀ (a : Bool), true == a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), false == a ===> ∀ (a : Bool), false = a
#testOptimize [ "UnfoldBEq_2" ] ∀ (a : Bool), false == a ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), true != a ===> ∀ (a : Bool), true = a
#testOptimize [ "UnfoldBEq_3" ] ∀ (a : Bool), true != a ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), false != a ===> ∀ (a : Bool), true = a
#testOptimize [ "UnfoldBEq_4" ] ∀ (a : Bool), false != a ===> ∀ (a : Bool), true = a

-- true != true ===> false
#testOptimize [ "UnfoldBEq_5" ] true != true ===> false

-- true != false ===> true
#testOptimize [ "UnfoldBEq_6" ] true != false ===> true

-- ∀ (a : Bool), a == a ===> True
#testOptimize [ "UnfoldBEq_7" ] ∀ (a : Bool), a == a ===> True

-- ∀ (a : Bool), a != a ===> False
#testOptimize [ "UnfoldBEq_8" ] ∀ (a : Bool), a != a ===> False

-- (10 : Int) == 10 ===> true
#testOptimize [ "UnfoldBEq_9" ] (10 : Int) == 10 ===> true

-- (10 : Int) != 10 ===> false
#testOptimize [ "UnfoldBEq_10" ] (10 : Int) != 10 ===> false

-- (10 : Int) == 20 ===> false
#testOptimize [ "UnfoldBEq_11" ] (10 : Int) == 20 ===> false

-- (10 : Int) != 20 ===> true
#testOptimize [ "UnfoldBEq_12" ] (10 : Int) != 20 ===> true

-- ∀ (x : Int), x == x ===> True
#testOptimize [ "UnfoldBEq_13" ] ∀ (x : Int), x == x ===> True

-- ∀ (x : Int), x != x ===> False
#testOptimize [ "UnfoldBEq_14" ] ∀ (x : Int), x != x ===> False

-- (10 : Nat) == 10 ===> true
#testOptimize [ "UnfoldBEq_15" ] (10 : Nat) == 10 ===> true

-- (10 : Nat) != 10 ===> false
#testOptimize [ "UnfoldBEq_16" ] (10 : Nat) != 10 ===> false

-- (10 : Nat) == 20 ===> false
#testOptimize [ "UnfoldBEq_17" ] (10 : Nat) == 20 ===> false

-- (10 : Nat) != 20 ===> True
#testOptimize [ "UnfoldBEq_18" ] (10 : Nat) != 20 ===> true

-- ∀ (x : Nat), x == x ===> True
#testOptimize [ "UnfoldBEq_19" ] ∀ (x : Nat), x == x ===> True

-- ∀ (x : Nat), x != x ===> False
#testOptimize [ "UnfoldBEq_20" ] ∀ (x : Nat), x != x ===> False

-- (List.nil : List Nat) == List.nil ===> true
#testOptimize [ "UnfoldBEq_21" ] (List.nil : List Nat) == List.nil ===> true

-- (List.nil : List Nat) != List.nil ===> false
#testOptimize [ "UnfoldBEq_22" ] (List.nil : List Nat) != List.nil ===> false

opaque a : Nat
opaque b : Nat
opaque c : Nat

-- (List.nil : List Nat) == [a, b, c] ===> false
#testOptimize [ "UnfoldBEq_23" ] (List.nil : List Nat) == [a, b, c] ===> false

-- (List.nil : List Nat) != [a, b, c] ===> true
#testOptimize [ "UnfoldBEq_24" ] (List.nil : List Nat) != [a, b, c] ===> true

-- ∀ (α : Type), [BEq α] → (List.nil : List α) == List.nil ===> True
#testOptimize [ "UnfoldBEq_25" ] ∀ (α : Type), [BEq α] → (List.nil : List α) == List.nil ===> True

-- ∀ (α : Type), [BEq α] → (List.nil : List α) != List.nil ===> False
#testOptimize [ "UnfoldBEq_26" ] ∀ (α : Type), [BEq α] → (List.nil : List α) != List.nil ===> False

-- ∀ (α : Type) (x y z : α), [BEq α] → List.nil == [x, y, z] ===> False
#testOptimize [ "UnfoldBEq_27" ] ∀ (α : Type) (x y z : α), [BEq α] → List.nil == [x, y, z] ===> False

-- ∀ (α : Type) (x y z : α), [BEq α] → List.nil != [x, y, z] ===> True
#testOptimize [ "UnfoldBEq_28" ] ∀ (α : Type) (x y z : α), [BEq α] → List.nil != [x, y, z] ===> True

-- "xyz" == "xyz" ===> true
#testOptimize [ "UnfoldBEq_29" ] "xyz" == "xyz" ===> true

-- "xyz" != "xyz" ===> false
#testOptimize [ "UnfoldBEq_30" ] "xyz" != "xyz" ===> false

-- "xyz" == "xyzzzz" ===> false
#testOptimize [ "UnfoldBEq_31" ] "xyz" == "xyzzzz" ===> false

-- "xyz" != "xyzzzz" ===> true
#testOptimize [ "UnfoldBEq_31" ] "xyz" != "xyzzzz" ===> true

-- ∀ (s : String), s == s ===> True
#testOptimize [ "UnfoldBEq_32" ] ∀ (s : String), s == s ===> True

-- ∀ (s : String), s != s ===> False
#testOptimize [ "UnfoldBEq_33" ] ∀ (s : String), s != s ===> False



/-! Test cases to validate when `BEq.beq` must be unfolded (i.e., for user defined types) -/

-- ∀ (α : Type) (x y : List α), [BEq α] → x == y ===> ∀ (α : Type) (x y : List α), [BEq α] → true = (List.beq x y)
#testOptimize [ "UnfoldNonOpaqueBEq_1"] ∀ (α : Type) (x y : List α), [BEq α] → x == y ===>
                                        ∀ (α : Type) (x y : List α), [BEq α] → true = (List.beq x y)

-- ∀ (α : Type) (x y : List α), [BEq α] → x != y ===> ∀ (α : Type) (x y : List α), [BEq α] → false = List.beq x y
#testOptimize [ "UnfoldNonOpaqueBEq_2"] ∀ (α : Type) (x y : List α), [BEq α] → x != y ===>
                                        ∀ (α : Type) (x y : List α), [BEq α] → false = List.beq x y

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Repr

def color_beq (x : Color) (y : Color) : Bool :=
  match x, y with
  | Color.transparent, Color.transparent => true
  | Color.red c1, Color.red c2 => color_beq c1 c2
  | _, _ => false

-- providing a BEq instance not satisfying refl, symm and trans properties
instance instBEqColor : BEq Color where
  beq a b := color_beq a b

-- ∀ (x y : Color), x == y ===> ∀ (x y : Color), true = color_beq x y
#testOptimize [ "UnfoldNonOpaqueBEq_3"] ∀ (x y : Color), x == y ===> ∀ (x y : Color), true = color_beq x y

-- ∀ (x y : Color), x != y ===> ∀ (x y : Color), false = color_beq x y
#testOptimize [ "UnfoldNonOpaqueBEq_4"] ∀ (x y : Color), x != y ===> ∀ (x y : Color), false = color_beq x y


/-! Test cases to validate when `BEq.beq must not be unfolded -/

-- ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnfolded_1" ] ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), a = b

-- ∀ (a b : Bool), a != b ===> ∀ (a b : Bool), ¬ (a = b)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BEqNotUnfolded_2" ] ∀ (a b : Bool), a != b ===> ∀ (a b : Bool), ¬ a = b

-- ∀ (x y : Int), x == y ===> ∀ (x y : Int), x = y
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnfolded_3" ] ∀ (x y : Int), x == y ===> ∀ (x y : Int), x = y

-- ∀ (x y : Int), x != y ===> ∀ (a : Bool), ¬ (x = y)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BEqNotUnfolded_4" ] ∀ (x y : Int), x != y ===> ∀ (x y : Int), ¬ (x = y)

-- ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), x = y
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnfolded_5" ] ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), x = y

-- ∀ (x y : Nat), x != y ===> ∀ (a : Bool), ¬ (x = y)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BEqNotUnfolded_6" ] ∀ (x y : Nat), x != y ===> ∀ (x y : Nat), ¬ (x = y)

-- ∀ (α : Type) (x y : α), [BEq α] → x == y ===> ∀ (α : Type) (x y : α), [BEq α] → true = (x == y)
-- NOTE : type class constraint case
#testOptimize [ "BEqNotUnfolded_7" ] ∀ (α : Type) (x y : α), [BEq α] → x == y ===>
                                     ∀ (α : Type) (x y : α), [BEq α] → true = (x == y)

-- ∀ (α : Type) (x y : α), [BEq α] → x != y ===> ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)
-- NOTE : type class constraint case
#testOptimize [ "BEqNotUnfolded_8" ] ∀ (α : Type) (x y : α), [BEq α] → x != y ===>
                                     ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)

-- ∀ (s t : String), s == t ===> ∀ (s t : String), s = t
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnfolded_9" ] ∀ (s t : String), s == t ===> ∀ (s t : String), s = t

-- ∀ (s t : String), s != t ===> ∀ (s t : String), ¬ (s = t)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BEqNotUnfolded_10" ] ∀ (s t : String), s != t ===> ∀ (s t : String), ¬ (s = t)


end Tests.UnfoldBEq
