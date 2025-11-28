import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.FunEq
/-! ## Test objectives to validate function equality simplification rules -/

/-! Define a test function that is NOT opaque and commutative -/
def testFun : Nat → Nat → Nat := fun x y => x + 2 * y

def testFun2 : Nat → Nat → Nat → Nat := fun x y z => x + y + z

/-! Test cases for function equality => conjunction of argument equalities -/

-- Nat.succ x = Nat.succ y => x = y
#testOptimize [ "FunEqSimple_1" ] ∀ (x y : Nat), (Nat.succ x = Nat.succ y) ===> ∀ (x y : Nat), x = y

-- List.replicate n x = List.replicate m y => n = m ∧ x = y
#testOptimize [ "FunEqSimple_2" ] ∀ (n m x y : Nat), (List.replicate n x = List.replicate m y) ===>
                                   ∀ (n m x y : Nat), n = m ∧ x = y

-- List.take with multiple arguments
#testOptimize [ "FunEqSimple_3" ] ∀ (n m : Nat) (xs ys : List Nat),
                                   (List.take n xs = List.take m ys) ===>
                                   ∀ (n m : Nat) (xs ys : List Nat), n = m ∧ xs = ys

/-! Test cases ensuring opaque commutative functions are NOT simplified -/

-- Nat.add should NOT be simplified (opaque commutative)
#testOptimize [ "FunEqOpaqueComm_1" ] ∀ (x1 x2 y1 y2 : Nat),
                                       (Nat.add x1 x2 = Nat.add y1 y2) ===>
                                       ∀ (x1 x2 y1 y2 : Nat), Nat.add x1 x2 = Nat.add y1 y2

-- Nat.mul should NOT be simplified (opaque commutative)
#testOptimize [ "FunEqOpaqueComm_2" ] ∀ (x1 x2 y1 y2 : Nat),
                                       (Nat.mul x1 x2 = Nat.mul y1 y2) ===>
                                       ∀ (x1 x2 y1 y2 : Nat), Nat.mul x1 x2 = Nat.mul y1 y2

-- Int.add should NOT be simplified (opaque commutative)
#testOptimize [ "FunEqOpaqueComm_3" ] ∀ (x1 x2 y1 y2 : Int),
                                       (Int.add x1 x2 = Int.add y1 y2) ===>
                                       ∀ (x1 x2 y1 y2 : Int), Int.add x1 x2 = Int.add y1 y2

-- Int.mul should NOT be simplified (opaque commutative)
#testOptimize [ "FunEqOpaqueComm_4" ] ∀ (x1 x2 y1 y2 : Int),
                                       (Int.mul x1 x2 = Int.mul y1 y2) ===>
                                       ∀ (x1 x2 y1 y2 : Int), Int.mul x1 x2 = Int.mul y1 y2

-- Using + syntax for Nat (maps to Nat.add) should NOT be simplified
-- Note: + gets normalized to Nat.add during optimization
#testOptimize [ "FunEqOpaqueComm_5" ] ∀ (x1 x2 y1 y2 : Nat),
                                       (x1 + x2 = y1 + y2) ===>
                                       ∀ (x1 x2 y1 y2 : Nat), Nat.add x1 x2 = Nat.add y1 y2

-- Using * syntax for Nat (maps to Nat.mul) should NOT be simplified
-- Note: * gets normalized to Nat.mul during optimization
#testOptimize [ "FunEqOpaqueComm_6" ] ∀ (x1 x2 y1 y2 : Nat),
                                       (x1 * x2 = y1 * y2) ===>
                                       ∀ (x1 x2 y1 y2 : Nat), Nat.mul x1 x2 = Nat.mul y1 y2

/-! Test cases ensuring rules are NOT applied when they shouldn't be -/

-- Different functions remain unchanged (note: operands may be reordered)
#testOptimize [ "FunEqUnchanged_1" ] ∀ (n m : Nat) (xs ys : List Nat),
                                      (List.take n xs = List.drop m ys) ===>
                                      ∀ (n m : Nat) (xs ys : List Nat), List.drop m ys = List.take n xs

-- Variables remain unchanged
#testOptimize [ "FunEqUnchanged_2" ] ∀ (f g : Nat → Nat) (x : Nat), (f x = g x) ===>
                                      ∀ (f g : Nat → Nat) (x : Nat), f x = g x

-- No arguments => remains unchanged
#testOptimize [ "FunEqUnchanged_3" ] ∀ (x y : Nat), (x = y) ===> ∀ (x y : Nat), x = y

/-! Test cases for nested function equality (recursive application) -/

-- Nat.succ (Nat.succ x) = Nat.succ (Nat.succ y) => x = y
#testOptimize [ "FunEqNested_1" ] ∀ (x y : Nat), (Nat.succ (Nat.succ x) = Nat.succ (Nat.succ y)) ===>
                                   ∀ (x y : Nat), x = y

-- List.replicate with Nat.succ arguments
#testOptimize [ "FunEqNested_2" ] ∀ (x y z w : Nat),
                                   (List.replicate (Nat.succ x) (Nat.succ y) =
                                    List.replicate (Nat.succ z) (Nat.succ w)) ===>
                                   ∀ (x y z w : Nat), x = z ∧ y = w

/-! Test cases with constructors inside function arguments -/

-- Function with constructor arguments should use ctor rules for inner parts
#testOptimize [ "FunEqWithCtor_1" ] ∀ (x1 x2 y1 y2 : Nat),
                                     (List.replicate 5 (Option.some x1) =
                                      List.replicate 5 (Option.some y1)) ===>
                                     ∀ (x1 y1 : Nat), x1 = y1

-- This tests that we properly handle functions wrapping constructors
#testOptimize [ "FunEqWithCtor_2" ] ∀ (x1 x2 y1 y2 : Nat) (xs ys : List Nat),
                                     (List.replicate 3 (List.cons x1 xs) =
                                      List.replicate 3 (List.cons y1 ys)) ===>
                                     ∀ (x1 y1 : Nat) (xs ys : List Nat), x1 = y1 ∧ xs = ys

/-! Test cases showing constructors take precedence over function rules -/

-- Constructor rules should be tried before function rules
-- Option.some is a constructor, not a function
#testOptimize [ "FunEqPrecedence_1" ] ∀ (x y : Nat), (Option.some x = Option.some y) ===>
                                       ∀ (x y : Nat), x = y

-- List.cons is a constructor
#testOptimize [ "FunEqPrecedence_2" ] ∀ (x y : Nat) (xs ys : List Nat),
                                       (List.cons x xs = List.cons y ys) ===>
                                       ∀ (x y : Nat) (xs ys : List Nat), x = y ∧ xs = ys

end Test.FunEq
