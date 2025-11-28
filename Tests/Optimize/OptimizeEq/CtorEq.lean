import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.CtorEq
/-! ## Test objectives to validate constructor equality simplification rules -/

/-! Test cases for different constructors => False -/

-- Option.none ≠ Option.some
#testOptimize [ "CtorEqDiff_1" ] ∀ (x : Nat), (Option.none = Option.some x) ===> False

-- List.nil ≠ List.cons
#testOptimize [ "CtorEqDiff_2" ] ∀ (x : Nat) (xs : List Nat), (List.nil = List.cons x xs) ===> False

-- Bool.false ≠ Bool.true
#testOptimize [ "CtorEqDiff_3" ] (false = true) ===> False

-- Sum.inl ≠ Sum.inr
#testOptimize [ "CtorEqDiff_4" ] ∀ (x y : Nat), (Sum.inl x = Sum.inr y) ===> False

-- Prod with different constructors in nested position
#testOptimize [ "CtorEqDiff_5" ] ∀ (x y : Nat), ((x, Option.none) = (y, Option.some 5)) ===> False

/-! Test cases for same constructor with arguments => conjunction of equalities -/

-- Option.some x = Option.some y => x = y
#testOptimize [ "CtorEqSame_1" ] ∀ (x y : Nat), (Option.some x = Option.some y) ===> ∀ (x y : Nat), x = y

-- List.cons x xs = List.cons y ys => x = y ∧ xs = ys
#testOptimize [ "CtorEqSame_2" ] ∀ (x y : Nat) (xs ys : List Nat), (List.cons x xs = List.cons y ys) ===>
                                   ∀ (x y : Nat) (xs ys : List Nat), x = y ∧ xs = ys

-- Pair equality => component equalities
#testOptimize [ "CtorEqSame_3" ] ∀ (x1 x2 y1 y2 : Nat), ((x1, x2) = (y1, y2)) ===>
                                   ∀ (x1 x2 y1 y2 : Nat), x1 = y1 ∧ x2 = y2

-- Sum.inl x = Sum.inl y => x = y
#testOptimize [ "CtorEqSame_4" ] ∀ (x y : Nat), (Sum.inl (α := Nat) (β := Nat) x = Sum.inl y) ===> ∀ (x y : Nat), x = y

-- Sum.inr x = Sum.inr y => x = y
#testOptimize [ "CtorEqSame_5" ] ∀ (x y : Nat), (Sum.inr (α := Nat) (β := Nat) x = Sum.inr y) ===> ∀ (x y : Nat), x = y

/-! Test cases for nested constructor equality (recursive application) -/

-- Nested Option: Option.some (Option.some x) = Option.some (Option.some y) => x = y
#testOptimize [ "CtorEqNested_1" ] ∀ (x y : Nat), (Option.some (Option.some x) = Option.some (Option.some y)) ===>
                                     ∀ (x y : Nat), x = y

-- Nested Option with different inner constructors => False
#testOptimize [ "CtorEqNested_2" ] ∀ (x : Nat), (Option.some Option.none = Option.some (Option.some x)) ===> False

-- List with pairs: [(x1, x2)] = [(y1, y2)] should decompose properly
-- Note: conjunction is left-associative: ((x1 = y1) ∧ (x2 = y2)) ∧ (xs = ys)
#testOptimize [ "CtorEqNested_3" ] ∀ (x1 x2 y1 y2 : Nat) (xs ys : List (Nat × Nat)),
                                     (List.cons (x1, x2) xs = List.cons (y1, y2) ys) ===>
                                     ∀ (x1 x2 y1 y2 : Nat) (xs ys : List (Nat × Nat)),
                                     (x1 = y1 ∧ x2 = y2) ∧ xs = ys

-- Triple nested: ((x1, x2), x3) = ((y1, y2), y3) => (x1 = y1 ∧ x2 = y2) ∧ x3 = y3
-- Note: conjunction is left-associative
#testOptimize [ "CtorEqNested_4" ] ∀ (x1 x2 x3 y1 y2 y3 : Nat),
                                     (((x1, x2), x3) = ((y1, y2), y3)) ===>
                                     ∀ (x1 x2 x3 y1 y2 y3 : Nat),
                                     ((x1 = y1 ∧ x2 = y2) ∧ x3 = y3)

/-! Test cases ensuring rules are NOT applied when they shouldn't be -/

-- Variables remain unchanged
#testOptimize [ "CtorEqUnchanged_1" ] ∀ (x y : Option Nat), (x = y) ===> ∀ (x y : Option Nat), x = y

-- Partially applied constructors remain unchanged
#testOptimize [ "CtorEqUnchanged_2" ] ∀ (f g : Nat → List Nat) (x : Nat),
                                       (f x = g x) ===> ∀ (f g : Nat → List Nat) (x : Nat), f x = g x

-- Mixed constructor and non-constructor
#testOptimize [ "CtorEqUnchanged_3" ] ∀ (x : Nat) (opt : Option Nat),
                                       (Option.some x = opt) ===> ∀ (x : Nat) (opt : Option Nat), Option.some x = opt

-- Note: Nat.succ is a regular function, not a constructor, so it WILL be simplified
-- This test moved to FunEq.lean as it tests function equality, not constructor equality

/-! Test cases with actual values -/

-- Concrete constructors with literals
#testOptimize [ "CtorEqLiteral_1" ] (Option.some 5 = Option.some 5) ===> True

-- Different literals in same constructor
#testOptimize [ "CtorEqLiteral_2" ] (Option.some 5 = Option.some 10) ===> False

-- Pair with literals
#testOptimize [ "CtorEqLiteral_3" ] ((5, 10) = (5, 10)) ===> True

#testOptimize [ "CtorEqLiteral_4" ] ((5, 10) = (5, 20)) ===> False

end Test.CtorEq
