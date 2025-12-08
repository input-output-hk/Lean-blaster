import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldFun

/-! ## Test objectives to validate function unfolding -/


/-! Test cases to validate unfolding of non-recursive functions. -/

def f (a: Nat) (b : Nat) : Nat := a + b
-- f x y ===> Nat.add x y
#testOptimize [ "UnfoldNonRecFun_1" ] ∀ (x y z : Nat), f x y > z ===> ∀ (x y z : Nat), z < Nat.add x y


def g (a : Nat) (b : Nat) : Nat := b + a
-- f x y = g y x ===> True
#testOptimize [ "UnfoldNonRecFun_2" ] ∀ (x y : Nat), f x y = g x y ===> True


def h (a : Nat) (b : Nat) (c : Nat) := c * g a b
-- h x y z ===> Nat.mul z * Nat.add x y
#testOptimize [ "UnfoldNonRecFun_3" ] ∀ (x y z n : Nat), h x y z < n ===>
                                      ∀ (x y z n : Nat), Nat.mul z (Nat.add x y) < n

def predNotAnd (a : Bool) (b : Bool) : Bool := ! (a && b)
def predAnd (a : Bool) (b : Bool) (c : Bool) := a && b && predNotAnd b a && c
-- predAnd a b c ===> False
#testOptimize [ "UnfoldNonRecFun_4" ] ∀ (a b c : Bool), predAnd a b c ===> False


def arith (a: Int) (b : Int) : Int := if a > 0 then a + b else a - b
-- arith x y = if x > 0 then x + y else x - y ===> True
#testOptimize [ "UnfoldNonRecFun_5" ] ∀ (x y : Int), (arith x y > x) → (if x > 0 then x + y else x - y) > x ===> True


/-! Test cases to validate unfolding of recursive functions only when reduced to a constant value. -/

-- List.length List.nil ===> 0
#testOptimize [ "UnfoldRecFun_1" ] ∀ (α : Type), (List.length (List.nil : List α)) = 0 ===> True

-- ∀ (a b c : Nat), List.drop 1 [a, b, c] = [b, c] ===> True
#testOptimize [ "UnfoldRecFun_2" ] ∀ (a b c : Nat), List.drop 1 [a, b, c] = [b, c] ===> True

-- ∀ (a b c : Nat), List.drop 3 [a, b, c] = List.nil ===> True
#testOptimize [ "UnfoldRecFun_3" ] ∀ (a b c : Nat), List.drop 3 [a, b, c] = List.nil ===> True

-- ∀ (a b c : Nat), List.drop 10 [a, b, c] = List.nil ===> True
#testOptimize [ "UnfoldRecFun_4" ] ∀ (a b c : Nat), List.drop 10 [a, b, c] = List.nil ===> True

-- ∀ (x : List Nat) (n : Nat), List.length (n :: x) = List.length x + 1 ===> True
#testOptimize [ "UnfoldRecFun_5" ] ∀ (x : List Nat) (n : Nat), List.length (n :: x) = (List.length x + 1) ===> True


-- ∀ (a b c : Int), List.map Int.neg [a, b, c] = [Int.neg a, Int.neg b, Int.neg c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: opaque function
#testOptimize [ "UnfoldRecFun_6" ]
  ∀ (a b c : Int), List.map Int.neg [a, b, c] = [Int.neg a, Int.neg b, Int.neg c] ===> True

-- ∀ (a b c d : Int), List.map (Int.add d) [a, b, c] = [Int.add a d, Int.add b d, Int.add c d] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: partially applied function
#testOptimize [ "UnfoldRecFun_7" ]
  ∀ (a b c d : Int), List.map (Int.add d) [a, b, c] = [Int.add a d, Int.add b d, Int.add c d] ===> True

-- ∀ (a b c : Int),
--   List.map (λ x => if x > 0 then x else -x) [a, b, c] =
--   [if a > 0 then a else -a, if b > 0 then b else -b, if c > 0 then c else -c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: lambda term
#testOptimize [ "UnfoldRecFun_8" ]
  ∀ (a b c : Int),
    List.map (λ x => if x > 0 then x else -x) [a, b, c] =
    [if a > 0 then a else -a, if b > 0 then b else -b, if c > 0 then c else -c] ===> True


structure FunRel α where
  f [LT α] : α → α
  inv : ∀ (x y : α), [LT α] → x < y → f x < f y

--  ∀ (a b c : Int) (rel : FunRel Int), List.map rel.f [a, b, c] = [rel.f a, rel.f b, rel.f c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: function in ctor
#testOptimize [ "UnfoldRecFun_9" ]
  ∀ (a b c : Int) (rel : FunRel Int), List.map rel.f [a, b, c] = [rel.f a, rel.f b, rel.f c] ===> True

class FunRelTwo (α : Type) [LT α] where
  f : α → α
  inv : ∀ (x y : α), x < y → f x < f y

-- ∀ (a b c : Int), [FunRelTwo Int] →
--   List.map FunRelTwo.f [a, b, c] = [FunRelTwo.f a, FunRelTwo.f b, FunRelTwo.f c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: undefined class function
#testOptimize [ "UnfoldRecFun_10" ]
  ∀ (a b c : Int), [FunRelTwo Int] →
    List.map FunRelTwo.f [a, b, c] = [FunRelTwo.f a, FunRelTwo.f b, FunRelTwo.f c] ===> True

-- ∀ (a b c : Nat), List.map Int.ofNat [a, b, c] = [Int.ofNat a, Int.ofNat b, Int.ofNat c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: a ctor expecting one or more arguments
#testOptimize [ "UnfoldRecFun_11" ]
  ∀ (a b c : Nat), List.map Int.ofNat [a, b, c] = [Int.ofNat a, Int.ofNat b, Int.ofNat c] ===> True

def findPositive (xs : List Int) (d : β) (r : β) : β :=
 match xs with
 | [] => d
 | x :: tl => if x > 0 then r else findPositive tl d r

-- ∀ (a b c : Int),
--   findPositive [a, b, c] Int.add Int.mul =
--   Blaster.dite' (0 < a)
--     (fun _ => Int.mul)
--     (fun _ =>
--       Blaster.dite' (0 < b)
--        (fun _ => Int.mul)
--        (fun _ => Blaster.dite' (0 < c) (fun _ => Int.mul) (fun _ => Int.add))) ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: when function type argument is only known at instantiation.
#testOptimize [ "UnfoldRecFun_12" ] (norm-result: 1)
  ∀ (a b c : Int),
    findPositive [a, b, c] Int.add Int.mul =
    Blaster.dite' (0 < a)
      (fun _ => Int.mul)
      (fun _ =>
        Blaster.dite' (0 < b)
         (fun _ => Int.mul)
         (fun _ => Blaster.dite' (0 < c) (fun _ => Int.mul) (fun _ => Int.add))) ===> True

-- ∀ (a b c : Nat) (f : Nat → Nat), List.map f [a, b, c] = [f a, f b, f c] ===> True
-- Test case to validate that unfolding properly considers fun params
-- Test case: quantified function
#testOptimize [ "UnfoldRecFun_13" ]
  ∀ (a b c : Nat) (f : Nat → Nat), List.map f [a, b, c] = [f a, f b, f c] ===> True


/-! Test cases to validate non unfolding of recursive functions that can't be reduced via `reduceApp` rule. -/

def add_n_times (n : Nat) (a : Int) : Int :=
  match n with
  | Nat.zero => a
  | Nat.succ n' => a + add_n_times n' a

-- add_n_times x y ≥ z ===> ¬ add_n_times x y < z
#testOptimize [ "RecFunNotUnfolded_1"  ] ∀ (x : Nat) (y z : Int), add_n_times x y ≥ z ===>
                                         ∀ (x : Nat) (y z : Int), ¬ add_n_times x y < z

-- ∀ (x : List Nat) (n : Nat), List.length x > n → List.drop n x ≠ List.nil ===>
-- ∀ (x : List Nat) (n : Nat), List.length x < List.length (a : x)
#testOptimize [ "RecFunNotUnfolded_2"  ]
  ∀ (x : List Nat) (n : Nat), List.length x > n → List.drop n x ≠ List.nil ===>
  ∀ (x : List Nat) (n : Nat), n < List.length x → ¬ (List.nil = List.drop n x)

end Tests.UnfoldFun
