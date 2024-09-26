import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

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
#testOptimize [ "UnfoldNonRecFun_4" ] ∀ (a b c : Bool), predAnd a b c ===> ∀ (_a _b _c : Bool), False


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


/-! Test cases to validate non unfolding of recursive functions that can't be reduced via `reduceApp` rule. -/

def add_n_times (n : Nat) (a : Int) : Int :=
  match n with
  | Nat.zero => a
  | Nat.succ n' => a + add_n_times n' a

-- add_n_times x y ≥ z ===> z ≤ add_n_times x y
#testOptimize [ "RecFunNotUnfolded_1"  ] ∀ (x : Nat) (y z : Int), add_n_times x y ≥ z ===>
                                         ∀ (x : Nat) (y z : Int), z ≤ add_n_times x y


-- ∀ (x : List Nat) (n : Nat), List.length x > n → List.drop n x ≠ List.nil ===>
-- ∀ (x : List Nat) (n : Nat), List.length x < List.length (a : x)
#testOptimize [ "RecFunNotUnfolded_2"  ] ∀ (x : List Nat) (n : Nat), List.length x > n → List.drop n x ≠ List.nil ===>
                                         ∀ (x : List Nat) (n : Nat), n < List.length x → ¬ (List.nil = List.drop n x)


end Tests.UnfoldFun
