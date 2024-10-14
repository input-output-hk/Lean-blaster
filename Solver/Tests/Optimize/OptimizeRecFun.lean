import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.RecFun

/-! ## Test objectives to validate the normalization of recursive functions. -/


/-! Test cases to validate recursive function normalization. -/


def powerN (a : Int) (n : Nat) : Int :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => a * powerN a n'

-- ∀ (x : Int) (n : Nat), powerN x n = Int.pow x n ===> True
#testOptimize ["NormRecFun_1"] ∀ (x : Int) (n : Nat), powerN x n = Int.pow x n ===> True


def listNatBeq (xs : List Nat) (ys : List Nat) : Bool :=
 match xs, ys with
 | [], [] => true
 | x :: xs, y :: ys => listNatBeq xs ys && y == x
 | _, _ => false

-- ∀ (xs ys : List Nat), (List.beq xs ys) = listNatBeq xs ys ===> True
#testOptimize ["NormRecFun_2"] ∀ (xs ys : List Nat), (List.beq xs ys) = listNatBeq xs ys ===> True


-- ∀ (xs ys : List Nat), listNatBeq xs ys = (xs == ys) ===> True
#testOptimize ["NormRecFun_3"] ∀ (xs ys : List Nat), listNatBeq xs ys = (xs == ys) ===> True


def listPolyBeq [BEq α] (xs : List α) (ys : List α) : Bool :=
 match xs, ys with
 | [], [] => true
 | x :: xs, y :: ys => listPolyBeq xs ys && x == y
 | _, _ => false


-- ∀ (xs ys : List Nat), (xs == ys) = listNatBeq xs ys ===> True
#testOptimize ["NormRecFun_4"] ∀ (α : Type) (xs ys : List α), [BEq α] → (List.beq xs ys) = listPolyBeq xs ys ===> True

-- ∀ (xs ys : List Nat), listNatBeq xs ys = (xs == ys) ===> True
#testOptimize ["NormRecFun_5"] ∀ (α : Type) (xs ys : List α), [BEq α] → listPolyBeq xs ys = (xs == ys) ===> True



end Tests.RecFun
