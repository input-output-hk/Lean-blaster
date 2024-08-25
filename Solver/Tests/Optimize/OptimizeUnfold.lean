import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeUnfold
/-! ## Test objectives to validate non-recursive function unfolding -/

def f (a: Int) (b : Int) : Int := a + b
-- f x y ===> Int.add x y
-- NOTE: unfolding + on Int is reduced to Int.add
#testOptimize [ "UnfoldNonRecFun_1" ] ∀ (x y : Int), f x y > x ===> ∀ (x y : Int), Int.add x y > x


def g (a: Int) (b : Int) : Int := if a > 0 then a + b else a - b
-- g x y = if x > 0 then x + y else x - y ===> True
#testOptimize [ "UnfoldNonRecFun_2" ] ∀ (x y : Int), (g x y > x) = ((if x > 0 then x + y else x - y) > x) ===> True

def add_n_times (n : Nat) (a : Int) : Int :=
  match n with
  | Nat.zero => a
  | Nat.succ n' => a + add_n_times n' a

-- add_n_times n ===> add_n_times n
#testOptimize [ "RecFunNotUnfolded" ] ∀ (x : Nat) (y : Int), add_n_times x y >= y ===>
                                      ∀ (x : Nat) (y : Int), add_n_times x y >= y

-- equality not unfolded
#testOptimize [ "EqNotUnfolded" ] ∀ (x y : Int), x = y ===> ∀ (x y : Int), x = y

-- boolean equality not unfolded for Int
-- NOTE: we explicitly introduce `= true` in the expected result to be deterministic
#testOptimize [ "BEqIntNotUnfolded" ] ∀ (x y : Int), x == y ===> ∀ (x y : Int), true = (x == y)

-- boolean equality not unfolded for Nat
-- NOTE: we explicitly introduce `= true` in the expected result to be deterministic
#testOptimize [ "BEqNatNotUnfolded" ] ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), true = (x == y)

-- boolean equality not unfolded for Bool
-- NOTE: reordering applied on commutative operators
-- NOTE: we explicitly introduce `= true` in the expected result to be deterministic
#testOptimize [ "BEqBoolNotUnfolded" ] ∀ (x y : Bool), x == y ===> ∀ (x y : Bool), true = (x == y)

-- boolean equality not unfolded for String
-- NOTE: reordering applied on commutative operators
-- NOTE: we explicitly introduce `= true` in the expected result to be deterministic
#testOptimize [ "BEqStringNotUnfolded" ] ∀ (x y : String), x == y ===> ∀ (x y : String), true = (x == y)

-- And not unfolded
-- NOTE: reordering applied on commutative operators
#testOptimize [ "AndNotUnfolded" ] ∀ (a b : Prop), a ∧ b ===> ∀ (a b : Prop), a ∧ b

-- Or not unfolded
-- NOTE: reordering applied on commutative operators
#testOptimize [ "OrNotUnfolded" ] ∀ (a b : Prop), a ∨ b ===> ∀ (a b : Prop), a ∨ b

-- Not not unfolded
#testOptimize [ "NotNotUnfolded" ] ∀ (a : Prop), ¬ a ===> ∀ (a : Prop), ¬ a

-- Ite not unfolded: case 1
#testOptimize [ "IteNotUnfolded_1" ] ∀ (x y : Int) (c : Bool), (if c then x else y) > x ===>
                                     ∀ (x y : Int) (c : Bool), (if true = c then x else y) > x

-- Ite not unfolded: case 2
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteNotUnfolded_2" ] ∀ (x y : Int), (if x = y then x else y) = y ===>
                                     ∀ (x y : Int), y = (if x = y then x else y)

-- Ite not unfolded: case 3
#testOptimize [ "IteNotUnfolded_3" ] ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x ===>
                                     ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x


-- Ite not unfolded: case 4
-- NOTE: considering explicit Decidable contraints on ite cond
#testOptimize [ "IteNotUnfolded_4" ] ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x ===>
                                     ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x

-- Ite not unfolded: case 5
-- NOTE: considering explicit DecidableEq constraints on parametric types
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteNotUnfolded_5" ] ∀ (α : Type) (x y : List α), [DecidableEq α] → (if x = y then x else y) = y ===>
                                     ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if x = y then x else y)


-- DIte not unfolded: case 1
-- NOTE: considering explicit Decidable contraints on ite cond
#testOptimize [ "DIteNotUnfolded_1" ] ∀ (x y : Int) (c : Prop), [Decidable c] → (if _h : c then x else y) > x ===>
                                      ∀ (x y : Int) (c : Prop), [Decidable c] → (if _h : c then x else y) > x

-- DIte not unfolded: case 2
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteNotUnfolded_2" ] ∀ (x y : Int), (if _h : x = y then x else y) = y ===>
                                      ∀ (x y : Int), y = (if _h : x = y then x else y)

-- DIte not unfolded: case 3
#testOptimize [ "DIteNotUnfolded_3" ] ∀ (a b : Bool) (x y : Int), (if _h : a = b then x else y) > x ===>
                                      ∀ (a b : Bool) (x y : Int), (if _h : a = b then x else y) > x

-- DIte not unfolded: case 4
-- NOTE: considering explicit DecidableEq constraints on parametric types
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteNotUnfolded_5" ] ∀ (α : Type) (x y : List α), [DecidableEq α] → (if _h : x = y then x else y) = y ===>
                                      ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if _h : x = y then x else y)

-- Exists not unfolded
#testOptimize [ "ExistsNotUnfolded" ] ∀ (x : Int), ∃ (y z : Int), y > x ∧ z > y ===>
                                      ∀ (x : Int), ∃ (y z : Int), y > x ∧ z > y


-- UNCOMMENT ONCE WE HAVE INT reduction rules
-- def select0 (x : Int) (y: Int) (z : Int) : Int :=
--  let args := #[x, y , z]
--  if h : 0 < args.size
--  then args[0]
--  else 0

-- #testOptimize ["DITEH"] ∀ (x y z : Int), (select0 x y z) = x ===> True

-- #testOptimize ["LambdaProp"] ∀ (x : Array Int) (i : Nat), i < x.size → x[i]? ≠ none ===> ∀ (x : Array Int) (i : Nat), i < x.size → x[i]? ≠ none



end Tests.OptimizeUnfold
