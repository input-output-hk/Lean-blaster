import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.BEqNat
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance for `Nat. -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- (10 : Nat) == 10 ===> true
#testOptimize [ "BEqNatCst_1" ] (10 : Nat) == 10 ===> true

-- (10 : Nat) == 100 ===> false
#testOptimize [ "BEqNatCst_2" ] (10 : Nat) == 100 ===> false

-- (20 : Nat) + 40 == 60 ===> true
#testOptimize [ "BEqNatCst_3" ] (20 : Nat) + 40 == 60 ===> true

-- (20 : Nat) + 40 == 60 * 2 ===> false
#testOptimize [ "BEqNatCst_4" ] (20 : Nat) + 40 == 60 * 2 ===> false

-- (List.nil : List Nat) == List.nil ===> True
#testOptimize [ "BEqNatCst_5" ] (List.nil : List Nat) == List.nil ===> true

-- List.nil == [1 : Nat, 2, 3, 4] ===> false
#testOptimize [ "BEqNatCst_6" ] List.nil == [(1 : Nat), 2, 3, 4] ===> false

variable (x : Nat)
variable (y : Nat)
variable (z : Nat)

-- List.nil == [a, b, c] ===> false
#testOptimize [ "BEqNatCst_7" ] List.nil == [x, y, z] ===> false

-- ∀ (x y z : Nat), (List.nil == [x, y, z]) ===> False
#testOptimize [ "BEqNatCst_8" ] ∀ (x y z : Nat), (List.nil == [x, y, z]) ===> False

-- Nat.beq (10 : Nat) 10 ===> true
#testOptimize [ "BEqNatCst_9" ] Nat.beq (10 : Nat) 10 ===> true

-- Nat.beq (10 : Nat) 100 ===> false
#testOptimize [ "BEqNatCst_10" ] Nat.beq (10 : Nat) 100 ===> false

-- Nat.beq ((20 : Nat) + 40) 60 ===> true
#testOptimize [ "BEqNatCst_11" ] Nat.beq ((20 : Nat) + 40) 60 ===> true

-- Nat.beq ((20 : Nat) + 40) (60 * 2) ===> false
#testOptimize [ "BEqNatCst_12" ] Nat.beq ((20 : Nat) + 40) (60 * 2) ===> false

-- [y, x, z] == [x, y] ===> false
-- NOTE: Reduce to false via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqNatCst_13" ] [y, x, z] == [x, y] ===> false

-- [y, x, z] == [y, x, z] ===> true
-- NOTE: Reduce to false via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqNatCst_14" ] [y, x, z] == [y, x, z] ===> true

/-! Test cases for simplification rule `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`. -/

-- x == x ===> True
#testOptimize [ "BEqNatReflexive_1" ] ∀ (x : Nat), (x == x) ===> True

-- x == (x + 0) ===> True
#testOptimize [ "BEqNatReflexive_2" ] ∀ (x : Nat), x == x + 0 ===> True

-- (10 + (x + 30)) == ((x + 15) + 25) ===> True
#testOptimize [ "BEqNatReflexive_3" ] ∀ (x : Nat), (10 + (x + 30)) == ((x + 15) + 25) ===> True

-- (100 + ((50 - x) - 70)) + y == (y + 100) ===> True
#testOptimize [ "BEqNatReflexive_4" ] ∀ (x y : Nat), (100 + ((50 - x) - 70)) + y == (y + 100) ===> True

-- x + y == (y + x) ===> True
#testOptimize [ "BEqNatReflexive_5" ] ∀ (x y : Nat), (x + y) == (y + x) ===> True

-- (x + y) + z == z + (y + x) ===> True
#testOptimize [ "BEqNatReflexive_6" ] ∀ (x y z : Nat), (x + y) + z == z + (y + x) ===> True

-- Nat.beq x x ===> True
#testOptimize [ "BEqNatReflexive_7" ] ∀ (x : Nat), (Nat.beq x x) ===> True

-- Nat.beq x (x + 0) ===> True
#testOptimize [ "BEqNatReflexive_8" ] ∀ (x : Nat), Nat.beq x (x + 0) ===> True

-- Nat.beq (10 + (x + 30)) ((x + 15) + 25) ===> True
#testOptimize [ "BEqNatReflexive_9" ] ∀ (x : Nat), Nat.beq (10 + (x + 30)) ((x + 15) + 25) ===> True

-- Nat.beq ((100 + ((50 - x) - 70)) + y) (y + 100) ===> True
#testOptimize [ "BEqNatReflexive_10" ] ∀ (x y : Nat), Nat.beq ((100 + ((50 - x) - 70)) + y) (y + 100) ===> True

-- Nat.beq (x + y) (y + x) ===> True
#testOptimize [ "BEqNatReflexive_11" ] ∀ (x y : Nat), Nat.beq (x + y) (y + x) ===> True

-- Nat.beq ((x + y) + z) (z + (y + x)) ===> True
#testOptimize [ "BEqNatReflexive_12" ] ∀ (x y z : Nat), Nat.beq ((x + y) + z) (z + (y + x)) ===> True


/-! Test cases to ensure that simplification rules `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)` is not applied wrongly. -/

-- x == y ===> x = y
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatUnchanged_1" ] ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), x = y

-- x == (y + z) ===> x = (Nat.add y z)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatUnchanged_2" ] ∀ (x y z : Nat), x == (y + z) ===> ∀ (x y z : Nat), x = (Nat.add y z)

-- (y + z) == x ===> x = (Nat.add y z)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatUnchanged_3" ] ∀ (x y z : Nat), (y + z) == x ===> ∀ (x y z : Nat), x = (Nat.add y z)

-- [y, x, z] == [x, y, z] ===> x == y
-- NOTE: Reduction via `reduceApp` rule applied on recursive function
#testOptimize [ "BEqNatUnchanged_4" ] [y, x, z] == [x, y, z] ===> x == y


-- ∀ (x y z : Nat), [y, x, z] == [x, y, z] ===> ∀ (x y : Nat), x = y
-- NOTE: Reduction via `reduceApp` rule applied on recursive function
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatUnchanged_5" ] ∀ (x y z : Nat), [y, x, z] == [x, y, z] ===>
                                      ∀ (x y : Nat), x = y


-- ∀ (x y z v : Nat), [y, x, z] == [x, y, v] ===>
-- ∀ (x y z v : Nat), (¬ (x = y) ∨ ((¬ (x = y) ∨ (z = v)) ∧ (x = y))) ∧ (x = y)
-- NOTE: Reduction via `reduceApp` rule applied on recursive function
-- NOTE: can be reduced to (x == y) && (z == v) with additional logical simplification rules.
#testOptimize [ "BEqNatUnchanged_6" ] ∀ (x y z v : Nat), [y, x, z] == [x, y, v] ===>
                                      ∀ (x y z v : Nat), true = (((x == y) && (z == v)) && (x == y))


-- ∀ (x : Nat), (x == 234) ===> ∀ (x : Nat), (x == 234)
-- NOTE: We here provide the internal representation to ensure that 234
-- is properly reduced to `Expr.lit (Literal.natVal 234)`.
def beqNatUnchanged_7 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
      (Lean.Expr.lit (Lean.Literal.natVal 234)))
    (Lean.Expr.bvar 0))
  (Lean.BinderInfo.default)

elab "beqNatUnchanged_7" : term => return beqNatUnchanged_7

#testOptimize [ "BEqNatUnchanged_7" ] ∀ (x : Nat), (x == 234) ===> beqNatUnchanged_7

-- ∀ (x : Nat), (Nat.beq x 234) ===> ∀ (x : Nat), (x == 234)
#testOptimize [ "BEqNatUnchanged_8" ] ∀ (x : Nat), Nat.beq x 234 ===> beqNatUnchanged_7


/-! Test cases for simplification rule `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`. -/

-- x == y = x == y ===> True
#testOptimize [ "BEqNatCommut_1" ] ∀ (x y : Nat), (x == y) = (x == y) ===> True


-- x == y = y == x ===> True
#testOptimize [ "BEqNatCommut_2" ] ∀ (x y : Nat), (x == y) = (y == x) ===> True

-- y == x ===> x = y (when `x` declared first)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatCommut_3" ] ∀ (x y : Nat), (y == x) ===> ∀ (x y : Nat), x = y

-- ((x + y) == z) = (z == (x + y)) ===> True
#testOptimize [ "BEqNatCommut_4" ] ∀ (x y z : Nat), ((x + y) == z) = (z == (x + y)) ===> True

-- ((x * y) == (y + z)) = ((y + z) == (x * y)) ===> True
#testOptimize [ "BEqNatCommut_5" ] ∀ (x y z : Nat), ((x * y) == (y + z)) = ((y + z) == (x * y)) ===> True

-- ((x + y) == z) = (z == (y + x)) ===> True
#testOptimize [ "BEqNatCommut_6" ] ∀ (x y z : Nat), ((x + y) == z) = (z == (y + x)) ===> True

-- ((x * y) == (y + z)) = ((z + y) == (x * y)) ===> True
#testOptimize [ "BEqNatCommut_7" ] ∀ (x y z : Nat), ((x * y) == (y + z)) = ((z + y) == (x * y)) ===> True

-- Nat.beq x y = x == y ===> True
#testOptimize [ "BEqNatCommut_8" ] ∀ (x y : Nat), (Nat.beq x y) = (x == y) ===> True

-- x == y = Nat.beq y x ===> True
#testOptimize [ "BEqNatCommut_9" ] ∀ (x y : Nat), (x == y) = (Nat.beq y x) ===> True

-- Nat.beq y x ===> x = y (when `x` declared first)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNatCommut_10" ] ∀ (x y : Nat), (Nat.beq y x) ===> ∀ (x y : Nat), x = y

-- (Nat.beq (x + y) z) = (z == (x + y)) ===> True
#testOptimize [ "BEqNatCommut_11" ] ∀ (x y z : Nat), (Nat.beq (x + y) z) = (z == (x + y)) ===> True

-- (Nat.beq (x * y) (y + z)) = ((y + z) == (x * y)) ===> True
#testOptimize [ "BEqNatCommut_12" ] ∀ (x y z : Nat), (Nat.beq (x * y) (y + z)) = ((y + z) == (x * y)) ===> True

-- (Nat.beq (x + y) z) = (z == (y + x)) ===> True
#testOptimize [ "BEqNatCommut_13" ] ∀ (x y z : Nat), (Nat.beq (x + y) z) = (z == (y + x)) ===> True

-- ((x * y) == (y + z)) = (Nat.beq (z + y) (x * y)) ===> True
#testOptimize [ "BEqNatCommut_14" ] ∀ (x y z : Nat), ((x * y) == (y + z)) = (Nat.beq (z + y) (x * y)) ===> True


/-! Test cases to ensure that constant propagation is properly performed
    when `BEq.beq` operands are reduced to constant values via optimization. -/

-- 0 == (0 - x) ===> true
#testOptimize [ "BEqNatReduce_1"] (0 == (0 - x)) ===> true

-- 100 + ((40 - x) - 50) == 100 ===> true
#testOptimize [ "BEqNatReduce_2"] (100 + ((40 - x) - 50)) == 100 ===> true

-- (((x + 100) - 45) + 125) - x == 10 + ((100 - y) - 125) ===> true
#testOptimize [ "BEqNatReduce_3"] (((x + 100) - 45) - 55) - x == 10 + ((100 - y) - 125) ===> false

end Test.BEqNat
