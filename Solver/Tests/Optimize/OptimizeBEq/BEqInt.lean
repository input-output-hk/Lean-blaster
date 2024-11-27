import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.BEqInt
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance for ``Int. -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- (430 : Int) == 430  ===> true
#testOptimize [ "BEqIntCst_1" ] (430 : Int) == 430 ===> true

-- (40 : Int) == 2300 ===> false
#testOptimize [ "BEqIntCst_2" ] (40 : Int) == 2300 ===> false

-- (-53 : Int) == -53 ===> true
#testOptimize [ "BEqIntCst_3" ] (-53 : Int) == -53 ===> true

-- (-430 : Int) == 430 ===> false
#testOptimize [ "BEqIntCst_4" ] (-430 : Int) == 430 ===> false

-- (-430 : Int) + 100 == -330 ===> true
#testOptimize [ "BEqIntCst_5" ] (-430 : Int) + 100 == -330 ===> true

-- (-430 : Int) + 200 == 115 * -2 ===> true
#testOptimize [ "BEqIntCst_6" ] (-430 : Int) + 200 == 115 * -2 ===> true

-- (List.nil : List Int) == List.nil ===> True
#testOptimize [ "BEqIntCst_7" ] (List.nil : List Int) == List.nil ===> true

-- List.nil == [(1 : Int), 2, 3, 4] ===> false
#testOptimize [ "BEqIntCst_8" ] List.nil == [(1 : Int), 2, 3, 4] ===> false

variable (x : Int)
variable (y : Int)
variable (z : Int)

-- List.nil == [a, b, c] ===> false
#testOptimize [ "BEqIntCst_9" ] List.nil == [x, y, z] ===> false

-- ∀ (x y z : Int), (List.nil == [x, y, z]) ===> False
#testOptimize [ "BEqIntCst_10" ] ∀ (x y z : Int), (List.nil == [x, y, z]) ===> False

-- [y, x, z] == [x, y] ===> List.beq [y, x, z] [x, y]
-- NOTE: Reduce to false via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqIntCst_11" ] [y, x, z] == [x, y] ===> false


-- [y, x, z] == [y, x, z] ===> true
-- NOTE: Reduce to true via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqIntCst_12" ] [y, x, z] == [y, x, z] ===> true


-- ∀ (x y z : Int), [x, y, z] == [x, y, z] ===> True
-- NOTE: Reduce to True via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqIntCst_13" ] ∀ (x y z : Int), [x, y, z] == [x, y, z] ===> True


/-! Test cases for simplification rule `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`. -/

-- x == x ===> True
#testOptimize [ "BEqIntReflexive_1" ] ∀ (x : Int), (x == x) ===> True

-- x == (x + 0) ===> True
#testOptimize [ "BEqIntReflexive_2" ] ∀ (x : Int), x == x + 0 ===> True

-- (10 + (x + 30)) == ((x + 15) + 25) ===> True
#testOptimize [ "BEqIntReflexive_3" ] ∀ (x : Int), (10 + (x + 30)) == ((x + 15) + 25) ===> True

-- (100 + ((50 - x) - 70)) + y == (y + (80 - x)) ===> True
#testOptimize [ "BEqIntReflexive_4" ] ∀ (x y : Int), (100 + ((50 - x) - 70)) + y == (y + (80 - x)) ===> True

-- x + y == (y + x) ===> True
#testOptimize [ "BEqIntReflexive_5" ] ∀ (x y : Int), (x + y) == (y + x) ===> True

-- (x + y) + z == z + (y + x) ===> True
#testOptimize [ "BEqIntReflexive_6" ] ∀ (x y z : Int), (x + y) + z == z + (y + x) ===> True

-- (x - x) = (x + -x) ===> True
#testOptimize [ "BEqIntReflexive_7" ] ∀ (x : Int), (x - x) = (x + -x) ===> True

-- (x * 1) - (x + 0) + y = y ===> True
#testOptimize [ "BEqIntReflexive_8" ] ∀ (x y : Int), (x * 1) - (x + 0) + y = y ===> True

-- TODO: uncomment test cases when introducing simplification rules on Int.div and Int.mod
-- TODO: Add additional test cases to cover all div and mod functions.

-- -- (x / (1 + (y * 0)) + (y % 0) = x + y ===> True
-- #testOptimize [ "BEqIntReflexive_9" ] ∀ (x y : Int), (x / (1 + (y * 0))) + (y % 0) = x + y ===> True


/-! Test cases to ensure that simplification rules `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)` is not applied wrongly. -/

-- x == y ===> x = y
-- NOTE: `true = (a == b)` is reduce to `a = b` when `isCompatibleBeqType Type(a)`
#testOptimize [ "BEqIntUnchanged_1" ] ∀ (x y : Int), x == y ===> ∀ (x y : Int), x = y

-- x == (y + z) ===> x = (y + z)
-- NOTE: `true = (a == b)` is reduce to `a = b` when `isCompatibleBeqType Type(a)`
#testOptimize [ "BEqIntUnchanged_2" ] ∀ (x y z : Int), x == (y + z) ===> ∀ (x y z : Int), x = (Int.add y z)

-- (y + z) == x ===> x = (y + z)
-- NOTE: `true = (a == b)` is reduce to `a = b` when `isCompatibleBeqType Type(a)`
#testOptimize [ "BEqIntUnchanged_3" ] ∀ (x y z : Int), (y + z) == x ===> ∀ (x y z : Int), x = (Int.add y z)

-- [y, x, z] == [x, y, z] ===> decide (x = y)
-- NOTE: Reduction via `reduceApp` rule, commutative of beq on Int and absorption rule on &&
#testOptimize [ "BEqIntUnchanged_4" ] [y, x, z] == [x, y, z] ===> decide (x = y)

-- ∀ (x y z : Int), [y, x, z] == [x, y, z] ===> ∀ (x y : Int), x = y
-- NOTE: Reduction via `reduceApp` rule, commutative of beq on Int and absorption rule on &&
-- NOTE: `true = (a == b)` is reduce to `a = b` when `isCompatibleBeqType Type(a)`
#testOptimize [ "BEqIntUnchanged_5" ] ∀ (x y z : Int), [y, x, z] == [x, y, z] ===>
                                      ∀ (x y : Int), x = y

-- ∀ (x y z v : Int), [y, x, z] == [x, y, v] ===>
-- ∀ (x y z v : Int), (¬ (x = y) ∨ ((¬ (x = y) ∨ (z = v)) ∧ (x = y))) ∧ (x = y)
-- NOTE: Reduction via `reduceApp` rule, commutative of beq on Int and absorption rule on &&
-- NOTE: can be reduced to (x == y) && (z == v) with additional boolean simplification rules.
#testOptimize [ "BEqIntUnchanged_6" ] ∀ (x y z v : Int), [y, x, z] == [x, y, v] ===>
                                      ∀ (x y z v : Int), (¬ (x = y) ∨ ((¬ (x = y) ∨ (z = v)) ∧ (x = y))) ∧ (x = y)

-- ∀ (x : Int), (x == 1234) ===> ∀ (x : Int), (x == 1234)
-- NOTE: We here provide the internal representation to ensure that 1234 is properly reduced to `Int.ofNat (Expr.lit (Literal.natVal 1234))`.
def beqIntUnchanged_7 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Int [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
      (Lean.Expr.app (Lean.Expr.const `Int.ofNat []) (Lean.Expr.lit (Lean.Literal.natVal 1234))))
    (Lean.Expr.bvar 0))
  (Lean.BinderInfo.default)

elab "beqIntUnchanged_7" : term => return beqIntUnchanged_7

#testOptimize [ "BEqIntUnchanged_7" ] ∀ (x : Int), (x == 1234) ===> beqIntUnchanged_7

-- ∀ (x : Int), (x = -453) ===> ∀ (x : Int), (x = -453)
-- NOTE: We here provide the internal representation to ensure that -453 is properly reduced to `Int.negSucc (Expr.lit (Literal.natVal 452))`.
def beqIntUnchanged_8 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Int [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
      (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 452))))
    (Lean.Expr.bvar 0))
  (Lean.BinderInfo.default)

elab "beqIntUnchanged_8" : term => return beqIntUnchanged_8

#testOptimize [ "BEqIntUnchanged_8" ] ∀ (x : Int), x == -453 ===> beqIntUnchanged_8


/-! Test cases for simplification rule `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`. -/

-- x == y = x == y ===> True
#testOptimize [ "BEqIntCommut_1" ] ∀ (x y : Int), (x == y) = (x == y) ===> True

-- x == y = y == x ===> True
#testOptimize [ "BEqIntCommut_2" ] ∀ (x y : Int), (x == y) = (y == x) ===> True

-- y == x ===> x == y (when `x` declared first)
-- NOTE: `true = (a == b)` is reduce to `a = b` when `isCompatibleBeqType Type(a)`
#testOptimize [ "BEqIntCommut_3" ] ∀ (x y : Int), (y == x) ===> ∀ (x y : Int), x = y

-- ((x + y) == z) = (z == (x + y)) ===> True
#testOptimize [ "BEqIntCommut_4" ] ∀ (x y z : Int), ((x + y) == z) = (z == (x + y)) ===> True

-- ((x * y) == (y + z)) = ((y + z) == (x * y)) ===> True
#testOptimize [ "BEqIntCommut_5" ] ∀ (x y z : Int), ((x * y) == (y + z)) = ((y + z) == (x * y)) ===> True

-- ((x + y) == z) = (z == (y + x)) ===> True
#testOptimize [ "BEqIntCommut_6" ] ∀ (x y z : Int), ((x + y) == z) = (z == (y + x)) ===> True

-- ((x * y) == (y + z)) = ((z + y) == (x * y)) ===> True
#testOptimize [ "BEqIntCommut_7" ] ∀ (x y z : Int), ((x * y) == (y + z)) = ((z + y) == (x * y)) ===> True


/-! Test cases to ensure that `reduceApp` is properly called
    when `BEq.beq` operands are reduced to constant values via optimization. -/

-- 0 == (0 - x) + x ===> true
#testOptimize [ "BEqIntReduce_1"] (0 == (0 - x) + x) ===> true

-- 100 + ((40 - x) - 50) == 100 ===> true
#testOptimize [ "BEqIntReduce_2"] 100 + (((40 - x) - 40) + x) == 100 ===> true

-- (((x - 100) - 45) + 145) - x == (125 + (100 - (225 - y))) - y ===> true
#testOptimize [ "BEqIntReduce_3"] (((x - 100) - 45) + 145) - x == (125 + (100 - (225 - y))) - y ===> true

-- ((((x - 100) - 45) + 145) - x) * y == (125 + (100 - (225 - y))) - y ===> true
#testOptimize [ "BEqIntReduce_4"] ((((x - 100) - 45) + 145) - x) * y == (125 + (100 - (225 - y))) - y ===> true

-- TODO: uncomment test case when simplifications on Int.div and Int.mod functions are introduced
-- (y % ((((x - 100) - 45) + 145) - x)) - y == (125 + (100 - (225 - y))) - y ===> true
-- #testOptimize [ "BEqIntReduce_5"] (y % ((((x - 100) - 45) + 145) - x)) - y == (125 + (100 - (225 - y))) - y ===> true



end Test.BEqInt
