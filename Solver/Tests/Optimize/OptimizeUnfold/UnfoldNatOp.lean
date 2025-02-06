import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldNatOp

/-! ## Test objectives to validate unfolding `Nat` operators -/


/-! Test cases to validate unfolding of `Nat` operators only when reduced to a constant value or via rewriting. -/

-- ∀ (x y : Nat), x + 0 > y ===> ∀ (x y : Nat), y < x
#testOptimize ["UnfoldNatOp_1"] ∀ (x y : Nat), x + 0 > y ===> ∀ (x y : Nat), y < x

-- ∀ (x y : Nat), (x + 10) - 10 < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_2"] ∀ (x y : Nat), (x + 10) - 10 < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (x - x) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_3"] ∀ (x y : Nat), (x - x) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (0 - x) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_4"] ∀ (x y : Nat), (0 - x) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), x - 0 < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_5"] ∀ (x y : Nat), x - 0 < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (10 - (x + 20)) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_6"] ∀ (x y : Nat), (10 - (x + 20)) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), ((10 - x) - 20) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_7"] ∀ (x y : Nat), ((10 - x) - 20) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), Nat.pred (x + 1) < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_8"] ∀ (x y : Nat), Nat.pred (x + 1) < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), Nat.pred (Nat.succ x) < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_9"] ∀ (x y : Nat), Nat.pred (Nat.succ x) < y ===> ∀ (x y : Nat), x < y

-- ∀ (x : Nat), Nat.beq x x ===> True
#testOptimize ["UnfoldNatOp_10"] ∀ (x : Nat), Nat.beq x x ===> True

-- ∀ (x : Nat), (0 * x) + x < y ===> ∀ (x : Nat), x < y
#testOptimize ["UnfoldNatOp_11"] ∀ (x y : Nat), (0 * x) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), ((1 * x) - x) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_12"] ∀ (x y : Nat), ((1 * x) - x) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (x / 1) < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_13"] ∀ (x y : Nat), x / 1 < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (x / 0) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_14"] ∀ (x y : Nat), (x / 0) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (x % 1) + x < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_15"] ∀ (x y : Nat), (x % 1) + x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), (x % 0) < y ===> ∀ (x y : Nat), x < y
#testOptimize ["UnfoldNatOp_16"] ∀ (x y : Nat), (x % 0) < y ===> ∀ (x y : Nat), x < y

-- TODO: add test cases for Nat.ble and Nat.blt when simplification rules are added


/-! Test cases to validate when `Nat` operators must not be unfolded -/

-- ∀ (x y z : Nat), x + y > z ===> ∀ (x y z : Nat), z < Nat.add x y
#testOptimize ["NatOpNotUnfolded_1"] ∀ (x y z : Nat), x + y > z ===> ∀ (x y z : Nat), z < Nat.add x y

-- ∀ (x y z : Nat), x - y < z ===> ∀ (x y : Nat), Nat.sub x y < z
#testOptimize ["NatOpNotUnfolded_2"] ∀ (x y z : Nat), x - y < z ===> ∀ (x y z : Nat), Nat.sub x y < z

-- ∀ (x y z : Nat), (x - z) + y < z ===> ∀ (x y z : Nat), Nat.add y (Nat.sub x z) < z
#testOptimize ["NatOpNotUnfolded_3"] ∀ (x y z : Nat), (x - z) + y < z ===> ∀ (x y z : Nat), Nat.add y (Nat.sub x z) < z

-- ∀ (x y z : Nat), Nat.pred ((x + y) + 1) < z ===> ∀ (x y z : Nat), Nat.add x y < z
#testOptimize ["NatOpNotUnfolded_4"]  ∀ (x y z : Nat), Nat.pred ((x + y) + 1) < z ===> ∀ (x y z : Nat), Nat.add x y < z

-- ∀ (x y : Nat), Nat.beq x y ===> ∀ (x y : Nat), true = (x == y)
#testOptimize ["NatOpNotUnfolded_5"] ∀ (x y : Nat), Nat.beq x y ===> ∀ (x y : Nat), x = y

-- ∀ (x y z : Nat), x * y > z ===> ∀ (x y z : Nat), z < Nat.mul x y
#testOptimize ["NatOpNotUnfolded_6"] ∀ (x y z : Nat), x * y > z ===> ∀ (x y z : Nat), z < Nat.mul x y

-- ∀ (x y z : Nat), x / y < z ===> ∀ (x y z : Nat), Nat.div x y < z
#testOptimize ["NatOpNotUnfolded_7"] ∀ (x y z : Nat), x / y < z ===> ∀ (x y z : Nat), Nat.div x y < z

-- ∀ (x y z : Nat), x % y < z ===> ∀ (x y z : Nat), Nat.mod x y < z
#testOptimize ["NatOpNotUnfolded_8"] ∀ (x y z : Nat), x % y < z ===> ∀ (x y z : Nat), Nat.mod x y < z

-- ∀ (x y : Nat), Nat.ble x y ===> ∀ (x y : Nat), true = (Nat.ble x y)
-- TODO: update test case when normalizing `Nat.ble x y = true` to `x ≤ y`
#testOptimize ["NatOpNotUnfolded_9"] ∀ (x y : Nat), Nat.ble x y ===> ∀ (x y : Nat), true = (Nat.ble x y)

-- ∀ (x y : Nat), Nat.blt x y ===> ∀ (x y : Nat), true = (Nat.blt x y)
-- TODO: update test case when normalizing `Nat.blt x y = true` to `x < y`
#testOptimize ["NatOpNotUnfolded_10"] ∀ (x y : Nat), Nat.blt x y ===> ∀ (x y : Nat), true = (Nat.blt x y)

end Tests.UnfoldNatOp
