import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntMul

/-! ## Test objectives to validate normalization and simplification rules on ``Int.mul -/

/-! Test cases for `reduceApp` rule on ``Int.mul -/

-- 0 * 5 ===> 0
def intMulCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 0))

elab "intMulCst_1" : term => return intMulCst_1

#testOptimize [ "IntMulCst_1", proof] (0 : Int) * 5 ===> intMulCst_1


-- 1 * 5 ===> 5
def intMulCst_2 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 5))
elab "intMulCst_2" : term => return intMulCst_2

#testOptimize [ "IntMulCst_2", proof] (1: Int) * 5 ===> intMulCst_2

/-! Tests cases for simplification rule 0 * n = 0 -/
#testOptimize ["IntMulZero_1", proof] ∀ (n : Int), 0 * n = 0 ===> True

variable (x : Int)
#testOptimize ["IntMulZero_2", proof] (0 : Int) * x ===> intMulCst_1


/-! Tests cases for simplification rule 1 * n = n-/
#testOptimize ["IntMulOne_1", proof] ∀ (x : Int), 1 * x = x ===> True

#testOptimize ["IntMulOne_2", proof] ∀ (x y : Int), 1 * x = y ===> ∀ (x y : Int), x = y
