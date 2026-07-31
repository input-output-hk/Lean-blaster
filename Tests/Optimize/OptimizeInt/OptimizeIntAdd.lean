import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntAdd

/-! ## Test objectives to validate normalization and simplification rules on ``Int.add -/

/-! Test cases for `reduceApp` rule on ``Int.add -/

-- 0 + 1 ===> 1
def intAddCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 1))

elab "intAddCst_1" : term => return intAddCst_1

#testOptimize [ "IntAddCst_1", proof] (0 : Int) + 1 ===> intAddCst_1

/-! Test cases for simplification rule `0 + n ===> n` -/

#testOptimize ["IntAddZero_1", proof] ∀ (m n: Int), 0 + m = n ===> ∀ (m n: Int), m = n

#testOptimize ["IntAddZero_2", proof] ∀ (n : Int), 0 + n = n ===> True
