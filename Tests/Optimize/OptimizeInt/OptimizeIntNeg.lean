import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntNeg

/-! ## Test objectives to validate normalization and simplification rules on ``Int.neg -/

/-! Tests cases for `reduceApp` rule on ``Int.neg -/

-- - (-5) ===> 5
def intNegCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 5))

elab "intNegCst_1" : term => return intNegCst_1

#testOptimize [ "IntNegCst_1", proof] -( - (5 : Int)) ===> intNegCst_1

#testOptimize [ "IntNegCst_2", proof] -(- 5 : Int) ===> intNegCst_1

-- `-(-2)` folds to `2`, which then feeds the add fold and `Int.zero_add`
#testOptimize ["IntNegCst_3", proof] ∀ (n : Int), -(-2) + -2 + n = n ===> True

-- `-0` folds to `0`, then `Int.zero_add`
#testOptimize ["IntNegCst_4", proof] ∀ (n : Int), -0 + n = n ===> True

/-! Test cases for simplification rule -(-n) = n -/

#testOptimize ["IntNegNeg_1", proof] ∀ (n : Int), -(-n) = n ===> True

#testOptimize ["IntNegNeg_2", proof] ∀ (x y : Int), -(-x) = y ===> ∀ (x y : Int), x = y

#testOptimize ["IntNegNeg_3", proof] ∀ (x : Int), -(-(-x)) = -x ===> True

end Tests.OptimizeIntNeg
