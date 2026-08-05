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

/-! Test cases for simplification rule `N1 + (N2 + n) ==> (N1 "+" N2) + n` -/

#testOptimize ["IntAddAssoc_1", proof] ∀ (n : Int), 1 + (2 + n) = 3 + n ===> True

-- nested operand carries a core `Int.add`, exercising `toElabForm`'s Int branch
#testOptimize ["IntAddAssoc_2", proof] ∀ (a b : Int), 1 + (2 + (a + b)) = 3 + (a + b) ===> True

/-! Test cases for simplification rule `N1 + -(N2 + n) ==> (N1 "-" N2) + -n` -/

#testOptimize ["IntAddNegAdd_1", proof] ∀ (n : Int), 5 + -(2 + n) = 3 + -n ===> True

/-! Test cases for the commutative reorder `n1 + n2 ==> n2 + n1` -/

#testOptimize ["IntAddComm_1", proof] ∀ (n : Int), n + 3 = 3 + n ===> True

-- reorder `n + 0 ==> 0 + n`, closed with `Int.add_zero`
#testOptimize ["IntAddComm_2", proof] ∀ (n : Int), n + 0 = n ===> True
