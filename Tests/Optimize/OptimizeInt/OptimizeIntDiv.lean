import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntDiv

/-! ## Test objectives to validate normalization and simplification rules on ``Int.ediv, ``Int.tdiv and ``Int.fdiv -/

/-! Test cases for `reduceApp` rule on ``Int.ediv, ``Int.tdiv and ``Int.fdiv -/


def intDivCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 5))

elab "intDivCst_1" : term => return intDivCst_1

def intDivCst_2 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 0))

elab "intDivCst_2" : term => return intDivCst_2

-- 5 / 1 ===> 5
#testOptimize [ "IntDivCst_1", proof] (5 : Int) / 1 ===> intDivCst_1

#testOptimize [ "IntFdivCst_1", proof] Int.fdiv 5 1 ===> intDivCst_1

#testOptimize [ "IntTdivCst_1", proof] Int.tdiv 5 1 ===> intDivCst_1

-- 0 / 5 ===> 0
#testOptimize [ "IntDivCst_2", proof] (0 : Int) / 5 ===> intDivCst_2

#testOptimize [ "IntFdivCst_2", proof] Int.fdiv 0 5 ===> intDivCst_2

#testOptimize [ "IntTdivCst_2", proof] Int.tdiv 0 5 ===> intDivCst_2

-- 5 / 0 ===> 0
#testOptimize [ "IntDivCst_3", proof] (5 : Int) / 0 ===> intDivCst_2

#testOptimize [ "IntFdivCst_3", proof] Int.fdiv 5 0 ===> intDivCst_2

#testOptimize [ "IntTdivCst_3", proof] Int.tdiv 5 0 ===> intDivCst_2

/-! Test cases for simplification rule n / 1 ===> n -/

#testOptimize[ "IntDivOne_1", proof] ∀ (n : Int), n / 1 = n ===> True

#testOptimize[ "IntFdivOne_1", proof] ∀ (n : Int), Int.fdiv n 1 = n ===> True

#testOptimize[ "IntTdivOne_1", proof] ∀ (n : Int), Int.tdiv n 1 = n ===> True

#testOptimize[ "IntDivOne_2", proof] ∀ (n m : Int), n / 1 = m ===> ∀ (n m : Int), n = m

#testOptimize[ "IntFdivOne_2", proof] ∀ (n m : Int), Int.fdiv n 1 = m ===> ∀ (n m : Int), n = m

#testOptimize[ "IntTdivOne_2", proof] ∀ (n m : Int), Int.tdiv n 1 = m ===> ∀ (n m : Int), n = m

/-! Test cases for simplification rule n / 0 ===> 0 -/

#testOptimize[ "IntDivZero_1", proof] ∀ (n : Int), n / 0 = 0 ===> True

#testOptimize[ "IntFdivZero_1", proof] ∀ (n : Int), Int.fdiv n 0 = 0 ===> True

#testOptimize[ "IntTdivZero_1", proof] ∀ (n : Int), Int.tdiv n 0 = 0 ===> True


/-! Test cases for simplification rule 0 / n ===> 0 -/

#testOptimize[ "IntDivZero_2", proof] ∀ (n : Int), 0 / n = 0 ===> True

#testOptimize[ "IntFdivZero_2", proof] ∀ (n : Int), Int.fdiv 0 n = 0 ===> True

#testOptimize[ "IntTdivZero_2", proof] ∀ (n : Int), Int.tdiv 0 n = 0 ===> True


/-! Test cases for the gcd normalization `(N1 * n) / N2 ==> ((N1 "/" gcd) * n) / (N2 "/" gcd)`. -/

#testOptimize[ "IntEDivGcd_1", proof] ∀ (x : Int), (6 * x) / 4 = (3 * x) / 2 ===> True

#testOptimize[ "IntEDivGcd_2", proof] ∀ (x : Int), (6 * x) / (-4) = (3 * x) / (-2) ===> True

#testOptimize[ "IntFdivGcd_1", proof] ∀ (x : Int), Int.fdiv (6 * x) 4 = Int.fdiv (3 * x) 2 ===> True

#testOptimize[ "IntTdivGcd_1", proof] ∀ (x : Int), Int.tdiv (6 * x) 4 = Int.tdiv (3 * x) 2 ===> True

-- the reduced literals must match the steps of the other disjunct
#testOptimize[ "IntTdivGcd_2", proof]
  ∀ (n : Int), ¬ (Int.tdiv (4 * n) 6 = Int.tdiv (2 * n) 3) ∨ n = n ===> True

#testOptimize[ "IntEDivGcd_3", proof] ∀ (n : Int), ¬ ((4 * n) / 6 = (2 * n) / 3) ∨ n = n ===> True

#testOptimize[ "IntFdivGcd_2", proof]
  ∀ (n : Int), ¬ (Int.fdiv (4 * n) 6 = Int.fdiv (2 * n) 3) ∨ n = n ===> True

-- the gcd reduces the divisor to 1
#testOptimize[ "IntEDivGcd_4", proof] ∀ (x : Int), (x * 6) / 3 = 2 * x ===> True

/-! Test cases for the constant fold `N1 / N2 ==> N1 "/" N2` under a composed goal. -/

#testOptimize[ "IntDivCst_4", proof] ∀ (x y : Int), ((7 / 2 + x) = (x + 3)) ∧ y - y = 0 ===> True

#testOptimize[ "IntFdivCst_4", proof]
  ∀ (x y : Int), ((Int.fdiv 7 2 + x) = (x + 3)) ∧ y - y = 0 ===> True

#testOptimize[ "IntTdivCst_4", proof]
  ∀ (x y : Int), ((Int.tdiv (-7) 2 + x) = (x + (-3))) ∧ y - y = 0 ===> True

-- the fold is replayed under a hypothesis-driven cancellation
#testOptimize[ "IntDivCst_5", proof]
  ∀ (x y : Int), y ≠ 0 → (x * y) / y + 7 / 2 = x + 3 ===> True

/-! Test cases for steps over `Int.ediv`, written with `/` and with the core function. -/

#testOptimize[ "ElabDivComm", proof] ∀ (x y : Int), x / 2 + y = y + x / 2 ===> True

#testOptimize[ "RawEDivComm", proof] ∀ (x y : Int), Int.ediv x 2 + y = y + Int.ediv x 2 ===> True

-- ∀ (x y z : Int), (Int.ediv x 2 + y = y + x / 2) ∧ z - z = 0 ===> True
#testOptimize[ "MixedEDivComm", proof]
  ∀ (x y z : Int), (Int.ediv x 2 + y = y + x / 2) ∧ z - z = 0 ===> True

-- ∀ (x : Int), x / 2 ≠ 0 → Int.ediv (x / 2) (x / 2) = 1 ===> True
#testOptimize[ "MixedEDivSelf", proof] ∀ (x : Int), x / 2 ≠ 0 → Int.ediv (x / 2) (x / 2) = 1 ===> True

-- ∀ (n : Int), ¬ (Int.ediv (4 * n) 6 = Int.ediv (2 * n) 3) ∨ n = n ===> True
#testOptimize[ "RawEDivGcd_1", proof]
  ∀ (n : Int), ¬ (Int.ediv (4 * n) 6 = Int.ediv (2 * n) 3) ∨ n = n ===> True

-- ∀ (x : Int), Int.ediv (x * 6) 3 = 2 * x ===> True
#testOptimize[ "RawEDivGcd_2", proof] ∀ (x : Int), Int.ediv (x * 6) 3 = 2 * x ===> True

end Tests.OptimizeIntDiv
