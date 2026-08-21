import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntMod

/-! ## Test objectives to validate normalization and simplification rules on ``Int.emod, ``Int.tmod and ``Int.fmod -/
/-! Test cases for `reduceApp` rule on ``Int.emod, ``Int.tmod and ``Int.fmod -/

def intModCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 0))
elab "intModCst_1" : term => return intModCst_1

def intModCst_2 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 5))
elab "intModCst_2" : term => return intModCst_2

-- 0 % 5 ===> 0
#testOptimize [ "IntModCst_1", proof] (0 : Int) % 5 ===> intModCst_1

#testOptimize [ "IntFmodCst_1", proof] Int.fmod 0 5 ===> intModCst_1

#testOptimize [ "IntTmodCst_1", proof] Int.tmod 0 5 ===> intModCst_1

-- 5 % 1 ===> 0
#testOptimize [ "IntModCst_2", proof] (5 : Int) % 1 ===> intModCst_1

#testOptimize [ "IntFmodCst_2", proof] Int.fmod 5 1 ===> intModCst_1

#testOptimize [ "IntTmodCst_2", proof] Int.tmod 5 1 ===> intModCst_1

-- 5 % 0 ===> 5
#testOptimize [ "IntModCst_3", proof] (5 : Int) % 0 ===> intModCst_2

#testOptimize [ "IntFmodCst_3", proof] Int.fmod 5 0 ===> intModCst_2

#testOptimize [ "IntTmodCst_3", proof] Int.tmod 5 0 ===> intModCst_2

/-! Test cases for simplification rule 0 % n ===> 0 -/
#testOptimize ["IntModZero_1", proof] ∀ (n : Int), 0 % n = 0 ===> True

#testOptimize ["IntFmodZero_1", proof] ∀ (n : Int), Int.fmod 0 n = 0 ===> True

#testOptimize ["IntTmodZero_1", proof] ∀ (n : Int), Int.tmod 0 n = 0 ===> True

/- Test cases for simplification rule n % 1 ===> 0 -/
#testOptimize ["IntModOne_1", proof] ∀ (n : Int), n % 1 = 0 ===> True

#testOptimize ["IntFmodOne_1", proof] ∀ (n : Int), Int.fmod n 1 = 0 ===> True

#testOptimize ["IntTmodOne_1", proof] ∀ (n : Int), Int.tmod n 1 = 0 ===> True

/- Test cases for simplification rule n % 0 ===> n -/
#testOptimize ["IntModZero_2", proof] ∀ (n : Int), n % 0 = n ===> True

#testOptimize ["IntFmodZero_2", proof] ∀ (n : Int), Int.fmod n 0 = n ===> True

#testOptimize ["IntTmodZero_2", proof] ∀ (n : Int), Int.tmod n 0 = n ===> True

#testOptimize ["IntModZero_3", proof] ∀ (n m : Int), n % 0 = m ===> ∀ (n m : Int), n = m

#testOptimize ["IntFmodZero_3", proof] ∀ (n m : Int), Int.fmod n 0 = m ===> ∀ (n m : Int), n = m

#testOptimize ["IntTmodZero_3", proof] ∀ (n m : Int), Int.tmod n 0 = m ===> ∀ (n m : Int), n = m


/-! Test cases for the gcd normalization `(N1 * n) % N2 ==> 0 (if N1 % N2 = 0)`. -/

#testOptimize ["IntEModGcd_1", proof] ∀ (x : Int), (6 * x) % 3 = 0 ===> True

#testOptimize ["IntEModGcd_2", proof] ∀ (x : Int), (6 * x) % (-3) = 0 ===> True

#testOptimize ["IntFmodGcd_1", proof] ∀ (x : Int), Int.fmod (6 * x) 3 = 0 ===> True

#testOptimize ["IntTmodGcd_1", proof] ∀ (x : Int), Int.tmod (6 * x) 3 = 0 ===> True

end Tests.OptimizeIntMod
