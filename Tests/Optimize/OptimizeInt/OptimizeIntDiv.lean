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
