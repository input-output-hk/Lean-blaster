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

#testOptimize [ "intAddCst_1", proof] (0 : Int) + 1 ===> intAddCst_1

-- 0 - 2 ===> -2
def intAddCst_2 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.negSucc [])
  (Lean.Expr.lit (Lean.Literal.natVal 1))

elab "intAddCst_2" : term => return intAddCst_2

#testOptimize [ "intAddCst_2", proof] (0 : Int) - 2 ===> intAddCst_2
