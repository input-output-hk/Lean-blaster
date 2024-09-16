import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatDiv

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.div -/

/-! Test cases for `reduceApp` rule on ``Nat.div. -/

-- 0 / 432 ===> 0
def natDivCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natDivCst_1" : term => return natDivCst_1

#testOptimize [ "NatDivCst_1" ] (0 : Nat) / 432 ===> natDivCst_1

-- 432 / 0  ===> 0
-- NOTE: divison by zero not triggered
#testOptimize [ "NatDivCst_2" ] (432 : Nat) / 0 ===> natDivCst_1

-- 7 / 3 ===> 2
def natDivCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 2)
elab "natDivCst_3" : term => return natDivCst_3

#testOptimize [ "NatDivCst_3" ] (7 : Nat) / 3 ===> natDivCst_3

-- 18 / 3 ===> 6
def natDivCst_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 6)
elab "natDivCst_4" : term => return natDivCst_4

#testOptimize [ "NatDivCst_4" ] (18 : Nat) / 3 ===> natDivCst_4

end Test.OptimizeNatDiv
