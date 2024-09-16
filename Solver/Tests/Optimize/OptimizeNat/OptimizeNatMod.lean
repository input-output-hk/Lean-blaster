import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatMod

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.mod -/

/-! Test cases for `reduceApp` rule on ``Nat.div. -/

-- 0 % 432 ===> 0
def natModCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natModCst_1" : term => return natModCst_1

#testOptimize [ "NatModCst_1" ] (0 : Nat) % 432 ===> natModCst_1

-- 432  % 0 ===> 432
-- NOTE: divison by zero not triggered
def natModCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 432)
elab "natModCst_2" : term => return natModCst_2

#testOptimize [ "NatModCst_2" ] (432 : Nat) % 0 ===> natModCst_2

-- 7 % 3 ===> 1
def natModCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natModCst_3" : term => return natModCst_3

#testOptimize [ "NatModCst_3" ] (7 : Nat) % 3 ===> natModCst_3

-- 18 % 3 ===> 0
#testOptimize [ "NatModCst_4" ] (18 : Nat) % 3 ===> natModCst_1

end Test.OptimizeNatMod
