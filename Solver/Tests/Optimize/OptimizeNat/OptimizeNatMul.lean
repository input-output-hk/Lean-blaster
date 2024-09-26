import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatMul

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.mul -/

/-! Test cases for `reduceApp` rule on ``Nat.mul. -/

-- 0 * 432 ===> 0
def natMulCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natMulCst_1" : term => return natMulCst_1

#testOptimize [ "NatMulCst_1" ] (0 : Nat) * 432 ===> natMulCst_1

-- 432 * 0 ===> 0
#testOptimize [ "NatMulCst_2" ] 432 * (0 : Nat) ===> natMulCst_1

def natMulCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 432)
elab "natMulCst_3" : term => return natMulCst_3

-- 432 * 1 ===> 32
#testOptimize [ "NatMulCst_3" ] 432 * (1 : Nat) ===> natMulCst_3

-- 1 * 432 ===> 32
#testOptimize [ "NatMulCst_4" ] 1 * (432 : Nat) ===> natMulCst_3

-- 34 * 432 ===> 14688
def natMulCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 14688)
elab "natMulCst_5" : term => return natMulCst_5

#testOptimize [ "NatMulCst_5" ] (34 : Nat) * 432 ===> natMulCst_5


end Test.OptimizeNatMul
