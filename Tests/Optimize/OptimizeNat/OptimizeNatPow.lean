import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatPow

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.pow -/
/-! Test cases for `reduceApp` rule on ``Nat.pow -/

-- 5 ^ 0 ===> 1
def natPowCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natPowCst_1": term => return natPowCst_1

#testOptimize ["NatPowCst_1", proof] (5 : Nat) ^ 0 ===> natPowCst_1

/-! Test cases for simplification rule `n ^ 0 ==> 1`-/
#testOptimize ["NatPowIden_1", proof] ∀ (n : Nat), n ^ 0 = 1 ===> True

end Test.OptimizeNatPow
