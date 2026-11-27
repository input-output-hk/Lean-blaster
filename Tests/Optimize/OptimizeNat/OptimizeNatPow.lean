import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatPow

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.pow
    (see `optimizeNatPow`):
      - n ^ 0 ==> 1
      - 0 ^ n ==> 0 (if nonZeroNatInHyps n)
      - 1 ^ n ==> 1
      - N1 ^ N2 ==> N1 "^" N2
    and the simplification rule on `LT.lt` involving ``Nat.pow (see `natPowLtReduce?` in `optimizeLT`):
      - n < N ^ n ==> True (if Type(n) = Nat ∧ N ≠ 0)

    NOTE: `nonZeroNatInHyps n` holds when `n` is a non-zero literal, when `0 < n` or `¬ (0 = n)` is in
    the hypothesis map (`n ≠ 0` and `1 ≤ n` are normalized to `¬ (0 = n)` beforehand), or when `n` is
    syntactically non-zero, i.e., `n := N + e`, `n := N ^ e` or `n := N * e` with `N ≠ 0` and `e`
    syntactically non-zero.
-/

/-! Test cases for `reduceApp` rule on ``Nat.pow (`N1 ^ N2 ==> N1 "^" N2`). -/

-- 2 ^ 10 ===> 1024
def natPowCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1024)
elab "natPowCst_1" : term => return natPowCst_1

#testOptimize [ "NatPowCst_1" ] (2 : Nat) ^ 10 ===> natPowCst_1

-- 0 ^ 0 ===> 1
def natPowCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natPowCst_2" : term => return natPowCst_2

#testOptimize [ "NatPowCst_2" ] (0 : Nat) ^ 0 ===> natPowCst_2

-- 0 ^ 5 ===> 0
def natPowCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natPowCst_3" : term => return natPowCst_3

#testOptimize [ "NatPowCst_3" ] (0 : Nat) ^ 5 ===> natPowCst_3

-- 7 ^ 1 ===> 7
def natPowCst_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 7)
elab "natPowCst_4" : term => return natPowCst_4

#testOptimize [ "NatPowCst_4" ] (7 : Nat) ^ 1 ===> natPowCst_4

-- ∀ (x y : Nat), 3 ^ 4 + x = y ===> ∀ (x y : Nat), y = 81 + x
#testOptimize [ "NatPowCst_5" ] (norm-result: 1) ∀ (x y : Nat), 3 ^ 4 + x = y ===> ∀ (x y : Nat), y = Nat.add 81 x


/-! Test cases for simplification rule `n ^ 0 ==> 1`. -/

-- ∀ (x y : Nat), x ^ 0 = y ===> ∀ (y : Nat), 1 = y
#testOptimize [ "NatPowZeroExp_1" ] (norm-result: 1) ∀ (x y : Nat), x ^ 0 = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x y : Nat), (x + 1) ^ 0 = y ===> ∀ (y : Nat), 1 = y
#testOptimize [ "NatPowZeroExp_2" ] (norm-result: 1) ∀ (x y : Nat), (x + 1) ^ 0 = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x y : Nat), (2 ^ x) ^ 0 = y ===> ∀ (y : Nat), 1 = y
#testOptimize [ "NatPowZeroExp_3" ] (norm-result: 1) ∀ (x y : Nat), (2 ^ x) ^ 0 = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x y : Nat), x ^ 0 + y ^ 0 = 2 ===> True
#testOptimize [ "NatPowZeroExp_4" ] ∀ (x y : Nat), x ^ 0 + y ^ 0 = 2 ===> True

-- ∀ (x y : Nat), x = 0 → 0 ^ x = y ===> ∀ (x y : Nat), 0 = x → 1 = y
-- `x` is substituted by `0` from the hypothesis: `0 ^ 0 ==> 1`
#testOptimize [ "NatPowZeroExp_5" ] (norm-result: 1) ∀ (x y : Nat), x = 0 → 0 ^ x = y ===> ∀ (x y : Nat), 0 = x → 1 = y


/-! Test cases for simplification rule `0 ^ n ==> 0 (if nonZeroNatInHyps n)`. -/

-- ∀ (x y : Nat), x ≠ 0 → 0 ^ x = y ===> ∀ (x y : Nat), ¬ (0 = x) → 0 = y
#testOptimize [ "NatPowZeroBase_1" ] (norm-result: 1) ∀ (x y : Nat), x ≠ 0 → 0 ^ x = y ===> ∀ (x y : Nat), ¬ 0 = x → 0 = y

-- ∀ (x y : Nat), 0 < x → 0 ^ x = y ===> ∀ (x y : Nat), 0 < x → 0 = y
#testOptimize [ "NatPowZeroBase_2" ] (norm-result: 1) ∀ (x y : Nat), 0 < x → 0 ^ x = y ===> ∀ (x y : Nat), 0 < x → 0 = y

-- ∀ (x y : Nat), 1 ≤ x → 0 ^ x = y ===> ∀ (x y : Nat), ¬ (0 = x) → 0 = y
#testOptimize [ "NatPowZeroBase_3" ] (norm-result: 1) ∀ (x y : Nat), 1 ≤ x → 0 ^ x = y ===> ∀ (x y : Nat), ¬ 0 = x → 0 = y

-- ∀ (x y : Nat), 0 ^ (x + 1) = y ===> ∀ (y : Nat), 0 = y
-- `1 + x` is syntactically non-zero: no hypothesis needed
#testOptimize [ "NatPowZeroBase_4" ] (norm-result: 1) ∀ (x y : Nat), 0 ^ (x + 1) = y ===> ∀ (y : Nat), 0 = y

-- ∀ (x y : Nat), 0 ^ (2 ^ x) = y ===> ∀ (y : Nat), 0 = y
-- `2 ^ x` is syntactically non-zero: no hypothesis needed
#testOptimize [ "NatPowZeroBase_5" ] (norm-result: 1) ∀ (x y : Nat), 0 ^ (2 ^ x) = y ===> ∀ (y : Nat), 0 = y

-- ∀ (x y : Nat), 0 ^ (3 * (x + 2)) = y ===> ∀ (y : Nat), 0 = y
-- `3 * (2 + x)` is syntactically non-zero: no hypothesis needed
#testOptimize [ "NatPowZeroBase_6" ] (norm-result: 1) ∀ (x y : Nat), 0 ^ (3 * (x + 2)) = y ===> ∀ (y : Nat), 0 = y

-- ∀ (x : Nat), 0 ^ (x + 1) = 0 ===> True
#testOptimize [ "NatPowZeroBase_7" ] ∀ (x : Nat), 0 ^ (x + 1) = 0 ===> True

-- ∀ (x y : Nat), x ≠ 0 → 0 ^ x < y ===> ∀ (x y : Nat), ¬ (0 = x) → 0 < y
#testOptimize [ "NatPowZeroBase_8" ] (norm-result: 1) ∀ (x y : Nat), x ≠ 0 → 0 ^ x < y ===> ∀ (x y : Nat), ¬ 0 = x → 0 < y


/-! Test cases for simplification rule `1 ^ n ==> 1`. -/

-- ∀ (x y : Nat), 1 ^ x = y ===> ∀ (y : Nat), 1 = y
#testOptimize [ "NatPowOneBase_1" ] (norm-result: 1) ∀ (x y : Nat), 1 ^ x = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x y : Nat), 1 ^ (x + y) = y ===> ∀ (y : Nat), 1 = y
#testOptimize [ "NatPowOneBase_2" ] (norm-result: 1) ∀ (x y : Nat), 1 ^ (x + y) = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x : Nat), 1 ^ x = 1 ===> True
#testOptimize [ "NatPowOneBase_3" ] ∀ (x : Nat), 1 ^ x = 1 ===> True

-- ∀ (x y : Nat), 1 ^ 0 ^ x = y ===> ∀ (y : Nat), 1 = y
-- `1 ^ (0 ^ x) ==> 1` whatever the exponent
#testOptimize [ "NatPowOneBase_4" ] (norm-result: 1) ∀ (x y : Nat), 1 ^ 0 ^ x = y ===> ∀ (y : Nat), 1 = y

-- ∀ (x : Nat), x < 1 ^ x ===> ∀ (x : Nat), 0 = x
-- `1 ^ x` is simplified to `1` beforehand, then `e < 1 ==> 0 = e`
#testOptimize [ "NatPowOneBase_5" ] (norm-result: 1) ∀ (x : Nat), x < 1 ^ x ===> ∀ (x : Nat), 0 = x


/-! Test cases for simplification rule `n < N ^ n ==> True (if N ≠ 0)`. -/

-- ∀ (x : Nat), x < 2 ^ x ===> True
#testOptimize [ "NatPowLt_1" ] ∀ (x : Nat), x < 2 ^ x ===> True

-- ∀ (x : Nat), x < 3 ^ x ===> True
#testOptimize [ "NatPowLt_2" ] ∀ (x : Nat), x < 3 ^ x ===> True

-- ∀ (x : Nat), x + 1 < 2 ^ (x + 1) ===> True
#testOptimize [ "NatPowLt_3" ] ∀ (x : Nat), x + 1 < 2 ^ (x + 1) ===> True

-- ∀ (x : Nat), 2 ^ x ≤ x ===> False
#testOptimize [ "NatPowLt_4" ] ∀ (x : Nat), 2 ^ x ≤ x ===> False

-- ∀ (x : Nat), ¬ (x < 2 ^ x) ===> False
#testOptimize [ "NatPowLt_5" ] ∀ (x : Nat), ¬ (x < 2 ^ x) ===> False

-- ∀ (x y : Nat), x < 10 ^ x ∧ y < 7 ^ y ===> True
#testOptimize [ "NatPowLt_6" ] ∀ (x y : Nat), x < 10 ^ x ∧ y < 7 ^ y ===> True

-- ∀ (x : Nat), Nat.log2 (x + 1) < x + 1 ===> True
-- `¬ (x < Nat.log2 (1 + x)) ==> ¬ ¬ (1 + x < 2 ^ (1 + x)) ==> True`
#testOptimize [ "NatPowLt_7" ] ∀ (x : Nat), Nat.log2 (x + 1) < x + 1 ===> True


/-! Test cases to ensure that the simplification rules are not applied without the required
    hypothesis, or when the operands do not have the expected shape. -/

-- ∀ (x y : Nat), 0 ^ x = y ===> ∀ (x y : Nat), y = 0 ^ x
-- no non-zero hypothesis on `x` (`0 ^ 0 = 1`)
#testOptimize [ "NatPowNoNorm_1" ] (norm-result: 1) ∀ (x y : Nat), 0 ^ x = y ===> ∀ (x y : Nat), y = Nat.pow 0 x

-- ∀ (x y : Nat), 0 ^ (2 * x) = y ===> ∀ (x y : Nat), y = 0 ^ (2 * x)
-- `2 * x` is not syntactically non-zero
#testOptimize [ "NatPowNoNorm_2" ] (norm-result: 1)
  ∀ (x y : Nat), 0 ^ (2 * x) = y ===> ∀ (x y : Nat), y = Nat.pow 0 (Nat.mul 2 x)

-- ∀ (x y : Nat), x ≠ 0 → 0 ^ (x * y) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 0 ^ (x * y)
-- the hypothesis is on `x`, not on the exponent `x * y`
#testOptimize [ "NatPowNoNorm_3" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → 0 ^ (x * y) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.pow 0 (Nat.mul x y)

-- ∀ (x y : Nat), 0 ^ (0 ^ x) = y ===> ∀ (x y : Nat), y = 0 ^ (0 ^ x)
-- `0 ^ x` is not syntactically non-zero
#testOptimize [ "NatPowNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Nat), 0 ^ (0 ^ x) = y ===> ∀ (x y : Nat), y = Nat.pow 0 (Nat.pow 0 x)

-- ∀ (x y : Nat), x ^ 1 = y ===> ∀ (x y : Nat), y = x ^ 1
-- no rule on exponent `1`
#testOptimize [ "NatPowNoNorm_5" ] (norm-result: 1) ∀ (x y : Nat), x ^ 1 = y ===> ∀ (x y : Nat), y = Nat.pow x 1

-- ∀ (x y : Nat), 2 ^ x = y ===> ∀ (x y : Nat), y = 2 ^ x
#testOptimize [ "NatPowNoNorm_6" ] (norm-result: 1) ∀ (x y : Nat), 2 ^ x = y ===> ∀ (x y : Nat), y = Nat.pow 2 x

-- ∀ (x y z : Nat), x ^ y = z ===> ∀ (x y z : Nat), z = x ^ y
#testOptimize [ "NatPowNoNorm_7" ] ∀ (x y z : Nat), x ^ y = z ===> ∀ (x y z : Nat), z = Nat.pow x y

-- ∀ (x : Nat), x < 0 ^ x ===> ∀ (x : Nat), x < 0 ^ x
-- `N = 0`
#testOptimize [ "NatPowNoNorm_8" ] (norm-result: 1) ∀ (x : Nat), x < 0 ^ x ===> ∀ (x : Nat), x < Nat.pow 0 x

-- ∀ (x y : Nat), x < 2 ^ y ===> ∀ (x y : Nat), x < 2 ^ y
-- the exponent is not the left operand
#testOptimize [ "NatPowNoNorm_9" ] (norm-result: 1) ∀ (x y : Nat), x < 2 ^ y ===> ∀ (x y : Nat), x < Nat.pow 2 y

-- ∀ (x : Nat), x < 2 ^ (x + 1) ===> ∀ (x : Nat), x < 2 ^ (1 + x)
#testOptimize [ "NatPowNoNorm_10" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ (x + 1) ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.add 1 x)

-- ∀ (x y : Nat), x < y ^ x ===> ∀ (x y : Nat), x < y ^ x
-- the base is not a literal
#testOptimize [ "NatPowNoNorm_11" ] ∀ (x y : Nat), x < y ^ x ===> ∀ (x y : Nat), x < Nat.pow y x

-- ∀ (x : Nat), 1 < x → x < x ^ 2 ===> ∀ (x : Nat), 1 < x → x < x ^ 2
#testOptimize [ "NatPowNoNorm_12" ] (norm-result: 1)
  ∀ (x : Nat), 1 < x → x < x ^ 2 ===> ∀ (x : Nat), 1 < x → x < Nat.pow x 2

-- ∀ (x : Nat), 2 ^ x < x ===> ∀ (x : Nat), 2 ^ x < x
-- the power is the left operand
#testOptimize [ "NatPowNoNorm_13" ] (norm-result: 1) ∀ (x : Nat), 2 ^ x < x ===> ∀ (x : Nat), Nat.pow 2 x < x

-- ∀ (x : Nat), x < 2 ^ x + 1 ===> ∀ (x : Nat), ¬ (2 ^ x < x)
-- `a < 1 + b ==> ¬ (b < a)` has precedence
#testOptimize [ "NatPowNoNorm_14" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ x + 1 ===> ∀ (x : Nat), ¬ Nat.pow 2 x < x

end Test.OptimizeNatPow
