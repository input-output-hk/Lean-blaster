import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2Mul

/-! ## Test objectives to validate the simplification rules on `Nat.log2` applied to a product
    with a power-of-two literal (see `natMulLog2Reduce?` in `optimizeNatLog2`):
      - (2 * n).log2 ==> 1 + n.log2 (if ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap)
      - (N * n).log2 ==> "Nat.log2 N" + n.log2
          (if ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap ∧ N = 2 ^ (log2 N))

    Both rules trigger a restart (the resulting sum is re-normalized).
    NOTE: `nonZeroNatInHyps n` holds when `0 < n` or `¬ (0 = n)` is in the hypothesis map
    (`n ≠ 0` and `1 ≤ n` are normalized to `¬ (0 = n)` beforehand), or when `n` is syntactically
    non-zero, i.e., `n := N + e`, `n := N ^ e` or `n := N * e` with `N ≠ 0` and `e` syntactically non-zero.
    NOTE: `n * N` is normalized to `N * n` beforehand (literal first).
-/

/-! Test cases for simplification rule `(2 * n).log2 ==> 1 + n.log2`. -/

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 1 + Nat.log2 x
#testOptimize [ "Log2Mul_1" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 1 (Nat.log2 x)

-- ∀ (x y : Nat), 0 < x → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), 0 < x → y = 1 + Nat.log2 x
#testOptimize [ "Log2Mul_2" ] (norm-result: 1)
  ∀ (x y : Nat), 0 < x → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), 0 < x → y = Nat.add 1 (Nat.log2 x)

-- ∀ (x y : Nat), ¬ (0 = x) → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 1 + Nat.log2 x
#testOptimize [ "Log2Mul_3" ] (norm-result: 1)
  ∀ (x y : Nat), ¬ (0 = x) → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 1 (Nat.log2 x)

-- ∀ (x y : Nat), 1 ≤ x → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 1 + Nat.log2 x
#testOptimize [ "Log2Mul_4" ] (norm-result: 1)
  ∀ (x y : Nat), 1 ≤ x → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 1 (Nat.log2 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 2) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 1 + Nat.log2 x
#testOptimize [ "Log2Mul_5" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 2) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 1 (Nat.log2 x)

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = Nat.log2 x + 1 ===> True
#testOptimize [ "Log2Mul_6" ] ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = Nat.log2 x + 1 ===> True

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = 1 + Nat.log2 x ===> True
#testOptimize [ "Log2Mul_7" ] ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = 1 + Nat.log2 x ===> True

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = Nat.log2 x ===> ∀ (x : Nat), 0 = x
-- restart: `1 + a = a ==> False`, then `¬ (0 = x) → False ==> 0 = x`
#testOptimize [ "Log2Mul_8" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = Nat.log2 x ===> ∀ (x : Nat), 0 = x

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * (2 * x)) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 2 + Nat.log2 x
-- `2 * (2 * x)` is normalized to `4 * x` beforehand
#testOptimize [ "Log2Mul_9" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * (2 * x)) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 2 (Nat.log2 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * x) < y ===> ∀ (x y : Nat), ¬ (0 = x) → 1 + Nat.log2 x < y
#testOptimize [ "Log2Mul_10" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * x) < y ===> ∀ (x y : Nat), ¬ 0 = x → Nat.add 1 (Nat.log2 x) < y

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < 3 ===> ∀ (x : Nat), ¬ (0 = x) → x < 4
-- restart: `1 + Nat.log2 x < 3 ==> Nat.log2 x < 2 ==> x < 2 ^ 2 ==> x < 4`
#testOptimize [ "Log2Mul_11" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < 3 ===> ∀ (x : Nat), ¬ 0 = x → x < 4

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < Nat.log2 x + 1 ===> ∀ (x : Nat), 0 = x
-- restart: `1 + Nat.log2 x < 1 + Nat.log2 x ==> False`
#testOptimize [ "Log2Mul_12" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < Nat.log2 x + 1 ===> ∀ (x : Nat), 0 = x


/-! Test cases for simplification rule `(N * n).log2 ==> "Nat.log2 N" + n.log2 (if N = 2 ^ (log2 N))`. -/

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (8 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 3 + Nat.log2 x
#testOptimize [ "Log2MulN_1" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (8 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 3 (Nat.log2 x)

-- ∀ (x y : Nat), 0 < x → Nat.log2 (4 * x) = y ===> ∀ (x y : Nat), 0 < x → y = 2 + Nat.log2 x
#testOptimize [ "Log2MulN_2" ] (norm-result: 1)
  ∀ (x y : Nat), 0 < x → Nat.log2 (4 * x) = y ===> ∀ (x y : Nat), 0 < x → y = Nat.add 2 (Nat.log2 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 16) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 4 + Nat.log2 x
#testOptimize [ "Log2MulN_3" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 16) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 4 (Nat.log2 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 4) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 2 + Nat.log2 x
#testOptimize [ "Log2MulN_4" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 4) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 2 (Nat.log2 x)

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (8 * x) = 3 + Nat.log2 x ===> True
#testOptimize [ "Log2MulN_5" ] ∀ (x : Nat), x ≠ 0 → Nat.log2 (8 * x) = 3 + Nat.log2 x ===> True


/-! Test cases where the operand is syntactically non-zero: no hypothesis is needed. -/

-- ∀ (x y : Nat), Nat.log2 (2 * (x + 1)) = y ===> ∀ (x y : Nat), y = 1 + Nat.log2 (1 + x)
#testOptimize [ "Log2MulNonZero_1" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * (x + 1)) = y ===> ∀ (x y : Nat), y = Nat.add 1 (Nat.log2 (Nat.add 1 x))

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * (x + 1)) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = 1 + Nat.log2 (1 + x)
#testOptimize [ "Log2MulNonZero_2" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 * (x + 1)) = y
  ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add 1 (Nat.log2 (Nat.add 1 x))

-- ∀ (x y : Nat), Nat.log2 (2 * 2 ^ x) = y ===> ∀ (x y : Nat), y = 1 + x
-- restart: `1 + Nat.log2 (2 ^ x) ==> 1 + x`
#testOptimize [ "Log2MulNonZero_3" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * 2 ^ x) = y ===> ∀ (x y : Nat), y = Nat.add 1 x

-- ∀ (x y : Nat), Nat.log2 (4 * (3 ^ x + 1)) = y ===> ∀ (x y : Nat), y = 2 + Nat.log2 (1 + 3 ^ x)
#testOptimize [ "Log2MulNonZero_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (4 * (3 ^ x + 1)) = y ===> ∀ (x y : Nat), y = Nat.add 2 (Nat.log2 (Nat.add 1 (Nat.pow 3 x)))


/-! Test cases to ensure that the simplification rules are not applied without the non-zero
    hypothesis (unless the operand is syntactically non-zero), or when the literal is not a power
    of two. -/

-- ∀ (x y : Nat), Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), y = Nat.log2 (2 * x)
#testOptimize [ "Log2MulNoNorm_1" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.mul 2 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (3 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = Nat.log2 (3 * x)
#testOptimize [ "Log2MulNoNorm_2" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (3 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.log2 (Nat.mul 3 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (6 * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = Nat.log2 (6 * x)
#testOptimize [ "Log2MulNoNorm_3" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (6 * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.log2 (Nat.mul 6 x)

-- ∀ (x y : Nat), Nat.log2 (2 * (3 * x)) = y ===> ∀ (x y : Nat), y = Nat.log2 (6 * x)
-- `2 * (3 * x)` is normalized to `6 * x` beforehand, which is not a power of two
#testOptimize [ "Log2MulNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * (3 * x)) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.mul 6 x)

-- ∀ (x y : Nat), Nat.log2 (2 * (3 * x + 2)) = y ===> ∀ (x y : Nat), y = 1 + Nat.log2 (2 + 3 * x)
-- `2 + 3 * x` is syntactically non-zero
#testOptimize [ "Log2MulNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * (3 * x + 2)) = y ===> ∀ (x y : Nat), y = Nat.add 1 (Nat.log2 (Nat.add 2 (Nat.mul 3 x)))

-- ∀ (x y : Nat), y ≠ 0 → Nat.log2 (x * y) = y ===> ∀ (x y : Nat), ¬ (0 = y) → y = Nat.log2 (x * y)
-- no literal factor
#testOptimize [ "Log2MulNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Nat), y ≠ 0 → Nat.log2 (x * y) = y ===> ∀ (x y : Nat), ¬ 0 = y → y = Nat.log2 (Nat.mul x y)

-- ∀ (x y : Nat), x = 0 → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), 0 = x → 0 = y
-- `x` is substituted by `0` from the hypothesis: `Nat.log2 (2 * 0) ==> 0`
#testOptimize [ "Log2MulNoNorm_7" ] (norm-result: 1)
  ∀ (x y : Nat), x = 0 → Nat.log2 (2 * x) = y ===> ∀ (x y : Nat), 0 = x → 0 = y

end Test.OptimizeNatLog2Mul
