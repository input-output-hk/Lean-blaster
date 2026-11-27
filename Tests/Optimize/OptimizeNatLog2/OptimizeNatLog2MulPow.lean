import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2MulPow

/-! ## Test objectives to validate the simplification rules on `Nat.log2` applied to a product
    with a power of a power-of-two literal (see `natMulPowLog2Reduce?` in `optimizeNatLog2`):
      - (2 ^ n * m).log2 | (m * 2 ^ n).log2 ==> n + m.log2
          (if ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap)
      - (N ^ n * m).log2 | (m * N ^ n).log2 ==> ("Nat.log2 N" * n) + m.log2
          (if ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ∧ N = 2 ^ (log2 N))

    Both rules trigger a restart (the resulting sum is re-normalized, which may reorder its operands).
    NOTE: `nonZeroNatInHyps m` also holds when `m` is a non-zero literal, or when `m` is syntactically
    non-zero, i.e., `m := N + e`, `m := N ^ e` or `m := N * e` with `N ≠ 0` and `e` syntactically non-zero.
-/

/-! Test cases for simplification rule `(2 ^ n * m).log2 | (m * 2 ^ n).log2 ==> n + m.log2`. -/

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = x + Nat.log2 y
#testOptimize [ "Log2MulPow_1" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.add x (Nat.log2 y)

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (y * 2 ^ x) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = x + Nat.log2 y
#testOptimize [ "Log2MulPow_2" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (y * 2 ^ x) = z ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.add x (Nat.log2 y)

-- ∀ (x y z : Nat), 0 < y → Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), 0 < y → z = x + Nat.log2 y
#testOptimize [ "Log2MulPow_3" ] (norm-result: 1)
  ∀ (x y z : Nat), 0 < y → Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), 0 < y → z = Nat.add x (Nat.log2 y)

-- ∀ (x y : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = x + Nat.log2 y ===> True
#testOptimize [ "Log2MulPow_4" ] ∀ (x y : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = x + Nat.log2 y ===> True

-- ∀ (x y : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = Nat.log2 (y * 2 ^ x) ===> True
#testOptimize [ "Log2MulPow_5" ] ∀ (x y : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) = Nat.log2 (y * 2 ^ x) ===> True

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ (x + 1) * y) = z
--   ===> ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 y + (1 + x)
-- restart: the sum `(1 + x) + Nat.log2 y` is reordered
#testOptimize [ "Log2MulPow_6" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ (x + 1) * y) = z
  ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.add (Nat.log2 y) (Nat.add 1 x)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 ^ x * x) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = x + Nat.log2 x
#testOptimize [ "Log2MulPow_7" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (2 ^ x * x) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add x (Nat.log2 x)

-- ∀ (x y : Nat), Nat.log2 (2 ^ x * 8) = y ===> ∀ (x y : Nat), y = 3 + x
-- `8` is a non-zero literal: no hypothesis needed, and `Nat.log2 8` is folded on restart
#testOptimize [ "Log2MulPow_8" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 ^ x * 8) = y ===> ∀ (x y : Nat), y = Nat.add 3 x

-- ∀ (x y : Nat), Nat.log2 (2 ^ x * 2) = y ===> ∀ (x y : Nat), y = 1 + x
#testOptimize [ "Log2MulPow_9" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 ^ x * 2) = y ===> ∀ (x y : Nat), y = Nat.add 1 x

-- ∀ (x y : Nat), Nat.log2 (8 * 2 ^ x) = y ===> ∀ (x y : Nat), y = 3 + x
#testOptimize [ "Log2MulPow_10" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (8 * 2 ^ x) = y ===> ∀ (x y : Nat), y = Nat.add 3 x

-- ∀ (x y : Nat), Nat.log2 (2 * 2 ^ x) = y ===> ∀ (x y : Nat), y = 1 + x
#testOptimize [ "Log2MulPow_11" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * 2 ^ x) = y ===> ∀ (x y : Nat), y = Nat.add 1 x

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) < z ===> ∀ (x y z : Nat), ¬ (0 = y) → x + Nat.log2 y < z
#testOptimize [ "Log2MulPow_12" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y) < z ===> ∀ (x y z : Nat), ¬ 0 = y → Nat.add x (Nat.log2 y) < z


/-! Test cases for simplification rule
    `(N ^ n * m).log2 | (m * N ^ n).log2 ==> ("Nat.log2 N" * n) + m.log2 (if N = 2 ^ (log2 N))`. -/

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (8 ^ x * y) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 y + 3 * x
-- restart: the sum `3 * x + Nat.log2 y` is reordered
#testOptimize [ "Log2MulPowN_1" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (8 ^ x * y) = z
  ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.add (Nat.log2 y) (Nat.mul 3 x)

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (y * 4 ^ x) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 y + 2 * x
#testOptimize [ "Log2MulPowN_2" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (y * 4 ^ x) = z
  ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.add (Nat.log2 y) (Nat.mul 2 x)

-- ∀ (x y z : Nat), 0 < y → Nat.log2 (16 ^ x * y) = z ===> ∀ (x y z : Nat), 0 < y → z = Nat.log2 y + 4 * x
#testOptimize [ "Log2MulPowN_3" ] (norm-result: 1)
  ∀ (x y z : Nat), 0 < y → Nat.log2 (16 ^ x * y) = z
  ===> ∀ (x y z : Nat), 0 < y → z = Nat.add (Nat.log2 y) (Nat.mul 4 x)

-- ∀ (x y : Nat), y ≠ 0 → Nat.log2 (8 ^ x * y) = 3 * x + Nat.log2 y ===> True
#testOptimize [ "Log2MulPowN_4" ] ∀ (x y : Nat), y ≠ 0 → Nat.log2 (8 ^ x * y) = 3 * x + Nat.log2 y ===> True


/-! Test cases where the factor is syntactically non-zero: no hypothesis is needed. -/

-- ∀ (x z : Nat), Nat.log2 (2 ^ x * 2 ^ z) = z ===> ∀ (x z : Nat), z = x + z
-- restart: `x + Nat.log2 (2 ^ z) ==> x + z`
#testOptimize [ "Log2MulPowNonZero_1" ] (norm-result: 1)
  ∀ (x z : Nat), Nat.log2 (2 ^ x * 2 ^ z) = z ===> ∀ (x z : Nat), z = Nat.add x z

-- ∀ (x y z : Nat), Nat.log2 (2 ^ x * (y + 1)) = z ===> ∀ (x y z : Nat), z = x + Nat.log2 (1 + y)
#testOptimize [ "Log2MulPowNonZero_2" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 (2 ^ x * (y + 1)) = z ===> ∀ (x y z : Nat), z = Nat.add x (Nat.log2 (Nat.add 1 y))

-- ∀ (x y z : Nat), Nat.log2 (2 ^ x * 3 ^ y) = z ===> ∀ (x y z : Nat), z = x + Nat.log2 (3 ^ y)
#testOptimize [ "Log2MulPowNonZero_3" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 (2 ^ x * 3 ^ y) = z ===> ∀ (x y z : Nat), z = Nat.add x (Nat.log2 (Nat.pow 3 y))

-- ∀ (x y z : Nat), Nat.log2 ((y + 1) * 4 ^ x) = z ===> ∀ (x y z : Nat), z = Nat.log2 (1 + y) + 2 * x
#testOptimize [ "Log2MulPowNonZero_4" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 ((y + 1) * 4 ^ x) = z
  ===> ∀ (x y z : Nat), z = Nat.add (Nat.log2 (Nat.add 1 y)) (Nat.mul 2 x)


/-! Test cases to ensure that the simplification rules are not applied without the non-zero
    hypothesis (unless the factor is syntactically non-zero), or when the base is not a
    power-of-two literal. -/

-- ∀ (x y z : Nat), Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), z = Nat.log2 (y * 2 ^ x)
#testOptimize [ "Log2MulPowNoNorm_1" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 (2 ^ x * y) = z ===> ∀ (x y z : Nat), z = Nat.log2 (Nat.mul y (Nat.pow 2 x))

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (3 ^ x * y) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 (y * 3 ^ x)
#testOptimize [ "Log2MulPowNoNorm_2" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (3 ^ x * y) = z
  ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.log2 (Nat.mul y (Nat.pow 3 x))

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (x ^ 2 * y) = z ===> ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 (y * x ^ 2)
#testOptimize [ "Log2MulPowNoNorm_3" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (x ^ 2 * y) = z
  ===> ∀ (x y z : Nat), ¬ 0 = y → z = Nat.log2 (Nat.mul y (Nat.pow x 2))

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * (2 * y)) = z ===>
-- ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 ((2 * y) * 2 ^ x)
-- the hypothesis is on `y`, not on the factor `2 * y`, which is not syntactically non-zero
#testOptimize [ "Log2MulPowNoNorm_4" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * (2 * y)) = z ===>
  ∀ (x y z : Nat), ¬ 0 = y → z = Nat.log2 (Nat.mul (Nat.mul 2 y) (Nat.pow 2 x))

-- ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y * 2) = z ===>
-- ∀ (x y z : Nat), ¬ (0 = y) → z = Nat.log2 (2 * (y * 2 ^ x))
-- the product is normalized to `2 * (y * 2 ^ x)`: neither `y * 2 ^ x` is known non-zero,
-- nor is `2 * (y * 2 ^ x)` of the form `2 ^ n * m`
#testOptimize [ "Log2MulPowNoNorm_5" ] (norm-result: 1)
  ∀ (x y z : Nat), y ≠ 0 → Nat.log2 (2 ^ x * y * 2) = z ===>
  ∀ (x y z : Nat), ¬ 0 = y → z = Nat.log2 (Nat.mul 2 (Nat.mul y (Nat.pow 2 x)))

end Test.OptimizeNatLog2MulPow
