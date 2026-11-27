import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2Pow

/-! ## Test objectives to validate the simplification rules on `Nat.log2` applied to a power
    (see `natPowLog2Reduce?` in `optimizeNatLog2`):
      - (2 ^ n).log2 ==> n
      - (N ^ n).log2 ==> "Nat.log2 N" * n (if N = 2 ^ (log2 N))

    The second rule triggers a restart (the resulting product is re-normalized).
-/

/-! Test cases for simplification rule `(2 ^ n).log2 ==> n`. -/

-- ∀ (x y : Nat), Nat.log2 (2 ^ x) = y ===> ∀ (x y : Nat), x = y
#testOptimize [ "Log2Pow_1" ] ∀ (x y : Nat), Nat.log2 (2 ^ x) = y ===> ∀ (x y : Nat), x = y

-- ∀ (x : Nat), Nat.log2 (2 ^ x) = x ===> True
#testOptimize [ "Log2Pow_2" ] ∀ (x : Nat), Nat.log2 (2 ^ x) = x ===> True

-- ∀ (x y : Nat), Nat.log2 (2 ^ (x + 1)) = y ===> ∀ (x y : Nat), y = 1 + x
#testOptimize [ "Log2Pow_3" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 ^ (x + 1)) = y ===> ∀ (x y : Nat), y = Nat.add 1 x

-- ∀ (x y : Nat), Nat.log2 (2 ^ x) = Nat.log2 (2 ^ y) ===> ∀ (x y : Nat), x = y
#testOptimize [ "Log2Pow_4" ] ∀ (x y : Nat), Nat.log2 (2 ^ x) = Nat.log2 (2 ^ y) ===> ∀ (x y : Nat), x = y

-- ∀ (x y : Nat), Nat.log2 (2 ^ Nat.log2 x) = y ===> ∀ (x y : Nat), y = Nat.log2 x
#testOptimize [ "Log2Pow_5" ] ∀ (x y : Nat), Nat.log2 (2 ^ Nat.log2 x) = y ===> ∀ (x y : Nat), y = Nat.log2 x

-- ∀ (x y : Nat), Nat.log2 (2 ^ (2 * x)) = y ===> ∀ (x y : Nat), y = 2 * x
#testOptimize [ "Log2Pow_6" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 ^ (2 * x)) = y ===> ∀ (x y : Nat), y = Nat.mul 2 x

-- ∀ (x y : Nat), Nat.log2 (2 ^ x) < y ===> ∀ (x y : Nat), x < y
#testOptimize [ "Log2Pow_7" ] ∀ (x y : Nat), Nat.log2 (2 ^ x) < y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), Nat.log2 (2 ^ x) < y + 1 ===> ∀ (x y : Nat), ¬ (y < x)
-- restart: `x < 1 + y ==> ¬ (y < x)` is applied on the simplified comparison
#testOptimize [ "Log2Pow_8" ] ∀ (x y : Nat), Nat.log2 (2 ^ x) < y + 1 ===> ∀ (x y : Nat), ¬ y < x


/-! Test cases for simplification rule `(N ^ n).log2 ==> "Nat.log2 N" * n (if N = 2 ^ (log2 N))`. -/

-- ∀ (x y : Nat), Nat.log2 (8 ^ x) = y ===> ∀ (x y : Nat), y = 3 * x
#testOptimize [ "Log2PowN_1" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (8 ^ x) = y ===> ∀ (x y : Nat), y = Nat.mul 3 x

-- ∀ (x y : Nat), Nat.log2 (16 ^ x) = y ===> ∀ (x y : Nat), y = 4 * x
#testOptimize [ "Log2PowN_2" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (16 ^ x) = y ===> ∀ (x y : Nat), y = Nat.mul 4 x

-- ∀ (x y : Nat), Nat.log2 (1024 ^ x) = y ===> ∀ (x y : Nat), y = 10 * x
#testOptimize [ "Log2PowN_3" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (1024 ^ x) = y ===> ∀ (x y : Nat), y = Nat.mul 10 x

-- ∀ (x y : Nat), Nat.log2 (4 ^ (x + y)) = y ===> ∀ (x y : Nat), y = 2 * (x + y)
#testOptimize [ "Log2PowN_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (4 ^ (x + y)) = y ===> ∀ (x y : Nat), y = Nat.mul 2 (Nat.add x y)

-- ∀ (x y : Nat), Nat.log2 (4 ^ x) < y ===> ∀ (x y : Nat), 2 * x < y
#testOptimize [ "Log2PowN_5" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (4 ^ x) < y ===> ∀ (x y : Nat), Nat.mul 2 x < y

-- ∀ (x : Nat), Nat.log2 (4 ^ x) = 2 * x ===> True
#testOptimize [ "Log2PowN_6" ] ∀ (x : Nat), Nat.log2 (4 ^ x) = 2 * x ===> True

-- ∀ (x y : Nat), Nat.log2 (1 ^ x) = y ===> ∀ (y : Nat), 0 = y
-- `1 ^ x` is folded to `1` beforehand, then `Nat.log2 1 ==> 0` (`x` no longer occurs)
#testOptimize [ "Log2PowN_7" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (1 ^ x) = y ===> ∀ (y : Nat), 0 = y


/-! Test cases to ensure that the simplification rules are not applied when the base
    is not a power of two or is not a literal. -/

-- ∀ (x y : Nat), Nat.log2 (3 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (3 ^ x)
#testOptimize [ "Log2PowNoNorm_1" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (3 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.pow 3 x)

-- ∀ (x y : Nat), Nat.log2 (6 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (6 ^ x)
#testOptimize [ "Log2PowNoNorm_2" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (6 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.pow 6 x)

-- ∀ (x y : Nat), Nat.log2 (0 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (0 ^ x)
#testOptimize [ "Log2PowNoNorm_3" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (0 ^ x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.pow 0 x)

-- ∀ (x y : Nat), Nat.log2 (x ^ 2) = y ===> ∀ (x y : Nat), y = Nat.log2 (x ^ 2)
#testOptimize [ "Log2PowNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (x ^ 2) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.pow x 2)

-- ∀ (x y : Nat), Nat.log2 (x ^ y) = y ===> ∀ (x y : Nat), y = Nat.log2 (x ^ y)
#testOptimize [ "Log2PowNoNorm_5" ] ∀ (x y : Nat), Nat.log2 (x ^ y) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.pow x y)

end Test.OptimizeNatLog2Pow
