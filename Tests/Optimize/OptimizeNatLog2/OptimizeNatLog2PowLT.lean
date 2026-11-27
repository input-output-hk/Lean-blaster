import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2PowLT

/-! ## Test objectives to validate the simplification rules on `LT.lt` comparing an operand with
    a power of two of its own `Nat.log2` (see `natPowLogLtReduce?` in `optimizeLT`):
      - n < 2 ^ n.log2 ==> False (if Type (n) = Nat ∧ nonZeroNatInHyps n)
      - n < 2 ^ (N + n.log2) ==> True (if Type (n) = Nat ∧ N ≠ 0)

    NOTE: `nonZeroNatInHyps n` also holds when `n` is syntactically non-zero, i.e., `n := N + e`,
    `n := N ^ e` or `n := N * e` with `N ≠ 0` and `e` syntactically non-zero.
    NOTE: `n.log2 + N` is normalized to `N + n.log2` beforehand, and the hypotheses are introduced
    with implications; a conclusion simplified to `False` therefore yields the negation of the
    hypothesis, e.g., `¬ (0 = x) → False ==> 0 = x`.
-/

/-! Test cases for simplification rule `n < 2 ^ n.log2 ==> False (if nonZeroNatInHyps n)`. -/

-- ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), 0 = x
#testOptimize [ "Log2PowLtSelf_1" ] (norm-result: 1) ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), 0 < x → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), 0 = x
#testOptimize [ "Log2PowLtSelf_2" ] (norm-result: 1) ∀ (x : Nat), 0 < x → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), x ≠ 0 → (x < 2 ^ Nat.log2 x) = False ===> True
#testOptimize [ "Log2PowLtSelf_3" ] ∀ (x : Nat), x ≠ 0 → (x < 2 ^ Nat.log2 x) = False ===> True

-- ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x ≤ x ===> True
#testOptimize [ "Log2PowLtSelf_4" ] ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x ≤ x ===> True

-- ∀ (x : Nat), x ≠ 0 → ¬ (2 ^ Nat.log2 x ≤ x) ===> ∀ (x : Nat), 0 = x
#testOptimize [ "Log2PowLtSelf_5" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → ¬ (2 ^ Nat.log2 x ≤ x) ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x < x + 1 ===> True
-- `a < 1 + b ==> ¬ (b < a)` is applied first, then the rule
#testOptimize [ "Log2PowLtSelf_6" ] ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x < x + 1 ===> True

-- ∀ (x y : Nat), y ≠ 0 → y < 2 ^ Nat.log2 y → x < y ===> True
#testOptimize [ "Log2PowLtSelf_7" ] ∀ (x y : Nat), y ≠ 0 → y < 2 ^ Nat.log2 y → x < y ===> True

-- ∀ (x : Nat), x ≠ 0 → x < 2 ^ (Nat.log2 x * 1) ===> ∀ (x : Nat), 0 = x
-- `Nat.log2 x * 1` is simplified to `Nat.log2 x` beforehand
#testOptimize [ "Log2PowLtSelf_8" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → x < 2 ^ (Nat.log2 x * 1) ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 x ∨ x < 2 ^ (Nat.log2 x + 1) ===> True
#testOptimize [ "Log2PowLtSelf_9" ] ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 x ∨ x < 2 ^ (Nat.log2 x + 1) ===> True

-- ∀ (x : Nat), x + 1 < 2 ^ Nat.log2 (x + 1) ===> False
-- `1 + x` is syntactically non-zero: no hypothesis needed
#testOptimize [ "Log2PowLtSelf_11" ] ∀ (x : Nat), x + 1 < 2 ^ Nat.log2 (x + 1) ===> False

-- ∀ (x : Nat), 2 ^ x < 2 ^ Nat.log2 (2 ^ x) ===> False
-- `Nat.log2 (2 ^ x)` is simplified to `x` beforehand, and `2 ^ x` is syntactically non-zero
#testOptimize [ "Log2PowLtSelf_12" ] ∀ (x : Nat), 2 ^ x < 2 ^ Nat.log2 (2 ^ x) ===> False

-- ∀ (x : Nat), x = 0 → x < 2 ^ Nat.log2 x ===> True
-- `x` is substituted by `0` from the hypothesis: `0 < 2 ^ Nat.log2 0 ==> 0 < 1 ==> True`
#testOptimize [ "Log2PowLtSelf_10" ] ∀ (x : Nat), x = 0 → x < 2 ^ Nat.log2 x ===> True


/-! Test cases for simplification rule `n < 2 ^ (N + n.log2) ==> True (if N ≠ 0)`. -/

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) ===> True
#testOptimize [ "Log2PowLtSucc_1" ] ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) ===> True

-- ∀ (x : Nat), x < 2 ^ (1 + Nat.log2 x) ===> True
#testOptimize [ "Log2PowLtSucc_2" ] ∀ (x : Nat), x < 2 ^ (1 + Nat.log2 x) ===> True

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 3) ===> True
#testOptimize [ "Log2PowLtSucc_3" ] ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 3) ===> True

-- ∀ (x : Nat), 2 ^ (Nat.log2 x + 1) ≤ x ===> False
#testOptimize [ "Log2PowLtSucc_4" ] ∀ (x : Nat), 2 ^ (Nat.log2 x + 1) ≤ x ===> False

-- ∀ (x : Nat), ¬ (x < 2 ^ (Nat.log2 x + 1)) ===> False
#testOptimize [ "Log2PowLtSucc_5" ] ∀ (x : Nat), ¬ (x < 2 ^ (Nat.log2 x + 1)) ===> False

-- ∀ (x : Nat), x + 1 < 2 ^ (Nat.log2 (x + 1) + 1) ===> True
#testOptimize [ "Log2PowLtSucc_6" ] ∀ (x : Nat), x + 1 < 2 ^ (Nat.log2 (x + 1) + 1) ===> True

-- ∀ (x : Nat), 2 ≤ x → x < 2 ^ (Nat.log2 x + 1) ===> True
#testOptimize [ "Log2PowLtSucc_7" ] ∀ (x : Nat), 2 ≤ x → x < 2 ^ (Nat.log2 x + 1) ===> True

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) ∧ ¬ (x < 2 ^ (Nat.log2 x + 2)) ===> False
#testOptimize [ "Log2PowLtSucc_8" ] ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) ∧ ¬ (x < 2 ^ (Nat.log2 x + 2)) ===> False

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) → x < 2 ^ (Nat.log2 x + 2) ===> True
#testOptimize [ "Log2PowLtSucc_9" ] ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 1) → x < 2 ^ (Nat.log2 x + 2) ===> True


/-! Test cases to ensure that the simplification rules are not applied without the non-zero
    hypothesis, or when the operands do not have the expected shape. -/

-- ∀ (x : Nat), x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), x < 2 ^ Nat.log2 x
#testOptimize [ "Log2PowLtNoNorm_1" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.log2 x)

-- ∀ (x : Nat), 2 ≤ x → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 2) → x < 2 ^ Nat.log2 x
-- `¬ (x < 2)` is not a recognized non-zero hypothesis
-- NOTE: Will be simplified via patch in blaster extension
#testOptimize [ "Log2PowLtNoNorm_2" ] (norm-result: 1)
  ∀ (x : Nat), 2 ≤ x → x < 2 ^ Nat.log2 x ===> ∀ (x : Nat), ¬ x < 2 → x < Nat.pow 2 (Nat.log2 x)

-- ∀ (x : Nat), 2 ^ Nat.log2 x < x + 1 ===> ∀ (x : Nat), ¬ (x < 2 ^ Nat.log2 x)
#testOptimize [ "Log2PowLtNoNorm_3" ] (norm-result: 1)
  ∀ (x : Nat), 2 ^ Nat.log2 x < x + 1 ===> ∀ (x : Nat), ¬ x < Nat.pow 2 (Nat.log2 x)

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 0) ===> ∀ (x : Nat), x < 2 ^ Nat.log2 x
-- `N = 0`: the sum is folded and the first rule needs a non-zero hypothesis
#testOptimize [ "Log2PowLtNoNorm_4" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ (Nat.log2 x + 0) ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.log2 x)

-- ∀ (x y : Nat), x < 2 ^ (Nat.log2 y + 1) ===> ∀ (x y : Nat), x < 2 ^ (1 + Nat.log2 y)
-- the operand of `Nat.log2` is not the left operand
#testOptimize [ "Log2PowLtNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Nat), x < 2 ^ (Nat.log2 y + 1) ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 1 (Nat.log2 y))

-- ∀ (x y : Nat), x ≠ 0 → x < 2 ^ Nat.log2 y ===> ∀ (x y : Nat), ¬ (0 = x) → x < 2 ^ Nat.log2 y
#testOptimize [ "Log2PowLtNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → x < 2 ^ Nat.log2 y ===> ∀ (x y : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.log2 y)

-- ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 (x + 1) ===> ∀ (x : Nat), ¬ (0 = x) → x < 2 ^ Nat.log2 (1 + x)
#testOptimize [ "Log2PowLtNoNorm_7" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → x < 2 ^ Nat.log2 (x + 1)
  ===> ∀ (x : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.log2 (Nat.add 1 x))

-- ∀ (x : Nat), x < 2 ^ (Nat.log2 (x + 1) + 1) ===> ∀ (x : Nat), x < 2 ^ (1 + Nat.log2 (1 + x))
#testOptimize [ "Log2PowLtNoNorm_8" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ (Nat.log2 (x + 1) + 1)
  ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.add 1 (Nat.log2 (Nat.add 1 x)))

-- ∀ (x : Nat), x < 4 ^ (Nat.log2 x + 1) ===> ∀ (x : Nat), x < 4 ^ (1 + Nat.log2 x)
-- the base is not `2`
#testOptimize [ "Log2PowLtNoNorm_9" ] (norm-result: 1)
  ∀ (x : Nat), x < 4 ^ (Nat.log2 x + 1) ===> ∀ (x : Nat), x < Nat.pow 4 (Nat.add 1 (Nat.log2 x))

-- ∀ (x : Nat), x ≠ 0 → x < 4 ^ Nat.log2 x ===> ∀ (x : Nat), ¬ (0 = x) → x < 4 ^ Nat.log2 x
#testOptimize [ "Log2PowLtNoNorm_10" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → x < 4 ^ Nat.log2 x ===> ∀ (x : Nat), ¬ 0 = x → x < Nat.pow 4 (Nat.log2 x)

-- ∀ (x y : Nat), x < 2 ^ (Nat.log2 x + y) ===> ∀ (x y : Nat), x < 2 ^ (y + Nat.log2 x)
-- the summand is not a literal
#testOptimize [ "Log2PowLtNoNorm_11" ] (norm-result: 1)
  ∀ (x y : Nat), x < 2 ^ (Nat.log2 x + y) ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add y (Nat.log2 x))

-- ∀ (x : Nat), x < 2 ^ (2 * Nat.log2 x) ===> ∀ (x : Nat), x < 2 ^ (2 * Nat.log2 x)
#testOptimize [ "Log2PowLtNoNorm_12" ] (norm-result: 1)
  ∀ (x : Nat), x < 2 ^ (2 * Nat.log2 x) ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.mul 2 (Nat.log2 x))

-- ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x < x ===> ∀ (x : Nat), ¬ (0 = x) → 2 ^ Nat.log2 x < x
-- the power is the left operand
#testOptimize [ "Log2PowLtNoNorm_13" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → 2 ^ Nat.log2 x < x ===> ∀ (x : Nat), ¬ 0 = x → Nat.pow 2 (Nat.log2 x) < x

end Test.OptimizeNatLog2PowLT
