import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2Eq

/-! ## Test objectives to validate the simplification rule on `Eq` comparing `Nat.log2` with a
    literal (see `natLogEqRel?` in `optimizeEq`):
      - 0 = n.log2 ==> n < 2 (if Type (n) = Nat)
      - N = n.log2 ==> ¬ (n < "2 ^ N") ∧ n < "2 ^ (N + 1)" (if Type (n) = Nat ∧ N ≠ 0)

    The rule triggers a restart (the resulting comparisons are re-normalized).
    NOTE: `n.log2 = N` is normalized to `N = n.log2` beforehand (literal first).
-/

/-! Test cases for simplification rule `0 = n.log2 ==> n < 2`. -/

-- ∀ (x : Nat), Nat.log2 x = 0 ===> ∀ (x : Nat), x < 2
#testOptimize [ "Log2EqZero_1" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x = 0 ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), 0 = Nat.log2 x ===> ∀ (x : Nat), x < 2
#testOptimize [ "Log2EqZero_2" ] (norm-result: 1) ∀ (x : Nat), 0 = Nat.log2 x ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), Nat.log2 x ≠ 0 ===> ∀ (x : Nat), ¬ (x < 2)
#testOptimize [ "Log2EqZero_3" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x ≠ 0 ===> ∀ (x : Nat), ¬ x < 2

-- ∀ (x : Nat), Nat.log2 x = 0 → x < 2 ===> True
#testOptimize [ "Log2EqZero_4" ] ∀ (x : Nat), Nat.log2 x = 0 → x < 2 ===> True

-- ∀ (x : Nat), x < 2 → Nat.log2 x = 0 ===> True
#testOptimize [ "Log2EqZero_5" ] ∀ (x : Nat), x < 2 → Nat.log2 x = 0 ===> True

-- ∀ (x : Nat), (Nat.log2 x = 0) = (x < 2) ===> True
#testOptimize [ "Log2EqZero_6" ] ∀ (x : Nat), (Nat.log2 x = 0) = (x < 2) ===> True

-- ∀ (x : Nat), Nat.log2 x < 1 ===> ∀ (x : Nat), x < 2
-- `e < 1 ==> 0 = e` is applied first, then the rule
#testOptimize [ "Log2EqZero_7" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < 1 ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = 1 ===> ∀ (x : Nat), ¬ (0 = x) → x < 2
-- restart: `1 + Nat.log2 x = 1 ==> 0 = Nat.log2 x ==> x < 2`
#testOptimize [ "Log2EqZero_8" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) = 1 ===> ∀ (x : Nat), ¬ 0 = x → x < 2


/-! Test cases for simplification rule `N = n.log2 ==> ¬ (n < "2 ^ N") ∧ n < "2 ^ (N + 1)"`. -/

-- ∀ (x : Nat), Nat.log2 x = 3 ===> ∀ (x : Nat), ¬ (x < 8) ∧ x < 16
#testOptimize [ "Log2EqCst_1" ] (norm-result: 1)
  ∀ (x : Nat), Nat.log2 x = 3 ===> ∀ (x : Nat), ¬ (x < 8) ∧ x < 16

-- ∀ (x : Nat), 3 = Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 8) ∧ x < 16
#testOptimize [ "Log2EqCst_2" ] (norm-result: 1)
  ∀ (x : Nat), 3 = Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 8) ∧ x < 16

-- ∀ (x : Nat), Nat.log2 x = 1 ===> ∀ (x : Nat), ¬ (x < 2) ∧ x < 4
#testOptimize [ "Log2EqCst_3" ] (norm-result: 1)
  ∀ (x : Nat), Nat.log2 x = 1 ===> ∀ (x : Nat), ¬ (x < 2) ∧ x < 4

-- ∀ (x : Nat), 2 = Nat.log2 (x + 1) ===> ∀ (x : Nat), ¬ (x < 3) ∧ x < 7
-- restart: `¬ (1 + x < 4) ∧ 1 + x < 8` is further simplified
#testOptimize [ "Log2EqCst_4" ] (norm-result: 1)
  ∀ (x : Nat), 2 = Nat.log2 (x + 1) ===> ∀ (x : Nat), ¬ (x < 3) ∧ x < 7

-- ∀ (x : Nat), Nat.log2 x = 1 → False ===> ∀ (x : Nat), ¬ (¬ (x < 2) ∧ x < 4)
#testOptimize [ "Log2EqCst_5" ] (norm-result: 1)
  ∀ (x : Nat), Nat.log2 x = 1 → False ===> ∀ (x : Nat), ¬ (¬ (x < 2) ∧ x < 4)

-- ∀ (x : Nat), Nat.log2 x = 3 → 8 ≤ x ===> True
#testOptimize [ "Log2EqCst_6" ] ∀ (x : Nat), Nat.log2 x = 3 → 8 ≤ x ===> True

-- ∀ (x : Nat), Nat.log2 x = 3 → x < 16 ===> True
#testOptimize [ "Log2EqCst_7" ] ∀ (x : Nat), Nat.log2 x = 3 → x < 16 ===> True

-- ∀ (x : Nat), 8 ≤ x → x < 16 → Nat.log2 x = 3 ===> True
#testOptimize [ "Log2EqCst_8" ] ∀ (x : Nat), 8 ≤ x → x < 16 → Nat.log2 x = 3 ===> True

-- ∀ (x : Nat), (Nat.log2 x = 2) = (4 ≤ x ∧ x < 8) ===> True
#testOptimize [ "Log2EqCst_9" ] ∀ (x : Nat), (Nat.log2 x = 2) = (4 ≤ x ∧ x < 8) ===> True


/-! Test cases to ensure that the simplification rule is not applied when no operand is a
    literal, or that a rule with a higher precedence applies. -/

-- ∀ (x y : Nat), Nat.log2 x = y ===> ∀ (x y : Nat), y = Nat.log2 x
#testOptimize [ "Log2EqNoNorm_1" ] ∀ (x y : Nat), Nat.log2 x = y ===> ∀ (x y : Nat), y = Nat.log2 x

-- ∀ (x : Nat), Nat.log2 (x + 1) = Nat.log2 x ===> ∀ (x : Nat), Nat.log2 x = Nat.log2 (1 + x)
#testOptimize [ "Log2EqNoNorm_2" ] (norm-result: 1)
  ∀ (x : Nat), Nat.log2 (x + 1) = Nat.log2 x ===> ∀ (x : Nat), Nat.log2 x = Nat.log2 (Nat.add 1 x)

-- ∀ (x : Nat), Nat.log2 x = Nat.log2 x ===> True
-- `e1 = e2 ==> True (if e1 =ₚₜᵣ e2)` has precedence
#testOptimize [ "Log2EqNoNorm_3" ] ∀ (x : Nat), Nat.log2 x = Nat.log2 x ===> True

-- ∀ (x : Nat), Nat.log2 (2 ^ x) = 3 ===> ∀ (x : Nat), 3 = x
-- `Nat.log2 (2 ^ x)` is simplified to `x` beforehand
#testOptimize [ "Log2EqNoNorm_4" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 (2 ^ x) = 3 ===> ∀ (x : Nat), 3 = x

-- Nat.log2 8 = 3 ===> True
-- `Nat.log2 8` is folded beforehand
#testOptimize [ "Log2EqNoNorm_5" ] Nat.log2 8 = 3 ===> True

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 2 ^ y) = y ===> ∀ (x y : Nat), ¬ (0 = x) → y = y + Nat.log2 x
#testOptimize [ "Log2EqNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 (x * 2 ^ y) = y ===> ∀ (x y : Nat), ¬ 0 = x → y = Nat.add y (Nat.log2 x)

end Test.OptimizeNatLog2Eq
