import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2LT

/-! ## Test objectives to validate the simplification rules on `LT.lt` involving `Nat.log2`
    (see `natLogLtReduce?` in `optimizeLT`):
      - n < n.log2 ==> False (if Type (n) = Nat)
      - k < n.log2 ==> ¬ (n < 2 ^ (1 + k)) (if Type (n) = Nat)
      - n.log2 < n ==> ¬ (0 = n) (if Type (n) = Nat)
      - n.log2 < N ==> n < "2 ^ N" (if Type (n) = Nat ∧ N ≠ 0)
      - n.log2 < N + k ==> n < 2 ^ (N + k) (if Type (n) = Nat ∧ N ≠ 0)
      - n.log2 < k ==> n < 2 ^ k (if Type (n) = Nat ∧ (nonZeroNatInHyps n ∨ nonZeroNatInHyps k))

    All the rules but the first trigger a restart (the resulting comparison is re-normalized).
    NOTE: `e1 ≤ e2` is normalized to `¬ (e2 < e1)` beforehand, so the rules also apply
    through `LE.le`.
    NOTE: `n.log2 < k` is not simplified without a non-zero hypothesis: for `n = 0` and `k = 0`,
    `n.log2 < k` is `False` whereas `n < 2 ^ k` is `True`. A right operand `N + k` with `N ≠ 0`
    is never zero, hence no hypothesis is needed in that case.
    NOTE: `nonZeroNatInHyps e` also holds when `e` is syntactically non-zero, i.e., `e := N + e'`,
    `e := N ^ e'` or `e := N * e'` with `N ≠ 0` and `e'` syntactically non-zero.
    NOTE: the rules on the left operand (`n.log2 < …`) have precedence over the rules on the right
    operand (`… < n.log2`).
-/

/-! Test cases for simplification rule `n < n.log2 ==> False`. -/

-- ∀ (x : Nat), x < Nat.log2 x ===> False
#testOptimize [ "Log2LtSelf_1" ] ∀ (x : Nat), x < Nat.log2 x ===> False

-- ∀ (x : Nat), x + 1 < Nat.log2 (x + 1) ===> False
#testOptimize [ "Log2LtSelf_2" ] ∀ (x : Nat), x + 1 < Nat.log2 (x + 1) ===> False

-- ∀ (x : Nat), Nat.log2 x ≤ x ===> True
#testOptimize [ "Log2LtSelf_3" ] ∀ (x : Nat), Nat.log2 x ≤ x ===> True

-- ∀ (x : Nat), x < Nat.log2 x → False ===> True
#testOptimize [ "Log2LtSelf_4" ] ∀ (x : Nat), x < Nat.log2 x → False ===> True

-- ∀ (x : Nat), Nat.log2 x ≤ x → x < 2 ^ (x + 1) ===> ∀ (x : Nat), x < 2 ^ (1 + x)
#testOptimize [ "Log2LtSelf_5" ] (norm-result: 1)
  ∀ (x : Nat), Nat.log2 x ≤ x → x < 2 ^ (x + 1) ===> ∀ (x : Nat), x < Nat.pow 2 (Nat.add 1 x)


/-! Test cases for simplification rule `k < n.log2 ==> ¬ (n < 2 ^ (1 + k))`. -/

-- ∀ (x y : Nat), x < Nat.log2 y ===> ∀ (x y : Nat), ¬ (y < 2 ^ (1 + x))
#testOptimize [ "Log2LtRight_1" ] (norm-result: 1)
  ∀ (x y : Nat), x < Nat.log2 y ===> ∀ (x y : Nat), ¬ y < Nat.pow 2 (Nat.add 1 x)

-- ∀ (x : Nat), 3 < Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 16)
-- restart: `2 ^ (1 + 3)` is folded
#testOptimize [ "Log2LtRight_2" ] (norm-result: 1) ∀ (x : Nat), 3 < Nat.log2 x ===> ∀ (x : Nat), ¬ x < 16

-- ∀ (x : Nat), 0 < Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 2)
#testOptimize [ "Log2LtRight_3" ] (norm-result: 1) ∀ (x : Nat), 0 < Nat.log2 x ===> ∀ (x : Nat), ¬ x < 2

-- ∀ (x y : Nat), x + 1 < Nat.log2 y ===> ∀ (x y : Nat), ¬ (y < 2 ^ (2 + x))
-- restart: `1 + (1 + x)` is folded to `2 + x`
#testOptimize [ "Log2LtRight_4" ] (norm-result: 1)
  ∀ (x y : Nat), x + 1 < Nat.log2 y ===> ∀ (x y : Nat), ¬ y < Nat.pow 2 (Nat.add 2 x)

-- ∀ (x : Nat), x < Nat.log2 (2 * x) ===> ∀ (x : Nat), ¬ (2 * x < 2 ^ (1 + x))
#testOptimize [ "Log2LtRight_5" ] (norm-result: 1)
  ∀ (x : Nat), x < Nat.log2 (2 * x) ===> ∀ (x : Nat), ¬ Nat.mul 2 x < Nat.pow 2 (Nat.add 1 x)

-- ∀ (x y : Nat), Nat.log2 x < Nat.log2 y ===> ∀ (x y : Nat), ¬ (y < 2 ^ (1 + Nat.log2 x))
-- no non-zero hypothesis on `x` nor `Nat.log2 y`: the rules on the left operand do not apply
-- (compare with `Log2LtHyp_11`)
#testOptimize [ "Log2LtRight_6" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < Nat.log2 y ===> ∀ (x y : Nat), ¬ y < Nat.pow 2 (Nat.add 1 (Nat.log2 x))

-- ∀ (x y : Nat), Nat.log2 x ≤ y ===> ∀ (x y : Nat), x < 2 ^ (1 + y)
-- restart: `Nat.log2 x ≤ y ==> ¬ (y < Nat.log2 x) ==> ¬ ¬ (x < 2 ^ (1 + y))`
#testOptimize [ "Log2LtRight_7" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x ≤ y ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 1 y)

-- ∀ (x y : Nat), Nat.log2 x < y + 1 ===> ∀ (x y : Nat), x < 2 ^ (1 + y)
-- restart: `Nat.log2 x < 1 + y ==> ¬ (y < Nat.log2 x) ==> ¬ ¬ (x < 2 ^ (1 + y))`
#testOptimize [ "Log2LtRight_8" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < y + 1 ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 1 y)

-- ∀ (x y : Nat), Nat.log2 x < Nat.log2 y + 1 ===> ∀ (x y : Nat), x < 2 ^ (1 + Nat.log2 y)
#testOptimize [ "Log2LtRight_9" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < Nat.log2 y + 1 ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 1 (Nat.log2 y))

-- ∀ (x : Nat), Nat.log2 x ≤ 3 ===> ∀ (x : Nat), x < 16
#testOptimize [ "Log2LtRight_10" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x ≤ 3 ===> ∀ (x : Nat), x < 16

-- ∀ (x : Nat), Nat.log2 x ≤ 0 ===> ∀ (x : Nat), x < 2
#testOptimize [ "Log2LtRight_11" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x ≤ 0 ===> ∀ (x : Nat), x < 2

-- ∀ (x y : Nat), x < Nat.log2 y → ¬ (y < 2 ^ (x + 1)) ===> True
#testOptimize [ "Log2LtRight_12" ] ∀ (x y : Nat), x < Nat.log2 y → ¬ (y < 2 ^ (x + 1)) ===> True

-- ∀ (x y : Nat), (x < Nat.log2 y) = (2 ^ (1 + x) ≤ y) ===> True
#testOptimize [ "Log2LtRight_13" ] ∀ (x y : Nat), (x < Nat.log2 y) = (2 ^ (1 + x) ≤ y) ===> True

-- ∀ (x : Nat), 2 < Nat.log2 x → 8 ≤ x ===> True
#testOptimize [ "Log2LtRight_14" ] ∀ (x : Nat), 2 < Nat.log2 x → 8 ≤ x ===> True

-- ∀ (x : Nat), 0 < Nat.log2 x → 2 ≤ x ===> True
#testOptimize [ "Log2LtRight_15" ] ∀ (x : Nat), 0 < Nat.log2 x → 2 ≤ x ===> True

-- ∀ (x : Nat), Nat.log2 (x + 1) < x + 1 ===> True
-- `a < 1 + b ==> ¬ (b < a)` has precedence over `n.log2 < n ==> ¬ (0 = n)`:
-- `¬ (x < Nat.log2 (1 + x)) ==> ¬ ¬ (1 + x < 2 ^ (1 + x)) ==> True` (see `n < N ^ n ==> True`)
#testOptimize [ "Log2LtRight_16" ] ∀ (x : Nat), Nat.log2 (x + 1) < x + 1 ===> True

-- ∀ (x : Nat), Nat.log2 (x + 1) ≤ x ===> True
-- restart: `¬ (x < Nat.log2 (1 + x)) ==> ¬ ¬ (1 + x < 2 ^ (1 + x)) ==> True`
#testOptimize [ "Log2LtRight_17" ] ∀ (x : Nat), Nat.log2 (x + 1) ≤ x ===> True


/-! Test cases for simplification rule `n.log2 < n ==> ¬ (0 = n)`. -/

-- ∀ (x : Nat), Nat.log2 x < x ===> ∀ (x : Nat), ¬ (0 = x)
#testOptimize [ "Log2LtOperand_1" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < x ===> ∀ (x : Nat), ¬ 0 = x

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 x < x ===> True
#testOptimize [ "Log2LtOperand_2" ] ∀ (x : Nat), x ≠ 0 → Nat.log2 x < x ===> True

-- ∀ (x : Nat), x ≤ Nat.log2 x ===> ∀ (x : Nat), 0 = x
-- restart: `x ≤ Nat.log2 x ==> ¬ (Nat.log2 x < x) ==> ¬ ¬ (0 = x)`
#testOptimize [ "Log2LtOperand_3" ] (norm-result: 1) ∀ (x : Nat), x ≤ Nat.log2 x ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), Nat.log2 x < x → x ≠ 0 ===> True
#testOptimize [ "Log2LtOperand_4" ] ∀ (x : Nat), Nat.log2 x < x → x ≠ 0 ===> True

-- ∀ (x : Nat), x < Nat.log2 x + 1 ===> ∀ (x : Nat), 0 = x
-- restart: `x < 1 + Nat.log2 x ==> ¬ (Nat.log2 x < x) ==> ¬ ¬ (0 = x)`
#testOptimize [ "Log2LtOperand_5" ] (norm-result: 1) ∀ (x : Nat), x < Nat.log2 x + 1 ===> ∀ (x : Nat), 0 = x


/-! Test cases for simplification rule `n.log2 < N ==> n < "2 ^ N" (if N ≠ 0)`. -/

-- ∀ (x : Nat), Nat.log2 x < 3 ===> ∀ (x : Nat), x < 8
#testOptimize [ "Log2LtCst_1" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < 3 ===> ∀ (x : Nat), x < 8

-- ∀ (x : Nat), Nat.log2 x < 2 ===> ∀ (x : Nat), x < 4
#testOptimize [ "Log2LtCst_2" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < 2 ===> ∀ (x : Nat), x < 4

-- ∀ (x : Nat), Nat.log2 x < 10 ===> ∀ (x : Nat), x < 1024
#testOptimize [ "Log2LtCst_3" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < 10 ===> ∀ (x : Nat), x < 1024

-- ∀ (x : Nat), 3 ≤ Nat.log2 x ===> ∀ (x : Nat), ¬ (x < 8)
#testOptimize [ "Log2LtCst_4" ] (norm-result: 1) ∀ (x : Nat), 3 ≤ Nat.log2 x ===> ∀ (x : Nat), ¬ x < 8

-- ∀ (x : Nat), Nat.log2 x < 1 ===> ∀ (x : Nat), x < 2
-- `e < 1 ==> 0 = e` has precedence, then `0 = n.log2 ==> n < 2` (see `natLogEqRel?` in `optimizeEq`)
#testOptimize [ "Log2LtCst_5" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 x < 1 ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < 3 ===> ∀ (x : Nat), ¬ (0 = x) → x < 4
-- restart: `1 + Nat.log2 x < 3 ==> Nat.log2 x < 2 ==> x < 4`
#testOptimize [ "Log2LtCst_6" ] (norm-result: 1)
  ∀ (x : Nat), x ≠ 0 → Nat.log2 (2 * x) < 3 ===> ∀ (x : Nat), ¬ 0 = x → x < 4

-- ∀ (x : Nat), Nat.log2 x < 5 → x < 32 ===> True
#testOptimize [ "Log2LtCst_7" ] ∀ (x : Nat), Nat.log2 x < 5 → x < 32 ===> True

-- ∀ (x : Nat), ¬ (Nat.log2 x < 5) → 32 ≤ x ===> True
#testOptimize [ "Log2LtCst_8" ] ∀ (x : Nat), ¬ (Nat.log2 x < 5) → 32 ≤ x ===> True

-- ∀ (x : Nat), (Nat.log2 x < 5) = (x < 32) ===> True
#testOptimize [ "Log2LtCst_9" ] ∀ (x : Nat), (Nat.log2 x < 5) = (x < 32) ===> True


/-! Test cases for simplification rule `n.log2 < N + k ==> n < 2 ^ (N + k) (if N ≠ 0)`. -/

-- ∀ (x y : Nat), Nat.log2 x < y + 2 ===> ∀ (x y : Nat), x < 2 ^ (2 + y)
#testOptimize [ "Log2LtAddCst_1" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < y + 2 ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 2 y)

-- ∀ (x y : Nat), Nat.log2 x < 2 + y ===> ∀ (x y : Nat), x < 2 ^ (2 + y)
#testOptimize [ "Log2LtAddCst_2" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < 2 + y ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 2 y)

-- ∀ (x y : Nat), Nat.log2 x < 3 + Nat.log2 y ===> ∀ (x y : Nat), x < 2 ^ (3 + Nat.log2 y)
#testOptimize [ "Log2LtAddCst_3" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < 3 + Nat.log2 y ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.add 3 (Nat.log2 y))

-- ∀ (x y z : Nat), Nat.log2 x < 5 + (y + z) ===> ∀ (x y z : Nat), x < 2 ^ (5 + (y + z))
#testOptimize [ "Log2LtAddCst_4" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 x < 5 + (y + z) ===> ∀ (x y z : Nat), x < Nat.pow 2 (Nat.add 5 (Nat.add y z))

-- ∀ (x y : Nat), y + 2 ≤ Nat.log2 x ===> ∀ (x y : Nat), ¬ (x < 2 ^ (2 + y))
-- restart: `y + 2 ≤ Nat.log2 x ==> ¬ (Nat.log2 x < 2 + y) ==> ¬ (x < 2 ^ (2 + y))`
#testOptimize [ "Log2LtAddCst_5" ] (norm-result: 1)
  ∀ (x y : Nat), y + 2 ≤ Nat.log2 x ===> ∀ (x y : Nat), ¬ x < Nat.pow 2 (Nat.add 2 y)

-- ∀ (x y : Nat), Nat.log2 (2 * x) < y + 2 ===> ∀ (x y : Nat), 2 * x < 2 ^ (2 + y)
-- no hypothesis on `x`: `Nat.log2 (2 * x)` is not simplified, the rule applies on `n := 2 * x`
#testOptimize [ "Log2LtAddCst_6" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (2 * x) < y + 2 ===> ∀ (x y : Nat), Nat.mul 2 x < Nat.pow 2 (Nat.add 2 y)

-- ∀ (x y : Nat), Nat.log2 x < y + 2 → x < 2 ^ (y + 2) ===> True
#testOptimize [ "Log2LtAddCst_7" ] ∀ (x y : Nat), Nat.log2 x < y + 2 → x < 2 ^ (y + 2) ===> True

-- ∀ (x y : Nat), (Nat.log2 x < y + 2) = (x < 2 ^ (2 + y)) ===> True
#testOptimize [ "Log2LtAddCst_8" ] ∀ (x y : Nat), (Nat.log2 x < y + 2) = (x < 2 ^ (2 + y)) ===> True


/-! Test cases for simplification rule
    `n.log2 < k ==> n < 2 ^ k (if nonZeroNatInHyps n ∨ nonZeroNatInHyps k)`. -/

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y ===> ∀ (x y : Nat), ¬ (0 = x) → x < 2 ^ y
#testOptimize [ "Log2LtHyp_1" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y ===> ∀ (x y : Nat), ¬ 0 = x → x < Nat.pow 2 y

-- ∀ (x y : Nat), y ≠ 0 → Nat.log2 x < y ===> ∀ (x y : Nat), ¬ (0 = y) → x < 2 ^ y
#testOptimize [ "Log2LtHyp_2" ] (norm-result: 1)
  ∀ (x y : Nat), y ≠ 0 → Nat.log2 x < y ===> ∀ (x y : Nat), ¬ 0 = y → x < Nat.pow 2 y

-- ∀ (x y : Nat), 0 < x → Nat.log2 x < y ===> ∀ (x y : Nat), 0 < x → x < 2 ^ y
#testOptimize [ "Log2LtHyp_3" ] (norm-result: 1)
  ∀ (x y : Nat), 0 < x → Nat.log2 x < y ===> ∀ (x y : Nat), 0 < x → x < Nat.pow 2 y

-- ∀ (x y : Nat), 0 < y → Nat.log2 x < y ===> ∀ (x y : Nat), 0 < y → x < 2 ^ y
#testOptimize [ "Log2LtHyp_4" ] (norm-result: 1)
  ∀ (x y : Nat), 0 < y → Nat.log2 x < y ===> ∀ (x y : Nat), 0 < y → x < Nat.pow 2 y

-- ∀ (x y : Nat), x ≠ 0 → y ≤ Nat.log2 x ===> ∀ (x y : Nat), ¬ (0 = x) → ¬ (x < 2 ^ y)
-- restart: `y ≤ Nat.log2 x ==> ¬ (Nat.log2 x < y) ==> ¬ (x < 2 ^ y)`
#testOptimize [ "Log2LtHyp_5" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → y ≤ Nat.log2 x ===> ∀ (x y : Nat), ¬ 0 = x → ¬ x < Nat.pow 2 y

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < 2 ^ y ===> ∀ (x y : Nat), ¬ (0 = x) → x < 2 ^ 2 ^ y
#testOptimize [ "Log2LtHyp_6" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < 2 ^ y ===> ∀ (x y : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.pow 2 y)

-- ∀ (x y z : Nat), x ≠ 0 → Nat.log2 x < y + z ===> ∀ (x y z : Nat), ¬ (0 = x) → x < 2 ^ (y + z)
#testOptimize [ "Log2LtHyp_7" ] (norm-result: 1)
  ∀ (x y z : Nat), x ≠ 0 → Nat.log2 x < y + z ===> ∀ (x y z : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.add y z)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y * 2 ===> ∀ (x y : Nat), ¬ (0 = x) → x < 2 ^ (2 * y)
#testOptimize [ "Log2LtHyp_8" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y * 2 ===> ∀ (x y : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.mul 2 y)

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y → x < 2 ^ y ===> True
#testOptimize [ "Log2LtHyp_9" ] ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < y → x < 2 ^ y ===> True

-- ∀ (x y : Nat), x ≠ 0 → (Nat.log2 x < y) = (x < 2 ^ y) ===> True
#testOptimize [ "Log2LtHyp_10" ] ∀ (x y : Nat), x ≠ 0 → (Nat.log2 x < y) = (x < 2 ^ y) ===> True

-- ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < Nat.log2 y ===> ∀ (x y : Nat), ¬ (0 = x) → x < 2 ^ Nat.log2 y
-- the rules on the left operand have precedence over `k < n.log2 ==> ¬ (n < 2 ^ (1 + k))`
#testOptimize [ "Log2LtHyp_11" ] (norm-result: 1)
  ∀ (x y : Nat), x ≠ 0 → Nat.log2 x < Nat.log2 y ===> ∀ (x y : Nat), ¬ 0 = x → x < Nat.pow 2 (Nat.log2 y)

-- ∀ (x y : Nat), Nat.log2 x < 2 ^ y ===> ∀ (x y : Nat), x < 2 ^ 2 ^ y
-- `2 ^ y` is syntactically non-zero: no hypothesis needed
#testOptimize [ "Log2LtHyp_12" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < 2 ^ y ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.pow 2 y)

-- ∀ (x y : Nat), Nat.log2 x < (y + 2) * 3 ===> ∀ (x y : Nat), x < 2 ^ (3 * (2 + y))
-- `3 * (2 + y)` is syntactically non-zero: no hypothesis needed
#testOptimize [ "Log2LtHyp_13" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < (y + 2) * 3 ===> ∀ (x y : Nat), x < Nat.pow 2 (Nat.mul 3 (Nat.add 2 y))

-- ∀ (x y : Nat), Nat.log2 (x + 1) < y ===> ∀ (x y : Nat), 1 + x < 2 ^ y
-- `1 + x` is syntactically non-zero: no hypothesis needed
#testOptimize [ "Log2LtHyp_14" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (x + 1) < y ===> ∀ (x y : Nat), Nat.add 1 x < Nat.pow 2 y


/-! Test cases to ensure that the simplification rules are not applied when the operands do not
    have the expected shape, when the non-zero hypothesis is missing, or that a rule with a higher
    precedence in `optimizeLT` applies. -/

-- ∀ (x y : Nat), Nat.log2 x < y ===> ∀ (x y : Nat), Nat.log2 x < y
-- no non-zero hypothesis on `x` nor `y` (`Nat.log2 0 < 0` is `False` whereas `0 < 2 ^ 0` is `True`)
#testOptimize [ "Log2LtNoNorm_1" ] ∀ (x y : Nat), Nat.log2 x < y ===> ∀ (x y : Nat), Nat.log2 x < y

-- ∀ (x y z : Nat), Nat.log2 x < y + z ===> ∀ (x y z : Nat), Nat.log2 x < y + z
-- the sum has no non-zero literal summand
#testOptimize [ "Log2LtNoNorm_2" ] (norm-result: 1)
  ∀ (x y z : Nat), Nat.log2 x < y + z ===> ∀ (x y z : Nat), Nat.log2 x < Nat.add y z

-- ∀ (x y : Nat), Nat.log2 x < 0 + y ===> ∀ (x y : Nat), Nat.log2 x < y
-- `0 + y` is simplified to `y` beforehand
#testOptimize [ "Log2LtNoNorm_3" ] ∀ (x y : Nat), Nat.log2 x < 0 + y ===> ∀ (x y : Nat), Nat.log2 x < y

-- ∀ (x y : Nat), Nat.log2 x < y * 3 ===> ∀ (x y : Nat), Nat.log2 x < 3 * y
-- `3 * y` is not syntactically non-zero
#testOptimize [ "Log2LtNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < y * 3 ===> ∀ (x y : Nat), Nat.log2 x < Nat.mul 3 y

-- ∀ (x y : Nat), Nat.log2 (3 * x) < y ===> ∀ (x y : Nat), Nat.log2 (3 * x) < y
-- `3 * x` is not syntactically non-zero
#testOptimize [ "Log2LtNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (3 * x) < y ===> ∀ (x y : Nat), Nat.log2 (Nat.mul 3 x) < y

-- ∀ (x y : Nat), Nat.log2 x < y - 2 ===> ∀ (x y : Nat), Nat.log2 x < y - 2
#testOptimize [ "Log2LtNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x < y - 2 ===> ∀ (x y : Nat), Nat.log2 x < Nat.sub y 2

-- ∀ (x y : Nat), Nat.log2 x < Nat.log2 (2 ^ y) ===> ∀ (x y : Nat), Nat.log2 x < y
-- `Nat.log2 (2 ^ y)` is simplified to `y` beforehand, then no non-zero hypothesis
#testOptimize [ "Log2LtNoNorm_7" ] ∀ (x y : Nat), Nat.log2 x < Nat.log2 (2 ^ y) ===> ∀ (x y : Nat), Nat.log2 x < y

-- ∀ (x y : Nat), Nat.log2 x + 1 < y ===> ∀ (x y : Nat), 1 + Nat.log2 x < y
-- the left operand is not exactly `Nat.log2 x`
#testOptimize [ "Log2LtNoNorm_8" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 x + 1 < y ===> ∀ (x y : Nat), Nat.add 1 (Nat.log2 x) < y

-- ∀ (x : Nat), Nat.log2 x < 0 ===> False
-- `e < 0 ==> False` has precedence
#testOptimize [ "Log2LtNoNorm_9" ] ∀ (x : Nat), Nat.log2 x < 0 ===> False

-- ∀ (x : Nat), Nat.log2 x < Nat.log2 x ===> False
-- `e1 < e2 ==> False (if e1 =ₚₜᵣ e2)` has precedence
#testOptimize [ "Log2LtNoNorm_10" ] ∀ (x : Nat), Nat.log2 x < Nat.log2 x ===> False

-- ∀ (x : Nat), Nat.log2 x < Nat.log2 x + 1 ===> True
-- `e < N + e ==> True` has precedence
#testOptimize [ "Log2LtNoNorm_11" ] ∀ (x : Nat), Nat.log2 x < Nat.log2 x + 1 ===> True

-- ∀ (x : Nat), Nat.log2 (2 ^ x) < x + 1 ===> True
-- `Nat.log2 (2 ^ x)` is simplified to `x` beforehand, then `e < N + e ==> True`
#testOptimize [ "Log2LtNoNorm_12" ] ∀ (x : Nat), Nat.log2 (2 ^ x) < x + 1 ===> True

-- ∀ (x : Nat), x = 0 → Nat.log2 x < x ===> ∀ (x : Nat), ¬ (0 = x)
-- `x` is substituted by `0` from the hypothesis: `Nat.log2 0 < 0 ==> False`, then `0 = x → False ==> ¬ (0 = x)`
#testOptimize [ "Log2LtNoNorm_13" ] (norm-result: 1)
  ∀ (x : Nat), x = 0 → Nat.log2 x < x ===> ∀ (x : Nat), ¬ 0 = x

end Test.OptimizeNatLog2LT
