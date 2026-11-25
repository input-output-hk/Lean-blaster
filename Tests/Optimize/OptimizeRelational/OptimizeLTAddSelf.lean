import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLTAddSelf

/-! ## Test objectives to validate the simplification rules on `LT.lt` comparing an operand
    with a sum containing that same operand (see `natRelLeftReduce?`, `natRelRightReduce?`,
    `intRelLeftReduce?` and `intRelRightReduce?` in `optimizeLT`):
      - a + b < a | b + a < a ==> False (if Type(a) = Nat)
      - N + e < e ==> False (if N > 0 ∧ Type(e) = Int)
      - N + e < e ==> True (if N < 0 ∧ Type(e) = Int)
      - a + b < a | b + a < a ==> False (if Type(a) = Int ∧ geqZeroIntInHyps b)
      - a + b < a | b + a < a ==> True (if Type(a) = Int ∧ ltZeroIntInHyps b)
      - e < N + e ==> True (if N > 0 ∧ Type(N) ∈ [Nat, Int])
      - e < N + e ==> False (if N < 0 ∧ Type(N) = Int)
      - a < a + b | a < b + a ==> False (if Type(a) = Nat ∧ eqZeroNatInHyps b)
      - a < a + b | a < b + a ==> True (if Type(a) = Nat ∧ gtZeroNatInHyps b)
      - a < a + b | a < b + a ==> False (if Type(a) = Int ∧ leqZeroIntInHyps b)
      - a < a + b | a < b + a ==> True (if Type(a) = Int ∧ gtZeroIntInHyps b)

    NOTE: the hypotheses are introduced with implications; a conclusion simplified to `False`
    therefore yields the negation of the hypothesis, e.g., `0 ≤ y → False ==> y < 0`.
-/

/-! Test cases for simplification rule `a + b < a | b + a < a ==> False (if Type(a) = Nat)`. -/

-- ∀ (x y : Nat), x + y < x ===> False
#testOptimize [ "NatAddLeft_1" ] ∀ (x y : Nat), x + y < x ===> False

-- ∀ (x y : Nat), y + x < x ===> False
#testOptimize [ "NatAddLeft_2" ] ∀ (x y : Nat), y + x < x ===> False

-- ∀ (x : Nat), 3 + x < x ===> False
#testOptimize [ "NatAddLeft_3" ] ∀ (x : Nat), 3 + x < x ===> False

-- ∀ (x y z : Nat), (x + y) + z < x + y ===> False
#testOptimize [ "NatAddLeft_4" ] ∀ (x y z : Nat), (x + y) + z < x + y ===> False


/-! Test cases for simplification rules on `e < N + e` and `a < a + b` with `Type(a) = Nat`. -/

-- ∀ (x : Nat), x < 3 + x ===> True
#testOptimize [ "NatAddRight_1" ] ∀ (x : Nat), x < 3 + x ===> True

-- ∀ (x : Nat), x < x + 1 ===> True
#testOptimize [ "NatAddRight_2" ] ∀ (x : Nat), x < x + 1 ===> True

-- ∀ (x : Nat), x < 0 + x ===> False
-- `0 + x` is simplified to `x` beforehand, i.e., `x < x ==> False`
#testOptimize [ "NatAddRight_3" ] ∀ (x : Nat), x < 0 + x ===> False

-- ∀ (x y : Nat), 0 = y → x < x + y ===> ∀ (y : Nat), 0 < y
-- `eqZeroNatInHyps y` holds: the conclusion is `False`, and `0 = y → False ==> 0 < y`
#testOptimize [ "NatAddRight_4" ] (norm-result: 1) ∀ (x y : Nat), 0 = y → x < x + y ===> ∀ (y : Nat), 0 < y

-- ∀ (x y : Nat), y = 0 → x < y + x ===> ∀ (y : Nat), 0 < y
#testOptimize [ "NatAddRight_5" ] (norm-result: 1) ∀ (x y : Nat), y = 0 → x < y + x ===> ∀ (y : Nat), 0 < y

-- ∀ (x y : Nat), 0 < y → x < x + y ===> True
-- `gtZeroNatInHyps y` holds
#testOptimize [ "NatAddRight_6" ] ∀ (x y : Nat), 0 < y → x < x + y ===> True

-- ∀ (x y : Nat), 0 < y → x < y + x ===> True
#testOptimize [ "NatAddRight_7" ] ∀ (x y : Nat), 0 < y → x < y + x ===> True

-- ∀ (x y z : Nat), 0 < z → x + y < (x + y) + z ===> True
#testOptimize [ "NatAddRight_8" ] ∀ (x y z : Nat), 0 < z → x + y < (x + y) + z ===> True


/-! Test cases for simplification rules on `N + e < e` and `a + b < a` with `Type(a) = Int`. -/

-- ∀ (x : Int), 3 + x < x ===> False
#testOptimize [ "IntAddLeft_1" ] ∀ (x : Int), 3 + x < x ===> False

-- ∀ (x : Int), x + 3 < x ===> False
#testOptimize [ "IntAddLeft_2" ] ∀ (x : Int), x + 3 < x ===> False

-- ∀ (x : Int), -3 + x < x ===> True
#testOptimize [ "IntAddLeft_3" ] ∀ (x : Int), -3 + x < x ===> True

-- ∀ (x : Int), x + (-3) < x ===> True
#testOptimize [ "IntAddLeft_4" ] ∀ (x : Int), x + (-3) < x ===> True

-- ∀ (x y : Int), 0 ≤ y → x + y < x ===> ∀ (y : Int), y < 0
-- `geqZeroIntInHyps y` holds (`0 ≤ y` is normalized to `¬ (y < 0)`): the conclusion is `False`
#testOptimize [ "IntAddLeft_5" ] (norm-result: 1) ∀ (x y : Int), 0 ≤ y → x + y < x ===> ∀ (y : Int), y < Int.ofNat 0

-- ∀ (x y : Int), 0 ≤ y → y + x < x ===> ∀ (y : Int), y < 0
#testOptimize [ "IntAddLeft_6" ] (norm-result: 1) ∀ (x y : Int), 0 ≤ y → y + x < x ===> ∀ (y : Int), y < Int.ofNat 0

-- ∀ (x y : Int), y < 0 → x + y < x ===> True
-- `ltZeroIntInHyps y` holds
#testOptimize [ "IntAddLeft_7" ] ∀ (x y : Int), y < 0 → x + y < x ===> True

-- ∀ (x y : Int), y < 0 → y + x < x ===> True
#testOptimize [ "IntAddLeft_8" ] ∀ (x y : Int), y < 0 → y + x < x ===> True


/-! Test cases for simplification rules on `e < N + e` and `a < a + b` with `Type(a) = Int`. -/

-- ∀ (x : Int), x < 3 + x ===> True
#testOptimize [ "IntAddRight_1" ] ∀ (x : Int), x < 3 + x ===> True

-- ∀ (x : Int), x < x + 3 ===> True
#testOptimize [ "IntAddRight_2" ] ∀ (x : Int), x < x + 3 ===> True

-- ∀ (x : Int), x < -3 + x ===> False
#testOptimize [ "IntAddRight_3" ] ∀ (x : Int), x < -3 + x ===> False

-- ∀ (x : Int), x < x + (-3) ===> False
#testOptimize [ "IntAddRight_4" ] ∀ (x : Int), x < x + (-3) ===> False

-- ∀ (x y : Int), y ≤ 0 → x < x + y ===> ∀ (y : Int), 0 < y
-- `leqZeroIntInHyps y` holds (`y ≤ 0` is normalized to `¬ (0 < y)`): the conclusion is `False`
#testOptimize [ "IntAddRight_5" ] (norm-result: 1) ∀ (x y : Int), y ≤ 0 → x < x + y ===> ∀ (y : Int), Int.ofNat 0 < y

-- ∀ (x y : Int), y ≤ 0 → x < y + x ===> ∀ (y : Int), 0 < y
#testOptimize [ "IntAddRight_6" ] (norm-result: 1) ∀ (x y : Int), y ≤ 0 → x < y + x ===> ∀ (y : Int), Int.ofNat 0 < y

-- ∀ (x y : Int), 0 < y → x < x + y ===> True
-- `gtZeroIntInHyps y` holds
#testOptimize [ "IntAddRight_7" ] ∀ (x y : Int), 0 < y → x < x + y ===> True

-- ∀ (x y : Int), 0 < y → x < y + x ===> True
#testOptimize [ "IntAddRight_8" ] ∀ (x y : Int), 0 < y → x < y + x ===> True


/-! Test cases to ensure that the simplification rules are not applied without the required hypotheses. -/

-- ∀ (x y : Nat), x < x + y ===> ∀ (x y : Nat), x < x + y
#testOptimize [ "AddSelfNoNorm_1" ] ∀ (x y : Nat), x < x + y ===> ∀ (x y : Nat), x < Nat.add x y

-- ∀ (x y : Int), x + y < x ===> ∀ (x y : Int), x + y < x
#testOptimize [ "AddSelfNoNorm_2" ] ∀ (x y : Int), x + y < x ===> ∀ (x y : Int), Int.add x y < x

-- ∀ (x y : Int), x < x + y ===> ∀ (x y : Int), x < x + y
#testOptimize [ "AddSelfNoNorm_3" ] ∀ (x y : Int), x < x + y ===> ∀ (x y : Int), x < Int.add x y

-- ∀ (x y : Int), y ≤ 0 → x + y < x ===> ∀ (x y : Int), ¬ (0 < y) → x + y < x
-- `y ≤ 0` is neither `geqZeroIntInHyps y` nor `ltZeroIntInHyps y`
#testOptimize [ "AddSelfNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Int), y ≤ 0 → x + y < x ===> ∀ (x y : Int), ¬ (Int.ofNat 0 < y) → Int.add x y < x

-- ∀ (x y : Int), 0 ≤ y → x < x + y ===> ∀ (x y : Int), ¬ (y < 0) → x < x + y
-- `0 ≤ y` is neither `leqZeroIntInHyps y` nor `gtZeroIntInHyps y`
#testOptimize [ "AddSelfNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Int), 0 ≤ y → x < x + y ===> ∀ (x y : Int), ¬ (y < Int.ofNat 0) → x < Int.add x y

-- ∀ (x y z : Nat), 0 < z → x < y + z ===> ∀ (x y z : Nat), 0 < z → x < y + z
-- the left operand does not occur in the sum
#testOptimize [ "AddSelfNoNorm_6" ] (norm-result: 1)
  ∀ (x y z : Nat), 0 < z → x < y + z ===> ∀ (x y z : Nat), 0 < z → x < Nat.add y z

end Test.OptimizeLTAddSelf
