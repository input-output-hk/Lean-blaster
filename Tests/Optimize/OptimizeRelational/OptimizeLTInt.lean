import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLTInt

/-! ## Test objectives to validate the `Int` specific normalization rules on `LT.lt` (see `optimizeLT`):
      - 0 < -e ==> e < 0 (if Type(e) = Int)
      - Int.neg e1 < Int.neg e2 ==> e2 < e1
      - Int.ofNat e1 < Int.ofNat e2 ==> e1 < e2

    The rules trigger a restart so that the resulting `LT.lt` expression is normalized in turn.
-/

/-! Test cases for normalization rule `0 < -e ==> e < 0 (if Type(e) = Int)`. -/

-- ∀ (x : Int), 0 < -x ===> ∀ (x : Int), x < 0
#testOptimize [ "LTZeroNeg_1" ] (norm-result: 1) ∀ (x : Int), 0 < -x ===> ∀ (x : Int), x < Int.ofNat 0

-- ∀ (x y : Int), 0 < -(x * y) ===> ∀ (x y : Int), x * y < 0
#testOptimize [ "LTZeroNeg_2" ] (norm-result: 1)
  ∀ (x y : Int), 0 < -(x * y) ===> ∀ (x y : Int), Int.mul x y < Int.ofNat 0

-- ∀ (x : Int), 0 < -(3 + x) ===> ∀ (x : Int), x < -3
-- restart: `3 + x < 0` is reduced to `x < 0 - 3` (see rule `N1 + a < N2 ==> a < N2 "-" N1`)
#testOptimize [ "LTZeroNeg_3" ] (norm-result: 1) ∀ (x : Int), 0 < -(3 + x) ===> ∀ (x : Int), x < Int.negSucc 2

-- ∀ (x : Int), 0 < -(x + 1) ===> ∀ (x : Int), x < -1
#testOptimize [ "LTZeroNeg_4" ] (norm-result: 1) ∀ (x : Int), 0 < -(x + 1) ===> ∀ (x : Int), x < Int.negSucc 0

-- ∀ (x : Int), 0 < -(-x) ===> ∀ (x : Int), 0 < x
-- `-(-x)` is simplified to `x` beforehand (the rule is not applied)
#testOptimize [ "LTZeroNeg_5" ] (norm-result: 1) ∀ (x : Int), 0 < -(-x) ===> ∀ (x : Int), Int.ofNat 0 < x

-- (0 : Int) < -(-5) ===> True
-- `-(-5)` is folded to the literal `5` beforehand
#testOptimize [ "LTZeroNeg_6" ] (0 : Int) < -(-5) ===> True


/-! Test cases for normalization rule `Int.neg e1 < Int.neg e2 ==> e2 < e1`. -/

-- ∀ (x y : Int), -x < -y ===> ∀ (x y : Int), y < x
#testOptimize [ "LTNegNeg_1" ] ∀ (x y : Int), -x < -y ===> ∀ (x y : Int), y < x

-- ∀ (x : Int), -x < -(x + 1) ===> False
-- restart: `1 + x < x` is simplified to `False` (see rule `N + e < e ==> False (if N > 0)`)
#testOptimize [ "LTNegNeg_2" ] ∀ (x : Int), -x < -(x + 1) ===> False

-- ∀ (x : Int), -(x + 1) < -x ===> True
-- restart: `x < 1 + x` is simplified to `True` (see rule `e < N + e ==> True (if N > 0)`)
#testOptimize [ "LTNegNeg_3" ] ∀ (x : Int), -(x + 1) < -x ===> True

-- ∀ (x y : Int), -(x + y) < -x ===> ∀ (x y : Int), x < x + y
#testOptimize [ "LTNegNeg_4" ] ∀ (x y : Int), -(x + y) < -x ===> ∀ (x y : Int), x < Int.add x y

-- ∀ (x y : Int), (-x < -y) = (y < x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "LTNegNeg_5" ] ∀ (x y : Int), (-x < -y) = (y < x) ===> True


/-! Test cases for normalization rule `Int.ofNat e1 < Int.ofNat e2 ==> e1 < e2`. -/

-- ∀ (x y : Nat), Int.ofNat x < Int.ofNat y ===> ∀ (x y : Nat), x < y
#testOptimize [ "LTOfNat_1" ] ∀ (x y : Nat), Int.ofNat x < Int.ofNat y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), Int.ofNat (x + y) < Int.ofNat x ===> False
-- restart: `x + y < x` is simplified to `False` on `Nat` (see rule `a + b < a ==> False`)
#testOptimize [ "LTOfNat_2" ] ∀ (x y : Nat), Int.ofNat (x + y) < Int.ofNat x ===> False

-- ∀ (x : Nat), Int.ofNat x < Int.ofNat (x + 3) ===> True
-- restart: `x < 3 + x` is simplified to `True` on `Nat`
#testOptimize [ "LTOfNat_3" ] ∀ (x : Nat), Int.ofNat x < Int.ofNat (x + 3) ===> True

-- ∀ (x : Nat), Int.ofNat x < Int.ofNat 1 ===> ∀ (x : Nat), 0 = x
-- restart: `x < 1` is normalized to `0 = x` on `Nat`
#testOptimize [ "LTOfNat_4" ] (norm-result: 1) ∀ (x : Nat), Int.ofNat x < Int.ofNat 1 ===> ∀ (x : Nat), 0 = x

-- ∀ (x y : Nat), (Int.ofNat x < Int.ofNat y) = (x < y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "LTOfNat_5" ] ∀ (x y : Nat), (Int.ofNat x < Int.ofNat y) = (x < y) ===> True


/-! Test cases to ensure that the `Int` normalization rules are not wrongly applied. -/

-- ∀ (x : Int), 1 < -x ===> ∀ (x : Int), 1 < -x
-- rule `0 < -e ==> e < 0` requires the left operand to be `0`
#testOptimize [ "LTIntNoNorm_1" ] (norm-result: 1) ∀ (x : Int), 1 < -x ===> ∀ (x : Int), Int.ofNat 1 < Int.neg x

-- ∀ (x : Int), 0 < x ===> ∀ (x : Int), 0 < x
#testOptimize [ "LTIntNoNorm_2" ] (norm-result: 1) ∀ (x : Int), 0 < x ===> ∀ (x : Int), Int.ofNat 0 < x

-- ∀ (x : Int), -x < 0 ===> ∀ (x : Int), -x < 0
-- rule `0 < -e ==> e < 0` is only applied when the negation is the right operand
#testOptimize [ "LTIntNoNorm_3" ] (norm-result: 1) ∀ (x : Int), -x < 0 ===> ∀ (x : Int), Int.neg x < Int.ofNat 0

-- ∀ (x y : Int), -x < y ===> ∀ (x y : Int), -x < y
-- rule `Int.neg e1 < Int.neg e2 ==> e2 < e1` requires both operands to be negations
#testOptimize [ "LTIntNoNorm_4" ] ∀ (x y : Int), -x < y ===> ∀ (x y : Int), Int.neg x < y

-- ∀ (x y : Int), x < -y ===> ∀ (x y : Int), x < -y
#testOptimize [ "LTIntNoNorm_5" ] ∀ (x y : Int), x < -y ===> ∀ (x y : Int), x < Int.neg y

-- ∀ (x : Nat) (y : Int), Int.ofNat x < y ===> ∀ (x : Nat) (y : Int), Int.ofNat x < y
-- rule `Int.ofNat e1 < Int.ofNat e2 ==> e1 < e2` requires both operands to be `Int.ofNat` applications
#testOptimize [ "LTIntNoNorm_6" ] ∀ (x : Nat) (y : Int), Int.ofNat x < y ===> ∀ (x : Nat) (y : Int), Int.ofNat x < y

-- ∀ (x : Nat) (y : Int), y < Int.ofNat x ===> ∀ (x : Nat) (y : Int), y < Int.ofNat x
#testOptimize [ "LTIntNoNorm_7" ] ∀ (x : Nat) (y : Int), y < Int.ofNat x ===> ∀ (x : Nat) (y : Int), y < Int.ofNat x

end Test.OptimizeLTInt
