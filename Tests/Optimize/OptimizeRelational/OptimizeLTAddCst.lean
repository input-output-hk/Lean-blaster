import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLTAddCst

/-! ## Test objectives to validate the normalization rules on `LT.lt` moving literal summands from
    one side to the other (see `addNatLeftLtReduce?`, `addNatRightLtReduce?`, `addIntLeftLtReduce?`,
    `addIntRightLtReduce?`, `addNatBothReduce?`, `addIntBothReduce?`, `natLtNorm?` and `intLtNorm?`
    in `optimizeLT`):
      - N1 + a < N2 ==> False (if Type(a) = Nat ∧ N2 ≤ N1)
      - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Nat ∧ N2 > N1)
      - N1 + a < N2 ==> a < N2 "-" N1 (if Type(a) = Int)
      - N1 < N2 + a ==> True (if Type(a) = Nat ∧ N1 < N2)
      - N1 < N2 + a ==> N1 "-" N2 < a (if Type(a) = Nat ∧ N1 ≥ N2)
      - N1 < N2 + a ==> N1 "-" N2 < a (if Type(a) = Int)
      - N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])
      - a < 1 + b ==> ¬ (b < a) (if Type(a) ∈ [Nat, Int])

    The rules producing a new `LT.lt` expression trigger a restart so that it is normalized in turn.
    NOTE: literal summands are normalized to the left operand of the sum, i.e., `a + N` is `N + a`.
-/

/-! Test cases for rules `N1 + a < N2` with `Type(a) = Nat`. -/

-- ∀ (x : Nat), 5 + x < 3 ===> False
#testOptimize [ "NatAddCstLeft_1" ] ∀ (x : Nat), 5 + x < 3 ===> False

-- ∀ (x : Nat), 5 + x < 5 ===> False
#testOptimize [ "NatAddCstLeft_2" ] ∀ (x : Nat), 5 + x < 5 ===> False

-- ∀ (x : Nat), x + 5 < 3 ===> False
#testOptimize [ "NatAddCstLeft_3" ] ∀ (x : Nat), x + 5 < 3 ===> False

-- ∀ (x : Nat), 3 + x < 5 ===> ∀ (x : Nat), x < 2
#testOptimize [ "NatAddCstLeft_4" ] (norm-result: 1) ∀ (x : Nat), 3 + x < 5 ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), x + 3 < 5 ===> ∀ (x : Nat), x < 2
#testOptimize [ "NatAddCstLeft_5" ] (norm-result: 1) ∀ (x : Nat), x + 3 < 5 ===> ∀ (x : Nat), x < 2

-- ∀ (x : Nat), 4 + x < 5 ===> ∀ (x : Nat), 0 = x
-- restart: `x < 1` is normalized to `0 = x`
#testOptimize [ "NatAddCstLeft_6" ] (norm-result: 1) ∀ (x : Nat), 4 + x < 5 ===> ∀ (x : Nat), 0 = x

-- ∀ (x y : Nat), 3 + (x + y) < 5 ===> ∀ (x y : Nat), x + y < 2
#testOptimize [ "NatAddCstLeft_7" ] (norm-result: 1) ∀ (x y : Nat), 3 + (x + y) < 5 ===> ∀ (x y : Nat), Nat.add x y < 2


/-! Test cases for rules `N1 < N2 + a` with `Type(a) = Nat`. -/

-- ∀ (x : Nat), 3 < 5 + x ===> True
#testOptimize [ "NatAddCstRight_1" ] ∀ (x : Nat), 3 < 5 + x ===> True

-- ∀ (x : Nat), 3 < x + 5 ===> True
#testOptimize [ "NatAddCstRight_2" ] ∀ (x : Nat), 3 < x + 5 ===> True

-- ∀ (x : Nat), 5 < 3 + x ===> ∀ (x : Nat), 2 < x
#testOptimize [ "NatAddCstRight_3" ] (norm-result: 1) ∀ (x : Nat), 5 < 3 + x ===> ∀ (x : Nat), 2 < x

-- ∀ (x : Nat), 5 < 5 + x ===> ∀ (x : Nat), 0 < x
#testOptimize [ "NatAddCstRight_4" ] (norm-result: 1) ∀ (x : Nat), 5 < 5 + x ===> ∀ (x : Nat), 0 < x

-- ∀ (x : Nat), 5 < x + 3 ===> ∀ (x : Nat), 2 < x
#testOptimize [ "NatAddCstRight_5" ] (norm-result: 1) ∀ (x : Nat), 5 < x + 3 ===> ∀ (x : Nat), 2 < x

-- ∀ (x : Nat), 0 < 5 + x ===> True
#testOptimize [ "NatAddCstRight_6" ] ∀ (x : Nat), 0 < 5 + x ===> True


/-! Test cases for rules `N1 + a < N2` and `N1 < N2 + a` with `Type(a) = Int`. -/

-- ∀ (x : Int), 5 + x < 3 ===> ∀ (x : Int), x < -2
#testOptimize [ "IntAddCstLeft_1" ] (norm-result: 1) ∀ (x : Int), 5 + x < 3 ===> ∀ (x : Int), x < Int.negSucc 1

-- ∀ (x : Int), 5 + x < 5 ===> ∀ (x : Int), x < 0
#testOptimize [ "IntAddCstLeft_2" ] (norm-result: 1) ∀ (x : Int), 5 + x < 5 ===> ∀ (x : Int), x < Int.ofNat 0

-- ∀ (x : Int), x + 3 < 10 ===> ∀ (x : Int), x < 7
#testOptimize [ "IntAddCstLeft_3" ] (norm-result: 1) ∀ (x : Int), x + 3 < 10 ===> ∀ (x : Int), x < Int.ofNat 7

-- ∀ (x : Int), -5 + x < -3 ===> ∀ (x : Int), x < 2
#testOptimize [ "IntAddCstLeft_4" ] (norm-result: 1) ∀ (x : Int), -5 + x < -3 ===> ∀ (x : Int), x < Int.ofNat 2

-- ∀ (x : Int), x + 3 < -4 ===> ∀ (x : Int), x < -7
#testOptimize [ "IntAddCstLeft_5" ] (norm-result: 1) ∀ (x : Int), x + 3 < -4 ===> ∀ (x : Int), x < Int.negSucc 6

-- ∀ (x : Int), 3 < 5 + x ===> ∀ (x : Int), -2 < x
#testOptimize [ "IntAddCstRight_1" ] (norm-result: 1) ∀ (x : Int), 3 < 5 + x ===> ∀ (x : Int), Int.negSucc 1 < x

-- ∀ (x : Int), 5 < 5 + x ===> ∀ (x : Int), 0 < x
#testOptimize [ "IntAddCstRight_2" ] (norm-result: 1) ∀ (x : Int), 5 < 5 + x ===> ∀ (x : Int), Int.ofNat 0 < x

-- ∀ (x : Int), 5 < 3 + x ===> ∀ (x : Int), 2 < x
#testOptimize [ "IntAddCstRight_3" ] (norm-result: 1) ∀ (x : Int), 5 < 3 + x ===> ∀ (x : Int), Int.ofNat 2 < x

-- ∀ (x : Int), -3 < -5 + x ===> ∀ (x : Int), 2 < x
#testOptimize [ "IntAddCstRight_4" ] (norm-result: 1) ∀ (x : Int), -3 < -5 + x ===> ∀ (x : Int), Int.ofNat 2 < x

-- ∀ (x : Int), 0 < -(3 + x) ===> ∀ (x : Int), x < -3
-- restart: `0 < -e ==> e < 0` first yields `3 + x < 0`
#testOptimize [ "IntAddCstRight_5" ] (norm-result: 1) ∀ (x : Int), 0 < -(3 + x) ===> ∀ (x : Int), x < Int.negSucc 2


/-! Test cases for rule `N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`. -/

-- ∀ (x y : Nat), 5 + x < 3 + y ===> ∀ (x y : Nat), 2 + x < y
#testOptimize [ "NatAddCstBoth_1" ] (norm-result: 1) ∀ (x y : Nat), 5 + x < 3 + y ===> ∀ (x y : Nat), Nat.add 2 x < y

-- ∀ (x y : Nat), 3 + x < 5 + y ===> ∀ (x y : Nat), x < 2 + y
#testOptimize [ "NatAddCstBoth_2" ] (norm-result: 1) ∀ (x y : Nat), 3 + x < 5 + y ===> ∀ (x y : Nat), x < Nat.add 2 y

-- ∀ (x y : Nat), 3 + x < 3 + y ===> ∀ (x y : Nat), x < y
#testOptimize [ "NatAddCstBoth_3" ] ∀ (x y : Nat), 3 + x < 3 + y ===> ∀ (x y : Nat), x < y

-- ∀ (x y : Nat), x + 1 < y + 1 ===> ∀ (x y : Nat), x < y
#testOptimize [ "NatAddCstBoth_4" ] ∀ (x y : Nat), x + 1 < y + 1 ===> ∀ (x y : Nat), x < y

-- ∀ (x : Nat), 3 + x < 5 + x ===> True
-- restart: `x < 2 + x` is simplified to `True`
#testOptimize [ "NatAddCstBoth_5" ] ∀ (x : Nat), 3 + x < 5 + x ===> True

-- ∀ (x : Nat), 5 + x < 3 + x ===> False
-- restart: `2 + x < x` is simplified to `False`
#testOptimize [ "NatAddCstBoth_6" ] ∀ (x : Nat), 5 + x < 3 + x ===> False

-- ∀ (x y : Nat), 4 + x < 5 + y ===> ∀ (x y : Nat), ¬ (y < x)
-- restart: `x < 1 + y` is normalized to `¬ (y < x)`
#testOptimize [ "NatAddCstBoth_7" ] ∀ (x y : Nat), 4 + x < 5 + y ===> ∀ (x y : Nat), ¬ (y < x)

-- ∀ (x y : Int), 5 + x < 3 + y ===> ∀ (x y : Int), 2 + x < y
#testOptimize [ "IntAddCstBoth_1" ] (norm-result: 1)
  ∀ (x y : Int), 5 + x < 3 + y ===> ∀ (x y : Int), Int.add (Int.ofNat 2) x < y

-- ∀ (x y : Int), 3 + x < 5 + y ===> ∀ (x y : Int), x < 2 + y
#testOptimize [ "IntAddCstBoth_2" ] (norm-result: 1)
  ∀ (x y : Int), 3 + x < 5 + y ===> ∀ (x y : Int), x < Int.add (Int.ofNat 2) y

-- ∀ (x y : Int), -5 + x < 3 + y ===> ∀ (x y : Int), x < 8 + y
#testOptimize [ "IntAddCstBoth_3" ] (norm-result: 1)
  ∀ (x y : Int), -5 + x < 3 + y ===> ∀ (x y : Int), x < Int.add (Int.ofNat 8) y

-- ∀ (x y : Int), 3 + x < -5 + y ===> ∀ (x y : Int), 8 + x < y
#testOptimize [ "IntAddCstBoth_4" ] (norm-result: 1)
  ∀ (x y : Int), 3 + x < -5 + y ===> ∀ (x y : Int), Int.add (Int.ofNat 8) x < y

-- ∀ (x y : Int), -5 + x < -3 + y ===> ∀ (x y : Int), x < 2 + y
#testOptimize [ "IntAddCstBoth_5" ] (norm-result: 1)
  ∀ (x y : Int), -5 + x < -3 + y ===> ∀ (x y : Int), x < Int.add (Int.ofNat 2) y

-- ∀ (x y : Int), 3 + x < 3 + y ===> ∀ (x y : Int), x < y
#testOptimize [ "IntAddCstBoth_6" ] ∀ (x y : Int), 3 + x < 3 + y ===> ∀ (x y : Int), x < y

-- ∀ (x : Int), 3 + x < 5 + x ===> True
-- restart: `x < 2 + x` is simplified to `True`
#testOptimize [ "IntAddCstBoth_7" ] ∀ (x : Int), 3 + x < 5 + x ===> True

-- ∀ (x : Int), 5 + x < 3 + x ===> False
-- restart: `2 + x < x` is simplified to `False`
#testOptimize [ "IntAddCstBoth_8" ] ∀ (x : Int), 5 + x < 3 + x ===> False

-- ∀ (x y : Int), 4 + x < 5 + y ===> ∀ (x y : Int), ¬ (y < x)
-- restart: `x < 1 + y` is normalized to `¬ (y < x)`
#testOptimize [ "IntAddCstBoth_9" ] ∀ (x y : Int), 4 + x < 5 + y ===> ∀ (x y : Int), ¬ (y < x)


/-! Test cases for rule `a < 1 + b ==> ¬ (b < a)`. -/

-- ∀ (x y : Nat), x < 1 + y ===> ∀ (x y : Nat), ¬ (y < x)
#testOptimize [ "LTSucc_1" ] ∀ (x y : Nat), x < 1 + y ===> ∀ (x y : Nat), ¬ (y < x)

-- ∀ (x y : Nat), x < y + 1 ===> ∀ (x y : Nat), ¬ (y < x)
#testOptimize [ "LTSucc_2" ] ∀ (x y : Nat), x < y + 1 ===> ∀ (x y : Nat), ¬ (y < x)

-- ∀ (x y : Int), x < 1 + y ===> ∀ (x y : Int), ¬ (y < x)
#testOptimize [ "LTSucc_3" ] ∀ (x y : Int), x < 1 + y ===> ∀ (x y : Int), ¬ (y < x)

-- ∀ (x y : Int), x < y + 1 ===> ∀ (x y : Int), ¬ (y < x)
#testOptimize [ "LTSucc_4" ] ∀ (x y : Int), x < y + 1 ===> ∀ (x y : Int), ¬ (y < x)

-- ∀ (x y : Nat), x < 1 + (x + y) ===> True
-- restart: `¬ (x + y < x)` is simplified to `¬ False`
#testOptimize [ "LTSucc_5" ] ∀ (x y : Nat), x < 1 + (x + y) ===> True

-- ∀ (x y : Int), x < 1 + (x + y) ===> ∀ (x y : Int), ¬ (x + y < x)
-- restart: `x + y < x` is not simplified on `Int` without hypothesis on `y`
#testOptimize [ "LTSucc_6" ] ∀ (x y : Int), x < 1 + (x + y) ===> ∀ (x y : Int), ¬ (Int.add x y < x)

-- ∀ (x y : Nat), (x < 1 + y) = (x ≤ y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "LTSucc_7" ] ∀ (x y : Nat), (x < 1 + y) = (x ≤ y) ===> True


/-! Test cases to ensure that the normalization rules are not wrongly applied. -/

-- ∀ (x y : Nat), 3 + x < y ===> ∀ (x y : Nat), 3 + x < y
-- a literal on one side only requires a literal on the other side
#testOptimize [ "AddCstNoNorm_1" ] (norm-result: 1) ∀ (x y : Nat), 3 + x < y ===> ∀ (x y : Nat), Nat.add 3 x < y

-- ∀ (x y : Nat), x < 3 + y ===> ∀ (x y : Nat), x < 3 + y
#testOptimize [ "AddCstNoNorm_2" ] (norm-result: 1) ∀ (x y : Nat), x < 3 + y ===> ∀ (x y : Nat), x < Nat.add 3 y

-- ∀ (x y : Nat), 1 + x < y ===> ∀ (x y : Nat), 1 + x < y
-- rule `a < 1 + b ==> ¬ (b < a)` requires the successor on the right operand
#testOptimize [ "AddCstNoNorm_3" ] (norm-result: 1) ∀ (x y : Nat), 1 + x < y ===> ∀ (x y : Nat), Nat.add 1 x < y

-- ∀ (x y : Int), 3 + x < y ===> ∀ (x y : Int), 3 + x < y
#testOptimize [ "AddCstNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Int), 3 + x < y ===> ∀ (x y : Int), Int.add (Int.ofNat 3) x < y

-- ∀ (x y : Int), x < 2 + y ===> ∀ (x y : Int), x < 2 + y
#testOptimize [ "AddCstNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Int), x < 2 + y ===> ∀ (x y : Int), x < Int.add (Int.ofNat 2) y

-- ∀ (x y : Int), 1 + x < y ===> ∀ (x y : Int), 1 + x < y
#testOptimize [ "AddCstNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Int), 1 + x < y ===> ∀ (x y : Int), Int.add (Int.ofNat 1) x < y

-- ∀ (x y : Nat), x * 3 < y * 5 ===> ∀ (x y : Nat), x * 3 < y * 5
-- literal factors are not literal summands
#testOptimize [ "AddCstNoNorm_7" ] (norm-result: 1)
  ∀ (x y : Nat), x * 3 < y * 5 ===> ∀ (x y : Nat), Nat.mul 3 x < Nat.mul 5 y

end Test.OptimizeLTAddCst
