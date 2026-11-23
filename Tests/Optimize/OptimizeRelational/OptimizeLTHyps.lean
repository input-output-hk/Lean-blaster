import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLTHyps

/-! ## Test objectives to validate the simplification rules on `LT.lt` relying on the hypothesis
    context only (see `predCstLTInHyp`, `intZeroLtSum?` and `natZeroLtSumReduce?` in `optimizeLT`):
      - N < e ==> False (if ¬ (N - 1 < e) := _ ∈ hypothesisContext.hypothesisMap ∧ Type(e) ∈ [Nat, Int])
      - 0 < x + y ==> True (if Type(x) = Int ∧ geqZeroIntInHyps x ∧ gtZeroIntInHyps y)
      - 0 < x + y ==> True (if Type(x) = Int ∧ gtZeroIntInHyps x ∧ geqZeroIntInHyps y)
      - 0 < x + y ==> False (if Type(x) = Int ∧ ltZeroIntInHyps x ∧ leqZeroIntInHyps y)
      - 0 < x + y ==> False (if Type(x) = Int ∧ leqZeroIntInHyps x ∧ ltZeroIntInHyps y)
      - x + y < 0 ==> False (if Type(x) = Int ∧ geqZeroIntInHyps x ∧ gtZeroIntInHyps y)
      - x + y < 0 ==> False (if Type(x) = Int ∧ gtZeroIntInHyps x ∧ geqZeroIntInHyps y)
      - x + y < 0 ==> True (if Type(x) = Int ∧ ltZeroIntInHyps x ∧ leqZeroIntInHyps y)
      - x + y < 0 ==> True (if Type(x) = Int ∧ leqZeroIntInHyps x ∧ ltZeroIntInHyps y)
      - 0 < x + y ==> True (if Type(x) = Nat ∧ (nonZeroNatInHyps x ∨ nonZeroNatInHyps y))

    NOTE: the hypotheses are introduced with implications; a conclusion simplified to `False`
    therefore yields the negation of the hypotheses, e.g., `h1 → h2 → False ==> h1 → ¬ h2`.
    `x ≤ N` is normalized to `¬ (N < x)`, `0 ≤ x` to `¬ (x < 0)` and `x ≤ 0` to `¬ (0 < x)`.
-/

/-! Test cases for simplification rule `N < e ==> False (if ¬ (N - 1 < e) ∈ hypothesisMap)`. -/

-- ∀ (x : Nat), x ≤ 4 → 5 < x ===> ∀ (x : Nat), 4 < x
-- the conclusion is `False`, and `¬ (4 < x) → False ==> 4 < x`
#testOptimize [ "LTPredCst_1" ] (norm-result: 1) ∀ (x : Nat), x ≤ 4 → 5 < x ===> ∀ (x : Nat), 4 < x

-- ∀ (x : Nat), ¬ (0 < x) → 1 < x ===> ∀ (x : Nat), 0 < x
#testOptimize [ "LTPredCst_2" ] (norm-result: 1) ∀ (x : Nat), ¬ (0 < x) → 1 < x ===> ∀ (x : Nat), 0 < x

-- ∀ (x : Int), x ≤ 4 → 5 < x ===> ∀ (x : Int), 4 < x
#testOptimize [ "LTPredCst_3" ] (norm-result: 1) ∀ (x : Int), x ≤ 4 → 5 < x ===> ∀ (x : Int), Int.ofNat 4 < x

-- ∀ (x : Int), x ≤ -4 → -3 < x ===> ∀ (x : Int), -4 < x
#testOptimize [ "LTPredCst_4" ] (norm-result: 1) ∀ (x : Int), x ≤ -4 → -3 < x ===> ∀ (x : Int), Int.negSucc 3 < x

-- ∀ (x : Int), x ≤ -1 → 0 < x ===> ∀ (x : Int), -1 < x
#testOptimize [ "LTPredCst_5" ] (norm-result: 1) ∀ (x : Int), x ≤ -1 → 0 < x ===> ∀ (x : Int), Int.negSucc 0 < x

-- ∀ (x y : Nat), x + y ≤ 4 → 5 < x + y ===> ∀ (x y : Nat), 4 < x + y
#testOptimize [ "LTPredCst_6" ] (norm-result: 1)
  ∀ (x y : Nat), x + y ≤ 4 → 5 < x + y ===> ∀ (x y : Nat), 4 < Nat.add x y


/-! Test cases for simplification rules `0 < x + y` and `x + y < 0` with `Type(x) = Int`. -/

-- ∀ (x y : Int), 0 ≤ x → 0 < y → 0 < x + y ===> True
#testOptimize [ "IntZeroLtSum_1" ] ∀ (x y : Int), 0 ≤ x → 0 < y → 0 < x + y ===> True

-- ∀ (x y : Int), 0 < x → 0 ≤ y → 0 < x + y ===> True
#testOptimize [ "IntZeroLtSum_2" ] ∀ (x y : Int), 0 < x → 0 ≤ y → 0 < x + y ===> True

-- ∀ (x y : Int), 0 < y → 0 ≤ x → 0 < x + y ===> True
-- the order of the hypotheses is irrelevant
#testOptimize [ "IntZeroLtSum_3" ] ∀ (x y : Int), 0 < y → 0 ≤ x → 0 < x + y ===> True

-- ∀ (x y : Int), 0 < x → 0 < y → 0 < x + y ===> True
-- `0 < x` also satisfies `geqZeroIntInHyps x` through the derived facts
#testOptimize [ "IntZeroLtSum_4" ] ∀ (x y : Int), 0 < x → 0 < y → 0 < x + y ===> True

-- ∀ (x y : Int), x ≤ 0 → y < 0 → 0 < x + y ===> ∀ (x y : Int), ¬ (0 < x) → ¬ (y < 0)
-- the conclusion is `False`
#testOptimize [ "IntZeroLtSum_5" ] (norm-result: 1)
  ∀ (x y : Int), x ≤ 0 → y < 0 → 0 < x + y ===> ∀ (x y : Int), ¬ (Int.ofNat 0 < x) → ¬ (y < Int.ofNat 0)

-- ∀ (x y : Int), x < 0 → y ≤ 0 → 0 < x + y ===> ∀ (x y : Int), x < 0 → 0 < y
-- the conclusion is `False`, and `¬ (¬ (0 < y)) ==> 0 < y`
#testOptimize [ "IntZeroLtSum_6" ] (norm-result: 1)
  ∀ (x y : Int), x < 0 → y ≤ 0 → 0 < x + y ===> ∀ (x y : Int), x < Int.ofNat 0 → Int.ofNat 0 < y

-- ∀ (x y : Int), 0 ≤ x → 0 < y → x + y < 0 ===> ∀ (x y : Int), ¬ (x < 0) → ¬ (0 < y)
#testOptimize [ "IntSumLtZero_1" ] (norm-result: 1)
  ∀ (x y : Int), 0 ≤ x → 0 < y → x + y < 0 ===> ∀ (x y : Int), ¬ (x < Int.ofNat 0) → ¬ (Int.ofNat 0 < y)

-- ∀ (x y : Int), 0 < x → 0 ≤ y → x + y < 0 ===> ∀ (x y : Int), 0 < x → y < 0
#testOptimize [ "IntSumLtZero_2" ] (norm-result: 1)
  ∀ (x y : Int), 0 < x → 0 ≤ y → x + y < 0 ===> ∀ (x y : Int), Int.ofNat 0 < x → y < Int.ofNat 0

-- ∀ (x y : Int), x ≤ 0 → y < 0 → x + y < 0 ===> True
#testOptimize [ "IntSumLtZero_3" ] ∀ (x y : Int), x ≤ 0 → y < 0 → x + y < 0 ===> True

-- ∀ (x y : Int), x < 0 → y ≤ 0 → x + y < 0 ===> True
#testOptimize [ "IntSumLtZero_4" ] ∀ (x y : Int), x < 0 → y ≤ 0 → x + y < 0 ===> True

-- ∀ (x y : Int), y ≤ 0 → x < 0 → x + y < 0 ===> True
-- the order of the hypotheses is irrelevant
#testOptimize [ "IntSumLtZero_5" ] ∀ (x y : Int), y ≤ 0 → x < 0 → x + y < 0 ===> True


/-! Test cases for simplification rule `0 < x + y ==> True (if Type(x) = Nat ∧ (nonZeroNatInHyps x ∨ nonZeroNatInHyps y))`. -/

-- ∀ (x y : Nat), x ≠ 0 → 0 < x + y ===> True
-- `x ≠ 0` is normalized to `¬ (0 = x)`
#testOptimize [ "NatZeroLtSum_1" ] ∀ (x y : Nat), x ≠ 0 → 0 < x + y ===> True

-- ∀ (x y : Nat), ¬ (0 = y) → 0 < x + y ===> True
#testOptimize [ "NatZeroLtSum_2" ] ∀ (x y : Nat), ¬ (0 = y) → 0 < x + y ===> True

-- ∀ (x y : Nat), 0 < x → 0 < x + y ===> True
-- `0 < x` also satisfies `nonZeroNatInHyps x` through the derived facts
#testOptimize [ "NatZeroLtSum_3" ] ∀ (x y : Nat), 0 < x → 0 < x + y ===> True

-- ∀ (x y z : Nat), z ≠ 0 → 0 < x + (y + z) ===> True
-- the sum is normalized to `x + (y + z)` where `y + z` is not zero
#testOptimize [ "NatZeroLtSum_4" ] ∀ (x y z : Nat), ¬ (0 = y + z) → 0 < x + (y + z) ===> True


/-! Test cases to ensure that the hypothesis based rules are not applied without the required hypotheses. -/

-- ∀ (x : Nat), x ≤ 4 → 6 < x ===> ∀ (x : Nat), ¬ (4 < x) → 6 < x
-- `¬ (5 < x)` is not in the hypothesis map
#testOptimize [ "HypsNoNorm_1" ] (norm-result: 1) ∀ (x : Nat), x ≤ 4 → 6 < x ===> ∀ (x : Nat), ¬ (4 < x) → 6 < x

-- ∀ (x : Int), x ≤ 4 → 7 < x ===> ∀ (x : Int), ¬ (4 < x) → 7 < x
#testOptimize [ "HypsNoNorm_2" ] (norm-result: 1)
  ∀ (x : Int), x ≤ 4 → 7 < x ===> ∀ (x : Int), ¬ (Int.ofNat 4 < x) → Int.ofNat 7 < x

-- ∀ (x : Nat), 5 < x → x ≤ 4 ===> ∀ (x : Nat), 5 < x → ¬ (4 < x)
-- the hypothesis `5 < x` does not match `¬ (N - 1 < e)`
#testOptimize [ "HypsNoNorm_3" ] (norm-result: 1) ∀ (x : Nat), 5 < x → x ≤ 4 ===> ∀ (x : Nat), 5 < x → ¬ (4 < x)

-- ∀ (x : Nat), 5 < x ===> ∀ (x : Nat), 5 < x
#testOptimize [ "HypsNoNorm_4" ] (norm-result: 1) ∀ (x : Nat), 5 < x ===> ∀ (x : Nat), 5 < x

-- ∀ (x y : Int), 0 ≤ x → 0 ≤ y → 0 < x + y ===> ∀ (x y : Int), ¬ (x < 0) → ¬ (y < 0) → 0 < x + y
-- both summands may be zero
#testOptimize [ "HypsNoNorm_5" ] (norm-result: 1)
  ∀ (x y : Int), 0 ≤ x → 0 ≤ y → 0 < x + y ===>
  ∀ (x y : Int), ¬ (x < Int.ofNat 0) → ¬ (y < Int.ofNat 0) → Int.ofNat 0 < Int.add x y

-- ∀ (x y : Int), 0 < x + y ===> ∀ (x y : Int), 0 < x + y
#testOptimize [ "HypsNoNorm_6" ] (norm-result: 1)
  ∀ (x y : Int), 0 < x + y ===> ∀ (x y : Int), Int.ofNat 0 < Int.add x y

-- ∀ (x y : Int), x + y < 0 ===> ∀ (x y : Int), x + y < 0
#testOptimize [ "HypsNoNorm_7" ] (norm-result: 1)
  ∀ (x y : Int), x + y < 0 ===> ∀ (x y : Int), Int.add x y < Int.ofNat 0

-- ∀ (x y : Int), 0 ≤ x → 0 < y → 1 < x + y ===> ∀ (x y : Int), ¬ (x < 0) → 0 < y → 1 < x + y
-- the left operand must be `0`
#testOptimize [ "HypsNoNorm_8" ] (norm-result: 1)
  ∀ (x y : Int), 0 ≤ x → 0 < y → 1 < x + y ===>
  ∀ (x y : Int), ¬ (x < Int.ofNat 0) → Int.ofNat 0 < y → Int.ofNat 1 < Int.add x y

-- ∀ (x y : Nat), 0 < x + y ===> ∀ (x y : Nat), 0 < x + y
#testOptimize [ "HypsNoNorm_9" ] (norm-result: 1) ∀ (x y : Nat), 0 < x + y ===> ∀ (x y : Nat), 0 < Nat.add x y

-- ∀ (x y : Nat), 0 = x → 0 < x + y ===> ∀ (x y : Nat), 0 = x → 0 < y
-- the hypothesis substitutes `x` by `0` in the conclusion (the rule is not applicable)
#testOptimize [ "HypsNoNorm_10" ] (norm-result: 1) ∀ (x y : Nat), 0 = x → 0 < x + y ===> ∀ (x y : Nat), 0 = x → 0 < y

-- ∀ (y : Int), 0 < y → 0 < 3 + y ===> ∀ (y : Int), 0 < y → -3 < y
-- the literal summand is moved to the left operand first (see rule `N1 < N2 + a ==> N1 "-" N2 < a`)
#testOptimize [ "HypsNoNorm_11" ] (norm-result: 1)
  ∀ (y : Int), 0 < y → 0 < 3 + y ===> ∀ (y : Int), Int.ofNat 0 < y → Int.negSucc 2 < y

end Test.OptimizeLTHyps
