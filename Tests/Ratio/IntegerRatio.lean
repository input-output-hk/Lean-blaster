import Ratio.Ratio

open Ratio

namespace Tests.Ratio.IntegerRatio

/- IntegerAddRatioBasics -/

-- INTEGER_ADD_RATIO_CONSTANT_1: integerAddRatio(0, R_ZERO) = R_ZERO and eqRatio(...)
#blaster [ ((integerAddRatio 0 R_ZERO == R_ZERO) && eqRatio (integerAddRatio 0 R_ZERO) R_ZERO) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_2: integerAddRatio(0, R_ONE) = R_ONE and eqRatio(...)
#blaster [ ((integerAddRatio 0 R_ONE == R_ONE) && eqRatio (integerAddRatio 0 R_ONE) R_ONE) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_3: integerAddRatio(0, R_HALF) = R_HALF and eqRatio(...)
#blaster [ ((integerAddRatio 0 R_HALF == R_HALF) && eqRatio (integerAddRatio 0 R_HALF) R_HALF) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_4: eqRatio(integerAddRatio(10, ratio(5, 3)), ratio(35, 3))
#blaster [ (eqRatio (integerAddRatio 10 (ratio 5 3)) (ratio 35 3)) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_5: eqRatio(integerAddRatio(10, ratio(-5, 3)), ratio(25, 3))
#blaster [ (eqRatio (integerAddRatio 10 (ratio (-5) 3)) (ratio 25 3)) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_6: eqRatio(integerAddRatio(16, ratio(5, 13)), ratio(213, 13))
#blaster [ (eqRatio (integerAddRatio 16 (ratio 5 13)) (ratio 213 13)) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_7: eqRatio(integerAddRatio(-16, ratio(5, 13)), ratio(-203, 13))
#blaster [ (eqRatio (integerAddRatio (-16) (ratio 5 13)) (ratio (-203) 13)) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_8: eqRatio(integerAddRatio(16, ratio(-5, 13)), ratio(203, 13))
#blaster [ (eqRatio (integerAddRatio 16 (ratio (-5) 13)) (ratio 203 13)) = true ]

-- INTEGER_ADD_RATIO_CONSTANT_9: eqRatio(integerAddRatio(16, ratio(5, -13)), ratio(203, 13))
#blaster [ (eqRatio (integerAddRatio 16 (ratio 5 (-13))) (ratio 203 13)) = true ]

/- IntegerAddRatioValidity -/

-- INTEGER_ADD_NOT_VALIDRATIO: ~isValidRatio(a) => ~isValidRatio(integerAddRatio(i, a))
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (integerAddRatio i a)) = false ]

-- INTEGER_ADD_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => isValidAndNormalizedRatio(integerAddRatio(i, a))
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (isValidAndNormalizedRatio (integerAddRatio i a)) = true ]

-- INTEGER_ADD_CORRECTNESS: isValidRatio(a) => integerAddRatio(i, a) = addRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerAddRatio i a == addRatio (fromInteger i) a) = true ]

/- IntegerSubRatioBasics -/

-- INTEGER_SUB_RATIO_CONSTANT_1: integerSubRatio(0, R_ZERO) = R_ZERO and eqRatio(...)
#blaster [ ((integerSubRatio 0 R_ZERO == R_ZERO) && eqRatio (integerSubRatio 0 R_ZERO) R_ZERO) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_2: integerSubRatio(0, R_ONE) = negate(R_ONE) and eqRatio(...)
#blaster [ ((integerSubRatio 0 R_ONE == negate R_ONE) && eqRatio (integerSubRatio 0 R_ONE) (negate R_ONE)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_3: integerSubRatio(0, R_HALF) = negate(R_HALF) and eqRatio(...)
#blaster [ ((integerSubRatio 0 R_HALF == negate R_HALF) && eqRatio (integerSubRatio 0 R_HALF) (negate R_HALF)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_4: eqRatio(integerSubRatio(10, ratio(5, 3)), ratio(25, 3))
#blaster [ (eqRatio (integerSubRatio 10 (ratio 5 3)) (ratio 25 3)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_5: eqRatio(integerSubRatio(10, ratio(-5, 3)), ratio(35, 3))
#blaster [ (eqRatio (integerSubRatio 10 (ratio (-5) 3)) (ratio 35 3)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_6: eqRatio(integerSubRatio(16, ratio(5, 13)), ratio(203, 13))
#blaster [ (eqRatio (integerSubRatio 16 (ratio 5 13)) (ratio 203 13)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_7: eqRatio(integerSubRatio(-16, ratio(5, 13)), ratio(-213, 13))
#blaster [ (eqRatio (integerSubRatio (-16) (ratio 5 13)) (ratio (-213) 13)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_8: eqRatio(integerSubRatio(16, ratio(-5, 13)), ratio(213, 13))
#blaster [ (eqRatio (integerSubRatio 16 (ratio (-5) 13)) (ratio 213 13)) = true ]

-- INTEGER_SUB_RATIO_CONSTANT_9: eqRatio(integerSubRatio(16, ratio(5, -13)), ratio(213, 13))
#blaster [ (eqRatio (integerSubRatio 16 (ratio 5 (-13))) (ratio 213 13)) = true ]

/- IntegerSubRatioValidity -/

-- INTEGER_SUB_NOT_VALIDRATIO: ~isValidRatio(a) => ~isValidRatio(integerSubRatio(i, a))
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (integerSubRatio i a)) = false ]

-- INTEGER_SUB_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => isValidAndNormalizedRatio(integerSubRatio(i, a))
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (isValidAndNormalizedRatio (integerSubRatio i a)) = true ]

-- INTEGER_SUB_CORRECTNESS: isValidRatio(a) => integerSubRatio(i, a) = subRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerSubRatio i a == subRatio (fromInteger i) a) = true ]

/- IntegerMulRatioBasics -/

-- INTEGER_MUL_RATIO_CONSTANT_1: integerMulRatio(10, R_ONE) = fromInteger(10) and eqRatio(...)
#blaster [ ((integerMulRatio 10 R_ONE == fromInteger 10) && eqRatio (integerMulRatio 10 R_ONE) (fromInteger 10)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_2: eqRatio(integerMulRatio(10, R_HALF), fromInteger(5))
#blaster [ (eqRatio (integerMulRatio 10 R_HALF) (fromInteger 5)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_3: eqRatio(integerMulRatio(10, ratio(5, 3)), ratio(50, 3))
#blaster [ (eqRatio (integerMulRatio 10 (ratio 5 3)) (ratio 50 3)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_4: eqRatio(integerMulRatio(10, ratio(-5, 3)), ratio(-50, 3))
#blaster [ (eqRatio (integerMulRatio 10 (ratio (-5) 3)) (ratio (-50) 3)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_5: eqRatio(integerMulRatio(16, ratio(5, 13)), ratio(80, 13))
#blaster [ (eqRatio (integerMulRatio 16 (ratio 5 13)) (ratio 80 13)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_6: eqRatio(integerMulRatio(-16, ratio(5, 13)), ratio(-80, 13))
#blaster [ (eqRatio (integerMulRatio (-16) (ratio 5 13)) (ratio (-80) 13)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_7: eqRatio(integerMulRatio(16, ratio(-5, 13)), ratio(-80, 13))
#blaster [ (eqRatio (integerMulRatio 16 (ratio (-5) 13)) (ratio (-80) 13)) = true ]

-- INTEGER_MUL_RATIO_CONSTANT_8: eqRatio(integerMulRatio(16, ratio(5, -13)), ratio(-80, 13))
#blaster [ (eqRatio (integerMulRatio 16 (ratio 5 (-13))) (ratio (-80) 13)) = true ]

/- IntegerMulRatioValidity -/

-- INTEGER_MUL_NOT_VALIDRATIO: ~isValidRatio(a) => ~isValidRatio(integerMulRatio(i, a))
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (integerMulRatio i a)) = false ]

-- INTEGER_MUL_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => isValidAndNormalizedRatio(integerMulRatio(i, a))
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (isValidAndNormalizedRatio (integerMulRatio i a)) = true ]

-- INTEGER_MUL_CORRECTNESS: isValidRatio(a) => integerMulRatio(i, a) = mulRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerMulRatio i a == mulRatio (fromInteger i) a) = true ]

/- IntegerLtRatioBasics -/

-- INTEGER_LT_RATIO_CONSTANT_1: not(integerLtRatio(0, R_ZERO))
#blaster [ (integerLtRatio 0 R_ZERO) = false ]

-- INTEGER_LT_RATIO_CONSTANT_2: integerLtRatio(0, R_ONE)
#blaster [ (integerLtRatio 0 R_ONE) = true ]

-- INTEGER_LT_RATIO_CONSTANT_3: integerLtRatio(0, R_HALF)
#blaster [ (integerLtRatio 0 R_HALF) = true ]

-- INTEGER_LT_RATIO_CONSTANT_4: not(integerLtRatio(10, ratio(25, 3)))
#blaster [ (integerLtRatio 10 (ratio 25 3)) = false ]

-- INTEGER_LT_RATIO_CONSTANT_5: not(integerLtRatio(10, ratio(5, 3)))
#blaster [ (integerLtRatio 10 (ratio 5 3)) = false ]

-- INTEGER_LT_RATIO_CONSTANT_6: not(integerLtRatio(16, ratio(16, 13)))
#blaster [ (integerLtRatio 16 (ratio 16 13)) = false ]

-- INTEGER_LT_RATIO_CONSTANT_7: integerLtRatio(-16, ratio(16, 13))
#blaster [ (integerLtRatio (-16) (ratio 16 13)) = true ]

-- INTEGER_LT_RATIO_CONSTANT_8: not(integerLtRatio(16, ratio(-208, 13)))
#blaster [ (integerLtRatio 16 (ratio (-208) 13)) = false ]

-- INTEGER_LT_RATIO_CONSTANT_9: not(integerLtRatio(16, ratio(208, 13)))
#blaster [ (integerLtRatio 16 (ratio 208 13)) = false ]

-- INTEGER_LT_RATIO_CONSTANT_10: not(integerLtRatio(16, ratio(208, -13)))
#blaster [ (integerLtRatio 16 (ratio 208 (-13))) = false ]

/- IntegerLtRatioValidity -/

-- INTEGER_LT_NOT_VALIDRATIO: ~isValidRatio(a) => ~ integerLtRatio(i, a)
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (integerLtRatio i a) = false ]

-- INTEGER_LT_CORRECTNESS: isValidRatio(a) => integerLtRatio(i, a) = ltRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerLtRatio i a == ltRatio (fromInteger i) a) = true ]

/- IntegerLeqRatioBasics -/

-- INTEGER_LEQ_RATIO_CONSTANT_1: integerLeqRatio(0, R_ZERO)
#blaster [ (integerLeqRatio 0 R_ZERO) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_2: integerLeqRatio(0, R_ONE)
#blaster [ (integerLeqRatio 0 R_ONE) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_3: integerLeqRatio(0, R_HALF)
#blaster [ (integerLeqRatio 0 R_HALF) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_4: integerLeqRatio(10, ratio(125, 3))
#blaster [ (integerLeqRatio 10 (ratio 125 3)) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_5: not(integerLeqRatio(10, ratio(5, 3)))
#blaster [ (integerLeqRatio 10 (ratio 5 3)) = false ]

-- INTEGER_LEQ_RATIO_CONSTANT_6: not(integerLeqRatio(16, ratio(16, 13)))
#blaster [ (integerLeqRatio 16 (ratio 16 13)) = false ]

-- INTEGER_LEQ_RATIO_CONSTANT_7: integerLeqRatio(-16, ratio(16, 13))
#blaster [ (integerLeqRatio (-16) (ratio 16 13)) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_8: not(integerLeqRatio(16, ratio(-208, 13)))
#blaster [ (integerLeqRatio 16 (ratio (-208) 13)) = false ]

-- INTEGER_LEQ_RATIO_CONSTANT_9: integerLeqRatio(16, ratio(208, 13))
#blaster [ (integerLeqRatio 16 (ratio 208 13)) = true ]

-- INTEGER_LEQ_RATIO_CONSTANT_10: not(integerLeqRatio(16, ratio(208, -13)))
#blaster [ (integerLeqRatio 16 (ratio 208 (-13))) = false ]

/- IntegerLeqRatioValidity -/

-- INTEGER_LEQ_NOT_VALIDRATIO: ~isValidRatio(a) => ~ integerLeqRatio(i, a)
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (integerLeqRatio i a) = false ]

-- INTEGER_LEQ_CORRECTNESS: isValidRatio(a) => integerLeqRatio(i, a) = leqRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerLeqRatio i a == leqRatio (fromInteger i) a) = true ]

/- IntegerGtRatioBasics -/

-- INTEGER_GT_RATIO_CONSTANT_1: not(integerGtRatio(0, R_ZERO))
#blaster [ (integerGtRatio 0 R_ZERO) = false ]

-- INTEGER_GT_RATIO_CONSTANT_2: integerGtRatio(1, R_ZERO)
#blaster [ (integerGtRatio 1 R_ZERO) = true ]

-- INTEGER_GT_RATIO_CONSTANT_3: integerGtRatio(1, R_HALF)
#blaster [ (integerGtRatio 1 R_HALF) = true ]

-- INTEGER_GT_RATIO_CONSTANT_4: integerGtRatio(10, ratio(17, 3))
#blaster [ (integerGtRatio 10 (ratio 17 3)) = true ]

-- INTEGER_GT_RATIO_CONSTANT_5: not(integerGtRatio(10, ratio(155, 3)))
#blaster [ (integerGtRatio 10 (ratio 155 3)) = false ]

-- INTEGER_GT_RATIO_CONSTANT_6: integerGtRatio(16, ratio(16, 13))
#blaster [ (integerGtRatio 16 (ratio 16 13)) = true ]

-- INTEGER_GT_RATIO_CONSTANT_7: integerGtRatio(16, ratio(-16, 13))
#blaster [ (integerGtRatio 16 (ratio (-16) 13)) = true ]

-- INTEGER_GT_RATIO_CONSTANT_8: integerGtRatio(16, ratio(-208, 13))
#blaster [ (integerGtRatio 16 (ratio (-208) 13)) = true ]

-- INTEGER_GT_RATIO_CONSTANT_9: not(integerGtRatio(16, ratio(208, 13)))
#blaster [ (integerGtRatio 16 (ratio 208 13)) = false ]

-- INTEGER_GT_RATIO_CONSTANT_10: integerGtRatio(16, ratio(208, -13))
#blaster [ (integerGtRatio 16 (ratio 208 (-13))) = true ]

/- IntegerGtRatioValidity -/

-- INTEGER_GT_NOT_VALIDRATIO: ~isValidRatio(a) => ~ integerGtRatio(i, a)
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (integerGtRatio i a) = false ]

-- INTEGER_GT_CORRECTNESS: isValidRatio(a) => integerGtRatio(i, a) = gtRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerGtRatio i a == gtRatio (fromInteger i) a) = true ]

/- IntegerGeqRatioBasics -/

-- INTEGER_GEQ_RATIO_CONSTANT_1: integerGeqRatio(0, R_ZERO)
#blaster [ (integerGeqRatio 0 R_ZERO) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_2: integerGeqRatio(1, R_ZERO)
#blaster [ (integerGeqRatio 1 R_ZERO) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_3: integerGeqRatio(1, R_HALF)
#blaster [ (integerGeqRatio 1 R_HALF) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_4: integerGeqRatio(10, ratio(17, 3))
#blaster [ (integerGeqRatio 10 (ratio 17 3)) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_5: not(integerGeqRatio(10, ratio(155, 3)))
#blaster [ (integerGeqRatio 10 (ratio 155 3)) = false ]

-- INTEGER_GEQ_RATIO_CONSTANT_6: integerGeqRatio(16, ratio(16, 13))
#blaster [ (integerGeqRatio 16 (ratio 16 13)) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_7: integerGeqRatio(16, ratio(-16, 13))
#blaster [ (integerGeqRatio 16 (ratio (-16) 13)) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_8: integerGeqRatio(16, ratio(-208, 13))
#blaster [ (integerGeqRatio 16 (ratio (-208) 13)) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_9: integerGeqRatio(16, ratio(208, 13))
#blaster [ (integerGeqRatio 16 (ratio 208 13)) = true ]

-- INTEGER_GEQ_RATIO_CONSTANT_10: integerGeqRatio(16, ratio(208, -13))
#blaster [ (integerGeqRatio 16 (ratio 208 (-13))) = true ]

/- IntegerGeqRatioValidity -/

-- INTEGER_GEQ_NOT_VALIDRATIO: ~isValidRatio(a) => ~ integerGeqRatio(i, a)
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (integerGeqRatio i a) = false ]

-- INTEGER_GEQ_CORRECTNESS: isValidRatio(a) => integerGeqRatio(i, a) = geqRatio(fromInteger(i), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (integerGeqRatio i a == geqRatio (fromInteger i) a) = true ]

end Tests.Ratio.IntegerRatio
