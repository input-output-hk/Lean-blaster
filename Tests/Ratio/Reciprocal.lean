import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Reciprocal

/- ReciprocalBasics -/

-- RECIP_ZERO: not(isValidRatio(recip(0)))
#blaster [ (isValidRatio (recip R_ZERO)) = false ]

-- RECIP_ONE: recip(1) = 1 and eqRatio(recip(1), 1)
#blaster [ ((recip R_ONE == R_ONE) && eqRatio (recip R_ONE) R_ONE) = true ]

-- RECIP_HALF: recip(1/2) = 2 and eqRatio(recip(1/2), 2)
#blaster [ ((recip R_HALF == fromInteger 2) && eqRatio (recip R_HALF) (fromInteger 2)) = true ]

-- RECIP_CONSTANTS_1: eqRatio(recip(15/45), 3)
#blaster [ (eqRatio (recip (ratio 15 45)) (fromInteger 3)) = true ]

-- RECIP_CONSTANTS_2: eqRatio(recip(-18/45), -5/2)
#blaster [ (eqRatio (recip (ratio (-18) 45)) (ratio (-5) 2)) = true ]

-- RECIP_CONSTANTS_3: eqRatio(recip(18/-45), -5/2)
#blaster [ (eqRatio (recip (ratio 18 (-45))) (ratio (-5) 2)) = true ]

/- ReciprocalInteger -/

-- RECIP_INTEGER_1: recip(fromInteger(a)) = ratio(1, a)
#blaster [ ∀ (a : Int),
  (recip (fromInteger a) == ratio 1 a) = true ]

-- RECIP_INTEGER_2: a <> 0 => recip(ratio(1, a)) = fromInteger(a)
#blaster [ ∀ (a : Int),
  (a == 0) = false →
  (recip (ratio 1 a) == fromInteger a) = true ]

-- RECIP_RATIO: a <> 0 => b <> 0 => recip(ratio(a, b)) = ratio(b, a)
#blaster (timeout: 60) [ ∀ (a b : Int),
  (a == 0) = false →
  (b == 0) = false →
  (recip (ratio a b) == ratio b a) = true ]

-- RECIP_EQ_NUM_DENUM: eqRatio(recip(ratio(a,b)), recip(ratio(b,a))) => eqRatio(absRatio(ratio(a,b)), R_ONE)
#blaster (timeout: 60) [ ∀ (a b : Int),
  eqRatio (recip (ratio a b)) (recip (ratio b a)) = true →
  (eqRatio (absRatio (ratio a b)) R_ONE) = true ]

/- ReciprocalValidity -/

-- RECIP_NOT_VALIDRATIO_1: ~isValidRatio(a) => ~isValidRatio(recip(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (recip a)) = false ]

-- RECIP_ZERO_NUM_NOT_VALIDRATIO: isValidRatio(a) => a.numerator = 0 => ~isValidRatio(recip(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (a.numerator == 0) = true →
  (isValidRatio (recip a)) = false ]

-- RECIP_NON_ZERO_NUM_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => a.numerator <> 0 => isValidAndNormalizedRatio(recip(a))
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (a.numerator == 0) = false →
  (isValidAndNormalizedRatio (recip a)) = true ]

-- RECIP_CORRECTNESS_1: isValidRatio(a) => not(eqRatio(a, R_ZERO)) => eqRatio(mulRatio(a, recip(a)), R_ONE)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  eqRatio a R_ZERO = false →
  (eqRatio (mulRatio a (recip a)) R_ONE) = true ]

-- RECIP_CORRECTNESS_2: isValidRatio(a) => isValidRatio(b) => not(eqRatio(a, R_ZERO)) => eqRatio(mulRatio(mulRatio(a, b), recip(a)), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true →
  isValidRatio b = true →
  eqRatio a R_ZERO = false →
  (eqRatio (mulRatio (mulRatio a b) (recip a)) b) = true ]

/- RecipMulRatioBasics -/

-- RECIP_MUL_RATIO_CONSTANT_1: recipMulRatio(10, R_ONE) = ratio(1, 10) and eqRatio(...)
#blaster [ ((recipMulRatio 10 R_ONE == ratio 1 10) && eqRatio (recipMulRatio 10 R_ONE) (ratio 1 10)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_2: eqRatio(recipMulRatio(10, R_HALF), ratio(1, 20))
#blaster [ (eqRatio (recipMulRatio 10 R_HALF) (ratio 1 20)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_3: eqRatio(recipMulRatio(10, ratio(5, 3)), ratio(5, 30))
#blaster [ (eqRatio (recipMulRatio 10 (ratio 5 3)) (ratio 5 30)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_4: eqRatio(recipMulRatio(10, ratio(-5, 3)), ratio(-5, 30))
#blaster [ (eqRatio (recipMulRatio 10 (ratio (-5) 3)) (ratio (-5) 30)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_5: eqRatio(recipMulRatio(16, ratio(5, 13)), ratio(5, 208))
#blaster [ (eqRatio (recipMulRatio 16 (ratio 5 13)) (ratio 5 208)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_6: eqRatio(recipMulRatio(-16, ratio(5, 13)), ratio(-5, 208))
#blaster [ (eqRatio (recipMulRatio (-16) (ratio 5 13)) (ratio (-5) 208)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_7: eqRatio(recipMulRatio(16, ratio(-5, 13)), ratio(-5, 208))
#blaster [ (eqRatio (recipMulRatio 16 (ratio (-5) 13)) (ratio (-5) 208)) = true ]

-- RECIP_MUL_RATIO_CONSTANT_8: eqRatio(recipMulRatio(16, ratio(5, -13)), ratio(-5, 208))
#blaster [ (eqRatio (recipMulRatio 16 (ratio 5 (-13))) (ratio (-5) 208)) = true ]

/- RecipMulRatioValidity -/

-- RECIP_MUL_NOT_VALIDRATIO_1: ~isValidRatio(a) => ~isValidRatio(recipMulRatio(i, a))
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (recipMulRatio i a)) = false ]

-- RECIP_MUL_NOT_VALIDRATIO_2: isValidRatio(a) => i = 0 => not(isValidRatio(recipMulRatio(i, a)))
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (i == 0) = true →
  (isValidRatio (recipMulRatio i a)) = false ]

-- RECIP_MUL_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => i <> 0 => isValidAndNormalizedRatio(recipMulRatio(i, a))
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (i == 0) = false →
  (isValidAndNormalizedRatio (recipMulRatio i a)) = true ]

-- RECIP_MUL_CORRECTNESS: isValidRatio(a) => i <> 0 => recipMulRatio(i, a) = mulRatio(recip(fromInteger(i)), a)
#blaster (timeout: 60) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (i == 0) = false →
  (recipMulRatio i a == mulRatio (recip (fromInteger i)) a) = true ]

end Tests.Ratio.Reciprocal
