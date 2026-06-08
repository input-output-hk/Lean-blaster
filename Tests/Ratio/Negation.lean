import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Negation

/- NegationBasics -/

-- NEGATE_ZERO: negate(0) = 0
#blaster [ ((negate R_ZERO == R_ZERO) && eqRatio (negate R_ZERO) R_ZERO) = true ]

-- NEGATE_ONE: negate(1) = -1
#blaster [ ((negate R_ONE == fromInteger (-1)) && eqRatio (negate R_ONE) (fromInteger (-1))) = true ]

-- NEGATE_HALF: negate(1/2) = -1/2
#blaster [ ((negate R_HALF == ratio (-1) 2) && eqRatio (negate R_HALF) (ratio (-1) 2)) = true ]

-- NEGATE_CONSTANTS_1: negate(15/45) = -15/45
#blaster [ ((negate (ratio 15 45) == ratio (-15) 45) && eqRatio (negate (ratio 15 45)) (ratio (-15) 45)) = true ]

-- NEGATE_CONSTANTS_2: negate(-15/45) = 15/45
#blaster [ ((negate (ratio (-15) 45) == ratio 15 45) && eqRatio (negate (ratio (-15) 45)) (ratio 15 45)) = true ]

-- NEGATE_CONSTANTS_3: negate(15/-45) = 15/45
#blaster [ ((negate (ratio 15 (-45)) == ratio 15 45) && eqRatio (negate (ratio 15 (-45))) (ratio 15 45)) = true ]

/- NegationRelational -/

-- NEGATE_SWAP_SIGN_1: isValidRatio(a) => a < 0 => negate(a) > 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → ltRatio a R_ZERO = true →
  (gtRatio (negate a) R_ZERO) = true ]

-- NEGATE_SWAP_SIGN_2: isValidRatio(a) => a > 0 => negate(a) < 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → gtRatio a R_ZERO = true →
  (ltRatio (negate a) R_ZERO) = true ]

-- NEGATE_EQ_IFF: isValidRatio(a) => negate(a) = negate(b) <-> a = b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true →
  (eqRatio (negate a) (negate b) == eqRatio a b) = true ]

-- NEGATE_LT_GT_IFF: isValidRatio(a) => negate(a) < negate(b) <-> a > b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true →
  (ltRatio (negate a) (negate b) == gtRatio a b) = true ]

-- NEGATE_GT_LT_IFF: isValidRatio(a) => negate(a) > negate(b) => a < b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → gtRatio (negate a) (negate b) = true →
  (ltRatio a b) = true ]

-- NEGATE_LEQ_GET_IFF: isValidRatio(a) => negate(a) <= negate(b) <-> a >= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true →
  (leqRatio (negate a) (negate b) == geqRatio a b) = true ]

-- NEGATE_GEQ_LEQ_IFF: isValidRatio(a) => negate(a) >= negate(b) => a <= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → geqRatio (negate a) (negate b) = true →
  (leqRatio a b) = true ]

/- NegationValidity -/

-- NEGATE_NOT_VALIDRATIO: ~isValidRatio(a) => ~isValidRatio(negate(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (negate a)) = false ]

-- NEGATE_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => isValidAndNormalizedRatio(negate(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (isValidAndNormalizedRatio (negate a)) = true ]

end Tests.Ratio.Negation
