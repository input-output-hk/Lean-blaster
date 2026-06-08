import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Absolute

/- AbsoluteBasics -/

-- ABS_ZERO: abs(0) = 0
#blaster [ ((absRatio R_ZERO == R_ZERO) && eqRatio (absRatio R_ZERO) R_ZERO) = true ]

-- ABS_ONE: abs(1) = 1
#blaster [ ((absRatio R_ONE == R_ONE) && eqRatio (absRatio R_ONE) R_ONE) = true ]

-- ABS_HALF: abs(1/2) = 1/2
#blaster [ ((absRatio R_HALF == R_HALF) && eqRatio (absRatio R_HALF) R_HALF) = true ]

-- ABS_CONSTANTS_1: absRatio(15 / 45) = 15/45
#blaster [ ((absRatio (ratio 15 45) == ratio 15 45) && eqRatio (absRatio (ratio 15 45)) (ratio 15 45)) = true ]

-- ABS_CONSTANTS_2: absRatio(-15 / 45) = 15/45
#blaster [ ((absRatio (ratio (-15) 45) == ratio 15 45) && eqRatio (absRatio (ratio (-15) 45)) (ratio 15 45)) = true ]

-- ABS_CONSTANTS_3: absRatio(15 / -45) = 15/45
#blaster [ ((absRatio (ratio 15 (-45)) == ratio 15 45) && eqRatio (absRatio (ratio 15 (-45))) (ratio 15 45)) = true ]

/- AbsoluteRelational -/

-- ABS_SWAP_NEG: isValidRatio(a) => a < 0 => absRatio(a) > 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → ltRatio a R_ZERO = true →
  (gtRatio (absRatio a) R_ZERO) = true ]

-- ABS_EQ_POS: isValidRatio(a) => a >= 0 => absRatio(a) = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → geqRatio a R_ZERO = true →
  ((absRatio a == a) && eqRatio (absRatio a) a) = true ]

-- ABS_NEGATE_IFF_ON_NEG: isValidRatio(a) => a < 0 => absRatio(a) = negate(a)
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → ltRatio a R_ZERO = true →
  (eqRatio (absRatio a) (negate a)) = true ]

-- ABS_EQ_IF: isValidRatio(a) => eqRatio(a, b) => eqRatio(absRatio(a), absRatio(b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → eqRatio a b = true →
  (eqRatio (absRatio a) (absRatio b)) = true ]

-- ABS_EQ_NEGATE: isValidRatio(a) => eqRatio(absRatio(a), absRatio(b)) => not(eqRatio(a, b)) => eqRatio(negate(a), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → eqRatio (absRatio a) (absRatio b) = true → eqRatio a b = false →
  (eqRatio (negate a) b) = true ]

-- ABS_LT_NEG_GT: isValidRatio(a) => absRatio(a) < absRatio(b) => a <= 0 => b <= 0 => a > b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → ltRatio (absRatio a) (absRatio b) = true → leqRatio a R_ZERO = true → leqRatio b R_ZERO = true →
  (gtRatio a b) = true ]

-- ABS_LT_POS: isValidRatio(a) => absRatio(a) < absRatio(b) => b >= 0 => a < b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → ltRatio (absRatio a) (absRatio b) = true → geqRatio b R_ZERO = true →
  (ltRatio a b) = true ]

-- ABS_LT_LEFT_POS_LT: isValidRatio(a) => absRatio(a) < absRatio(b) => a >= 0 => (b < 0 or b > a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → ltRatio (absRatio a) (absRatio b) = true → geqRatio a R_ZERO = true →
  (ltRatio b R_ZERO || gtRatio b a) = true ]

-- ABS_LEQ_NEG_GEQ: isValidRatio(a) => absRatio(a) <= absRatio(b) => a <= 0 => b <= 0 => a >= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → leqRatio (absRatio a) (absRatio b) = true → leqRatio a R_ZERO = true → leqRatio b R_ZERO = true →
  (geqRatio a b) = true ]

-- ABS_LEQ_POS: isValidRatio(a) => absRatio(a) <= absRatio(b) => b >= 0 => a <= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → leqRatio (absRatio a) (absRatio b) = true → geqRatio b R_ZERO = true →
  (leqRatio a b) = true ]

-- ABS_LEQ_LEFT_POS_GEQ: isValidRatio(a) => absRatio(a) <= absRatio(b) => a >= 0 => (b < 0 or b >= a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → leqRatio (absRatio a) (absRatio b) = true → geqRatio a R_ZERO = true →
  (ltRatio b R_ZERO || geqRatio b a) = true ]

-- ABS_GT_NEG_LT: isValidRatio(a) => absRatio(a) > absRatio(b) => a <= 0 => b <= 0 => a < b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → gtRatio (absRatio a) (absRatio b) = true → leqRatio a R_ZERO = true → leqRatio b R_ZERO = true →
  (ltRatio a b) = true ]

-- ABS_GT_LEFT_POS_GT: isValidRatio(a) => absRatio(a) > absRatio(b) => a >= 0 => a > b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → gtRatio (absRatio a) (absRatio b) = true → geqRatio a R_ZERO = true →
  (gtRatio a b) = true ]

-- ABS_GT_RIGHT_POS_LT: isValidRatio(a) => absRatio(a) > absRatio(b) => b >= 0 => (a < 0 or b < a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → gtRatio (absRatio a) (absRatio b) = true → geqRatio b R_ZERO = true →
  (ltRatio a R_ZERO || ltRatio b a) = true ]

-- ABS_GEQ_NEG_LEQ: isValidRatio(a) => absRatio(a) >= absRatio(b) => a <= 0 => b <= 0 => a <= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → geqRatio (absRatio a) (absRatio b) = true → leqRatio a R_ZERO = true → leqRatio b R_ZERO = true →
  (leqRatio a b) = true ]

-- ABS_GEQ_LEFT_POS_GEQ: isValidRatio(a) => absRatio(a) >= absRatio(b) => a >= 0 => a >= b
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → geqRatio (absRatio a) (absRatio b) = true → geqRatio a R_ZERO = true →
  (geqRatio a b) = true ]

-- ABS_GEQ_RIGHT_POS_LEQ: isValidRatio(a) => absRatio(a) > absRatio(b) => b >= 0 => (a < 0 or b <= a)
-- NOTE: Lustre code uses gtRatio (not geqRatio) despite the comment saying ">="; following the CODE.
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → gtRatio (absRatio a) (absRatio b) = true → geqRatio b R_ZERO = true →
  (ltRatio a R_ZERO || leqRatio b a) = true ]

/- AbsoluteValidity -/

-- ABS_NOT_VALIDRATIO: ~isValidRatio(a) => ~isValidRatio(absRatio(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = false →
  (isValidRatio (absRatio a)) = false ]

-- ABS_VALID_AND_NORMALIZED_RATIO: isValidRatio(a) => isValidAndNormalizedRatio(absRatio(a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (isValidAndNormalizedRatio (absRatio a)) = true ]

end Tests.Ratio.Absolute
