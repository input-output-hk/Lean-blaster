import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Multiplication

/- MultiplicationBasics -/

-- MUL_ZERO_TWICE: 0 * 0 = 0
#blaster [ ((mulRatio R_ZERO R_ZERO == R_ZERO) && eqRatio (mulRatio R_ZERO R_ZERO) R_ZERO) = true ]

-- MUL_ZERO_ONE: 0 * 1 = 0
#blaster [ ((mulRatio R_ZERO R_ONE == R_ZERO) && eqRatio (mulRatio R_ZERO R_ONE) R_ZERO) = true ]

-- MUL_HALF_TWICE: 0.5 * 0.5 = 0.25
#blaster [ (eqRatio (mulRatio R_HALF R_HALF) (ratio 1 4)) = true ]

-- MUL_ONE_TWICE: 1 * 1 = 1
#blaster [ ((mulRatio R_ONE R_ONE == R_ONE) && eqRatio (mulRatio R_ONE R_ONE) R_ONE) = true ]

-- MUL_ONE_NEGATE: 1 * -1 = -1
#blaster [ (mulRatio R_ONE (negate R_ONE) == negate R_ONE) = true ]

-- MUL_CONSTANTS_1: 5/10 * 4/15 = 2/15
#blaster [ (eqRatio (mulRatio (ratio 5 10) (ratio 4 15)) (ratio 2 15)) = true ]

-- MUL_CONSTANTS_2: 5/10 * 12/45 = 2/15
#blaster [ (eqRatio (mulRatio (ratio 5 10) (ratio 12 45)) (ratio 2 15)) = true ]

-- MUL_CONSTANTS_3: 5/10 * -4/15 = -2/15
#blaster [ (eqRatio (mulRatio (ratio 5 10) (ratio (-4) 15)) (ratio (-2) 15)) = true ]

-- MUL_CONSTANTS_4: 5/10 * 4/-15 = -2/15
#blaster [ (eqRatio (mulRatio (ratio 5 10) (ratio 4 (-15))) (ratio (-2) 15)) = true ]

-- MUL_CONSTANTS_5: 5/10 * -12/-45 = 2/15
#blaster [ (eqRatio (mulRatio (ratio 5 10) (ratio (-12) (-45))) (ratio 2 15)) = true ]

/- MultiplicationCommutativity -/

-- MUL_COMMUTATIVITY
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → b.isNaN = false →
  (mulRatio a b == mulRatio b a) = true ]

/- MultiplicationAssociativityOne -/

-- MUL_ASSOCIATIVITY_1: (a * b) * c = a * (b * c)
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (mulRatio (mulRatio a b) c == mulRatio a (mulRatio b c)) = true ]

/- MultiplicationAssociativityTwo -/

-- MUL_ASSOCIATIVITY_2: (a * b) * c = (a * c) * b
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (mulRatio (mulRatio a b) c == mulRatio (mulRatio a c) b) = true ]

/- MultiplicationIdentity -/

-- MUL_ZERO_LEFT: 0 * a = 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (eqRatio (mulRatio R_ZERO a) R_ZERO) = true ]

-- MUL_ZERO_RIGHT: a * 0 = 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (eqRatio (mulRatio a R_ZERO) R_ZERO) = true ]

-- MUL_IDENTITY_LEFT: 1 * a = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((mulRatio R_ONE a == a) && eqRatio (mulRatio R_ONE a) a) = true ]

-- MUL_IDENTITY_RIGHT: a * 1 = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((mulRatio a R_ONE == a) && eqRatio (mulRatio a R_ONE) a) = true ]

/- MultiplicationNegation -/

-- MUL_NEGATE_ONE: a * -1 = -a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (mulRatio a (negate R_ONE) == negate a) = true ]

-- MUL_NEG_LEFT: -a * b = -(a * b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (mulRatio (negate a) b == negate (mulRatio a b)) = true ]

-- MUL_NEG_RIGHT: a * -b = -(a * b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (mulRatio a (negate b) == negate (mulRatio a b)) = true ]

/- MultiplicationRelational -/

-- MUL_GT_IFF: a > 0 => (b > 0 <-> a * b > 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (gtRatio b R_ZERO == gtRatio (mulRatio a b) R_ZERO) = true ]

-- MUL_GEQ_IFF: a > 0 => (b >= 0 <-> a * b >= 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (geqRatio b R_ZERO == geqRatio (mulRatio a b) R_ZERO) = true ]

-- MUL_LT_IFF: a < 0 => (b < 0 <-> a * b > 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a R_ZERO = true →
  (ltRatio b R_ZERO == gtRatio (mulRatio a b) R_ZERO) = true ]

-- MUL_LEQ_IFF: a < 0 => (b <= 0 <-> a * b >= 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a R_ZERO = true →
  (leqRatio b R_ZERO == geqRatio (mulRatio a b) R_ZERO) = true ]

-- MUL_LT_NEG_IFF: a > 0 => (a * b < 0 <-> b < 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (ltRatio (mulRatio a b) R_ZERO == ltRatio b R_ZERO) = true ]

-- MUL_LEQ_NEG_IFF: a > 0 => (a * b <= 0 <-> b <= 0)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (leqRatio (mulRatio a b) R_ZERO == leqRatio b R_ZERO) = true ]

-- MUL_REQ_IFF: a <> 0 => (a * b = a * c <-> b = c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a R_ZERO = false →
  (eqRatio (mulRatio a b) (mulRatio a c) == eqRatio b c) = true ]

-- MUL_LEQ_COMPARE: a >= 0 => b <= c => a * b <= a * c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a R_ZERO = true → leqRatio b c = true →
  (leqRatio (mulRatio a b) (mulRatio a c)) = true ]

-- MUL_LT_COMPARE: a > 0 => (b < c <-> a * b < a * c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (ltRatio b c == ltRatio (mulRatio a b) (mulRatio a c)) = true ]

-- MUL_GEQ_COMPARE: a >= 0 => b >= c => a * b >= a * c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a R_ZERO = true → geqRatio b c = true →
  (geqRatio (mulRatio a b) (mulRatio a c)) = true ]

-- MUL_GT_COMPARE: a > 0 => (b > c <-> a * b > a * c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a R_ZERO = true →
  (gtRatio b c == gtRatio (mulRatio a b) (mulRatio a c)) = true ]

-- MUL_EQ_SWAP: b <> 0 => c <> 0 => (a * b = c <-> a = c * recip(b))
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → eqRatio b R_ZERO = false → eqRatio c R_ZERO = false →
  (eqRatio (mulRatio a b) c == eqRatio a (mulRatio c (recip b))) = true ]

/- MultiplicationValidity -/

-- MUL_NOT_VALIDRATIO_LEFT: ~valid a => valid b => ~valid (a * b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = false → isValidRatio b = true →
  (isValidRatio (mulRatio a b)) = false ]

-- MUL_NOT_VALIDRATIO_RIGHT: valid a => ~valid b => ~valid (a * b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = false →
  (isValidRatio (mulRatio a b)) = false ]

-- MUL_VALID_AND_NORMALIZED_RATIO: valid a => valid b => validAndNormalized (a * b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (isValidAndNormalizedRatio (mulRatio a b)) = true ]

end Tests.Ratio.Multiplication
