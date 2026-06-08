import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Addition

/- AdditionBasics -/

-- ADD_ZERO_TWICE: 0 + 0 = 0
#blaster [ ((addRatio R_ZERO R_ZERO == R_ZERO) && eqRatio (addRatio R_ZERO R_ZERO) R_ZERO) = true ]

-- ONE_SUCC: 0 + 1 = 1
#blaster [ ((addRatio R_ZERO R_ONE == R_ONE) && eqRatio (addRatio R_ZERO R_ONE) R_ONE) = true ]

-- ADD_HALF_TWICE: 0.5 + 0.5 = 1
#blaster [ (eqRatio (addRatio R_HALF R_HALF) R_ONE) = true ]

-- ADD_ONE_TWICE: 1 + 1 = 2
#blaster [ ((addRatio R_ONE R_ONE == fromInteger 2) && eqRatio (addRatio R_ONE R_ONE) (fromInteger 2)) = true ]

-- ONE_NEGATE: 1 + (-1) = 0
#blaster [ (addRatio R_ONE (negate R_ONE) == R_ZERO) = true ]

-- ADD_CONSTANTS_1: 85/100 + 15/100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 100)) R_ONE) = true ]

-- ADD_CONSTANTS_2: 85/100 + 150/1000 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 150 1000)) R_ONE) = true ]

-- ADD_CONSTANTS_3: 85/100 + -15/100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) 100)) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_4: 85/100 + 15/-100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 (-100))) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_5: 85/100 + -15/-100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) (-100))) R_ONE) = true ]

/- AdditionCommutativity -/

-- ADD_COMMUTATIVITY
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → b.isNaN = false →
  (addRatio a b == addRatio b a) = true ]

/- AdditionAssociativity -/

-- ADD_ASSOCIATIVITY_1: (a + b) + c = a + (b + c)
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (addRatio (addRatio a b) c == addRatio a (addRatio b c)) = true ]

-- ADD_ASSOCIATIVITY_2: (a + c) + b = (a + b) + c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (addRatio (addRatio a c) b == addRatio (addRatio a b) c) = true ]

/- AdditionIdentity -/

-- IDENTITY_LEFT: 0 + a = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((addRatio R_ZERO a == a) && eqRatio (addRatio R_ZERO a) a) = true ]

-- IDENTITY_RIGHT: a + 0 = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((addRatio a R_ZERO == a) && eqRatio (addRatio a R_ZERO) a) = true ]

/- AdditionNegation -/

-- ADD_OPPOSITE: a + (-a) = 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a (negate a)) R_ZERO) = true ]

-- ADD_NEG_DISTRIB: -(a + b) = -a + -b
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (negate (addRatio a b) == addRatio (negate a) (negate b)) = true ]

/- AdditionRelational -/

-- ADD_TWICE_EQ_MUL_BY_2: a + a = 2 * a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (eqRatio (addRatio a a) (mulRatio (fromInteger 2) a)) = true ]

-- ADD_GT_POS: a > 0 → b > 0 → a + b > 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  gtRatio a R_ZERO = true → gtRatio b R_ZERO = true →
  (gtRatio (addRatio a b) R_ZERO) = true ]

-- ADD_LT_NEG: a < 0 → b < 0 → a + b < 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  ltRatio a R_ZERO = true → ltRatio b R_ZERO = true →
  (ltRatio (addRatio a b) R_ZERO) = true ]

-- ADD_OPP_GEQ_POS: a < 0 → a + b ≥ 0 → b ≥ -a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  ltRatio a R_ZERO = true → geqRatio (addRatio a b) R_ZERO = true →
  (geqRatio b (negate a)) = true ]

-- ADD_OPP_LEQ_NEG: a > 0 → a + b ≤ 0 → b ≤ -a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  gtRatio a R_ZERO = true → leqRatio (addRatio a b) R_ZERO = true →
  (leqRatio b (negate a)) = true ]

-- ADD_REQ_IFF: (a + b = a + c) ↔ (b = c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a b) (addRatio a c) == eqRatio b c) = true ]

-- ADD_RLT_IFF: (a + b < a + c) ↔ (b < c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (ltRatio (addRatio a b) (addRatio a c) == ltRatio b c) = true ]

-- ADD_RLEQ_IFF: (a + b ≤ a + c) ↔ (b ≤ c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (leqRatio (addRatio a b) (addRatio a c) == leqRatio b c) = true ]

-- ADD_RGT_IFF: (a + b > a + c) ↔ (b > c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (gtRatio (addRatio a b) (addRatio a c) == gtRatio b c) = true ]

-- ADD_RGEQ_IFF: (a + b ≥ a + c) ↔ (b ≥ c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (geqRatio (addRatio a b) (addRatio a c) == geqRatio b c) = true ]

-- ADD_EQ_SWAP: (a + b = c) ↔ (a = c - b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a b) c == eqRatio a (subRatio c b)) = true ]

-- Normalization lemmas (numerator/denominator carry at most a shared sign flip).
-- One per node variable a/b/c, mirroring AdditionRelational.lus:48-50.
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((((a.denominator == -a_d) && (a.numerator == -a_n))
    || ((a.denominator == a_d) && (a.numerator == a_n)))) = true ]

#blaster [ ∀ (b_n b_d : Int),
  let b := ratio b_n b_d
  isValidRatio b = true →
  ((((b.denominator == -b_d) && (b.numerator == -b_n))
    || ((b.denominator == b_d) && (b.numerator == b_n)))) = true ]

#blaster [ ∀ (c_n c_d : Int),
  let c := ratio c_n c_d
  isValidRatio c = true →
  ((((c.denominator == -c_d) && (c.numerator == -c_n))
    || ((c.denominator == c_d) && (c.numerator == c_n)))) = true ]

/- AdditionValidity -/

-- ADD_NOT_VALIDRATIO_LEFT: ¬valid a → valid b → ¬valid (a + b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = false → isValidRatio b = true →
  (isValidRatio (addRatio a b)) = false ]

-- ADD_NOT_VALIDRATIO_RIGHT: valid a → ¬valid b → ¬valid (a + b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = false →
  (isValidRatio (addRatio a b)) = false ]

-- ADD_VALID_AND_NORMALIZED_RATIO: valid a → valid b → validAndNormalized (a + b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (isValidAndNormalizedRatio (addRatio a b)) = true ]

/- AdditionDistributivity -/

-- ADD_MUL_DISTRIB: (a + b) * c = (a * c) + (b * c), plus the source's normalization/positivity lemmas
#blaster (timeout: 120) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → isValidRatio c = true →
  ( eqRatio (mulRatio (addRatio a b) c) (addRatio (mulRatio a c) (mulRatio b c))
    && (((a.denominator == -a_d) && (a.numerator == -a_n)) || ((a.denominator == a_d) && (a.numerator == a_n)))
    && (((b.denominator == -b_d) && (b.numerator == -b_n)) || ((b.denominator == b_d) && (b.numerator == b_n)))
    && (((c.denominator == -c_d) && (c.numerator == -c_n)) || ((c.denominator == c_d) && (c.numerator == c_n)))
    && decide ((addRatio (mulRatio a c) (mulRatio b c)).denominator > 0)
    && decide ((mulRatio a c).denominator > 0)
    && decide ((mulRatio b c).denominator > 0)
    && decide ((mulRatio (addRatio a b) c).denominator > 0)
    && decide ((addRatio a b).denominator > 0)
    && decide (a.denominator > 0)
    && decide (b.denominator > 0)
    && decide (c.denominator > 0) ) = true ]

end Tests.Ratio.Addition
