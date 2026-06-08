import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Subtraction

/- SubtractionBasics -/

-- SUB_ZERO_TWICE: 0 - 0 = 0
#blaster [ ((subRatio R_ZERO R_ZERO == R_ZERO) && eqRatio (subRatio R_ZERO R_ZERO) R_ZERO) = true ]

-- ONE_PRED: 0 - 1 = -1
#blaster [ ((subRatio R_ZERO R_ONE == negate R_ONE) && eqRatio (subRatio R_ZERO R_ONE) (negate R_ONE)) = true ]

-- SUB_HALF_TWICE: 0.5 - 0.5 = 0
#blaster [ (eqRatio (subRatio R_HALF R_HALF) R_ZERO) = true ]

-- SUB_ONE_TWICE: 1 - 1 = 0
#blaster [ ((subRatio R_ONE R_ONE == R_ZERO) && eqRatio (subRatio R_ONE R_ONE) R_ZERO) = true ]

-- ONE_NEGATE: 1 - (-1) = 2
#blaster [ ((subRatio R_ONE (negate R_ONE) == fromInteger 2) && eqRatio (subRatio R_ONE (negate R_ONE)) (fromInteger 2)) = true ]

-- SUB_CONSTANTS_1: 85/100 - 15/100 = 70/100
#blaster [ (eqRatio (subRatio (ratio 85 100) (ratio 15 100)) (ratio 70 100)) = true ]

-- SUB_CONSTANTS_2: 85/100 - 150/1000 = 70/100
#blaster [ (eqRatio (subRatio (ratio 85 100) (ratio 150 1000)) (ratio 70 100)) = true ]

-- SUB_CONSTANTS_3: 85/100 - (-15)/100 = 1
#blaster [ (eqRatio (subRatio (ratio 85 100) (ratio (-15) 100)) R_ONE) = true ]

-- SUB_CONSTANTS_4: 85/100 - 15/(-100) = 1
#blaster [ (eqRatio (subRatio (ratio 85 100) (ratio 15 (-100))) R_ONE) = true ]

-- SUB_CONSTANTS_5: 85/100 - (-15)/(-100) = 70/100
#blaster [ (eqRatio (subRatio (ratio 85 100) (ratio (-15) (-100))) (ratio 70 100)) = true ]

/- SubtractionIdentity -/

-- SUB_IDENTITY: valid a => a - 0 = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((subRatio a R_ZERO == a) && eqRatio (subRatio a R_ZERO) a) = true ]

-- SUB_SAME: valid a => a - a = 0
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (eqRatio (subRatio a a) R_ZERO) = true ]

-- SUB_NEGATION: valid a => 0 - a = -a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((eqRatio (subRatio R_ZERO a) (negate a)) && (subRatio R_ZERO a == negate a)) = true ]

/- SubtractionNegation -/

-- SUB_OPPOSITE: valid a => valid b => a - (-a) = a * 2
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (subRatio a (negate a)) (mulRatio a (fromInteger 2))) = true ]

-- SUB_NEG_DISTRIB: valid a => valid b => -(a - b) = (-a) - (-b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (negate (subRatio a b) == subRatio (negate a) (negate b)) = true ]

/- SubtractionNotCommutative -/

-- SUB_NOT_COMMUTATIVE: valid a => (a - b = b - a) => a = b
-- This is a qualified non-commutativity property: subtraction commutes ONLY when a = b.
-- Only isValidRatio(a) is guarded (no isValidRatio(b) in the Lustre source).
-- The implication chain a - b = b - a => a = b is preserved as two hypotheses.
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true →
  (eqRatio (subRatio a b) (subRatio b a)) = true →
  (eqRatio a b) = true ]

/- SubtractionDistributivity -/

-- SUB_MUL_DISTRIB: valid a => valid b => valid c => (a - b) * c = (a * c) - (b * c)
#blaster (timeout: 120) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → isValidRatio c = true →
  ( eqRatio (mulRatio (subRatio a b) c) (subRatio (mulRatio a c) (mulRatio b c))
    && (((a.denominator == -a_d) && (a.numerator == -a_n)) || ((a.denominator == a_d) && (a.numerator == a_n)))
    && (((b.denominator == -b_d) && (b.numerator == -b_n)) || ((b.denominator == b_d) && (b.numerator == b_n)))
    && (((c.denominator == -c_d) && (c.numerator == -c_n)) || ((c.denominator == c_d) && (c.numerator == c_n)))
    && ((subRatio (mulRatio a c) (mulRatio b c)).denominator > 0)
    && ((mulRatio a c).denominator > 0)
    && ((mulRatio b c).denominator > 0)
    && ((mulRatio (subRatio a b) c).denominator > 0)
    && ((subRatio a b).denominator > 0)
    && (a.denominator > 0)
    && (b.denominator > 0)
    && (c.denominator > 0)
  ) = true ]

/- SubtractionRelational -/

-- SUB_GEQ_POS: valid a => valid b => a - b >= 0 => b <= a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  geqRatio (subRatio a b) R_ZERO = true →
  (leqRatio b a) = true ]

-- SUB_LEQ_NEG: valid a => valid b => a - b <= 0 => b >= a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  leqRatio (subRatio a b) R_ZERO = true →
  (geqRatio b a) = true ]

-- SUB_REQ_IFF: valid a => valid b => (a - b = a - c) <-> (b = c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (subRatio a b) (subRatio a c) == eqRatio b c) = true ]

-- SUB_RLT_GEQ: valid a => valid b => a - b < a - c => b >= c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  ltRatio (subRatio a b) (subRatio a c) = true →
  (geqRatio b c) = true ]

-- SUB_RLEQ_GEQ: valid a => valid b => a - b <= a - c => b >= c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  leqRatio (subRatio a b) (subRatio a c) = true →
  (geqRatio b c) = true ]

-- SUB_RGT_LEQ: valid a => valid b => a - b > a - c => b <= c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  gtRatio (subRatio a b) (subRatio a c) = true →
  (leqRatio b c) = true ]

-- SUB_RGEQ_LEQ: valid a => valid b => a - b >= a - c => b <= c
-- Note: the Lustre source comment says "<-> b <= c" but the check body uses "=>" (implication),
-- not "=" (biconditional). Translated faithfully as an implication.
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  geqRatio (subRatio a b) (subRatio a c) = true →
  (leqRatio b c) = true ]

-- SUB_EQ_SWAP: valid a => valid b => (a - b = c) <-> (a = c + b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (subRatio a b) c == eqRatio a (addRatio c b)) = true ]

/- SubtractionValidity -/

-- SUB_NOT_VALIDRATIO_LEFT: ~valid a => valid b => ~valid (a - b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = false → isValidRatio b = true →
  (isValidRatio (subRatio a b)) = false ]

-- SUB_NOT_VALIDRATIO_RIGHT: valid a => ~valid b => ~valid (a - b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = false →
  (isValidRatio (subRatio a b)) = false ]

-- SUB_VALID_AND_NORMALIZED_RATIO: valid a => valid b => validAndNormalized (a - b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (isValidAndNormalizedRatio (subRatio a b)) = true ]

end Tests.Ratio.Subtraction
