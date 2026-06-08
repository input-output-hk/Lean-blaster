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

end Tests.Ratio.Addition
