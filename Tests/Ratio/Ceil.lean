import Ratio.Ratio

open Ratio

private def ceilCustomRatio (a : Ratio) : Int :=
  let tmp := quotient a.numerator a.denominator
  if a.denominator * tmp < a.numerator then tmp + 1 else tmp

namespace Tests.Ratio.Ceil

/- CeilBasics -/

-- CEIL_CONSTANT_1: ceil(ratio(-10, -3)) = 4
#blaster [ (ceil (ratio (-10) (-3)) == 4) = true ]

-- CEIL_CONSTANT_2: ceil(ratio(10, -3)) = -3
#blaster [ (ceil (ratio 10 (-3)) == (-3)) = true ]

-- CEIL_CONSTANT_3: ceil(ratio(-10, 3)) = -3
#blaster [ (ceil (ratio (-10) 3) == (-3)) = true ]

-- CEIL_CONSTANT_4: ceil(ratio(-10, -6)) = 2
#blaster [ (ceil (ratio (-10) (-6)) == 2) = true ]

-- CEIL_CONSTANT_5: ceil(ratio(10, -6)) = -1
#blaster [ (ceil (ratio 10 (-6)) == (-1)) = true ]

-- CEIL_CONSTANT_6: ceil(ratio(-10, 6)) = -1
#blaster [ (ceil (ratio (-10) 6) == (-1)) = true ]

-- CEIL_ZERO: ceil(0) = 0
#blaster [ (ceil R_ZERO == 0) = true ]

-- CEIL_ONE: ceil(1) = 1
#blaster [ (ceil R_ONE == 1) = true ]

-- CEIL_HALF: ceil(0.5) = 1
#blaster [ (ceil R_HALF == 1) = true ]

-- CEIL_INTEGER: ceil(fromInteger(i)) = i
#blaster [ ∀ (i : Int), (ceil (fromInteger i) == i) = true ]

/- CeilEqualityOne -/

-- CEIL_STRUCT_EQ: isValidRatio(a) => isValidRatio(b) => a = b => ceil(a) = ceil(b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (ceil a == ceil b) = true ]

/- CeilEqualityTwo -/

-- CEIL_EQRATIO: isValidRatio(a) => eqRatio(a, b) => ceil(a) = ceil(b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → eqRatio a b = true →
  (ceil a == ceil b) = true ]

/- CeilExactDivisor -/

-- CEIL_EXACTDIVISOR: isValidRatio(a) => a.numerator mod a.denominator = 0 => ceil(a) = a.numerator div a.denominator
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → (Int.emod a.numerator a.denominator == 0) = true →
  (ceil a == Int.ediv a.numerator a.denominator) = true ]

/- CeilRounding -/

-- CEIL_EQ_TRUNCATE_NEG: isValidRatio(a) => a < 0 => ceil(a) = truncate(a)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → ltRatio a R_ZERO = true →
  (ceil a == truncate a) = true ]

-- CEIL_EQ_TRUNCATE_PLUS_ONE_E_DIV: isValidRatio(a) => a > 0 => a.numerator mod a.denominator <> 0 => ceil(a) = truncate(a) + 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → gtRatio a R_ZERO = true → (Int.emod a.numerator a.denominator != 0) = true →
  (ceil a == truncate a + 1) = true ]

-- CEIL_EQ_TRUNCATE_NE_DIV: isValidRatio(a) => a > 0 => a.numerator mod a.denominator = 0 => ceil(a) = truncate(a)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → gtRatio a R_ZERO = true → (Int.emod a.numerator a.denominator == 0) = true →
  (ceil a == truncate a) = true ]

-- CEIL_RND_TOWARDS_INFINITY_1: isValidRatio(a) => a.numerator > 0 => absInt(a.numerator) < absInt(a.denominator) => ceil(a) = 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → decide (a.numerator > 0) = true → decide (absInt a.numerator < absInt a.denominator) = true →
  (ceil a == 1) = true ]

-- CEIL_RND_TOWARDS_INFINITY_2: isValidRatio(a) => a.numerator <= 0 => absInt(a.numerator) < absInt(a.denominator) => ceil(a) = 0
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → decide (a.numerator ≤ 0) = true → decide (absInt a.numerator < absInt a.denominator) = true →
  (ceil a == 0) = true ]

-- CEIL_RND_TOWARDS_INFINITY_3: isValidRatio(a) => a.numerator mod a.denominator <> 0 => ceil(a) = (a.numerator div a.denominator) + 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → (Int.emod a.numerator a.denominator != 0) = true →
  (ceil a == Int.ediv a.numerator a.denominator + 1) = true ]

-- CEIL_EQUIV_CEIL_CUSTOMRATIO: isValidRatio(a) => ceil(a) = ceilCustomRatio(a)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (ceil a == ceilCustomRatio a) = true ]

end Tests.Ratio.Ceil
