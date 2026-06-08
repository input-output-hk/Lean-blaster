import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Truncate

/- TruncateBasics -/

-- TRUNCATE_CONSTANT_1: truncate(ratio(-10, -3)) = 3
#blaster [ (truncate (ratio (-10) (-3)) == 3) = true ]

-- TRUNCATE_CONSTANT_2: truncate(ratio(10, -3)) = -3
#blaster [ (truncate (ratio 10 (-3)) == (-3)) = true ]

-- TRUNCATE_CONSTANT_3: truncate(ratio(-10, 3)) = -3
#blaster [ (truncate (ratio (-10) 3) == (-3)) = true ]

-- TRUNCATE_CONSTANT_4: truncate(ratio(-10, -6)) = 1
#blaster [ (truncate (ratio (-10) (-6)) == 1) = true ]

-- TRUNCATE_CONSTANT_5: truncate(ratio(10, -6)) = -1
#blaster [ (truncate (ratio 10 (-6)) == (-1)) = true ]

-- TRUNCATE_CONSTANT_6: truncate(ratio(-10, 6)) = -1
#blaster [ (truncate (ratio (-10) 6) == (-1)) = true ]

-- TRUNCATE_ZERO: truncate(0) = 0
#blaster [ (truncate R_ZERO == 0) = true ]

-- TRUNCATE_ONE: truncate(1) = 1
#blaster [ (truncate R_ONE == 1) = true ]

-- TRUNCATE_HALF: truncate(0.5) = 0
#blaster [ (truncate R_HALF == 0) = true ]

-- TRUNCATE_INTEGER: truncate(fromInteger(i)) = i
#blaster [ ∀ (i : Int),
  (truncate (fromInteger i) == i) = true ]

/- TruncateEqualityOne -/

-- TRUNCATE_STRUCT_EQ: isValidRatio(a) => isValidRatio(b) => a = b => truncate(a) = truncate(b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (truncate a == truncate b) = true ]

/- TruncateEqualityTwo -/

-- TRUNCATE_EQRATIO: isValidRatio(a) => eqRatio(a, b) => truncate(a) = truncate(b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → eqRatio a b = true →
  (truncate a == truncate b) = true ]

/- TruncateExactDivisor -/

-- TRUNCATE_EXACTDIVISOR: isValidRatio(a) => a.numerator mod a.denominator = 0 => truncate(a) = a.numerator div a.denominator
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (Int.emod a.numerator a.denominator = 0) = true →
  (truncate a == Int.ediv a.numerator a.denominator) = true ]

/- TruncateRounding -/

-- TRUNCATE_RND_TOWARDS_ZERO_1: isValidRatio(a) => absInt(a.numerator) < absInt(a.denominator) => truncate(a) = 0
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (absInt a.numerator < absInt a.denominator) = true →
  (truncate a == 0) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_2: isValidRatio(a) => a.numerator > 0 => a.denominator > 0 => a.numerator mod a.denominator < 0 => truncate(a) = (a.numerator div a.denominator) - 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator > 0) = true →
  decide (a.denominator > 0) = true →
  decide (Int.emod a.numerator a.denominator < 0) = true →
  (truncate a == Int.ediv a.numerator a.denominator - 1) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_3: isValidRatio(a) => a.numerator < 0 => a.denominator > 0 => (a.numerator div a.denominator) * a.denominator < a.numerator => truncate(a) = (a.numerator div a.denominator) + 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator < 0) = true →
  decide (a.denominator > 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator < a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator + 1) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_4: isValidRatio(a) => a.numerator < 0 => a.denominator < 0 => (a.numerator div a.denominator) * a.denominator < a.numerator => truncate(a) = (a.numerator div a.denominator) - 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator < 0) = true →
  decide (a.denominator < 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator < a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator - 1) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_5: isValidRatio(a) => a.numerator > 0 => a.denominator < 0 => (a.numerator div a.denominator) * a.denominator > a.numerator => truncate(a) = (a.numerator div a.denominator) - 1
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator > 0) = true →
  decide (a.denominator < 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator > a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator - 1) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_6: isValidRatio(a) => a.numerator > 0 => a.denominator > 0 => a.numerator mod a.denominator >= 0 => truncate(a) = (a.numerator div a.denominator)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator > 0) = true →
  decide (a.denominator > 0) = true →
  decide (Int.emod a.numerator a.denominator ≥ 0) = true →
  (truncate a == Int.ediv a.numerator a.denominator) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_7: isValidRatio(a) => a.numerator < 0 => a.denominator > 0 => (a.numerator div a.denominator) * a.denominator >= a.numerator => truncate(a) = (a.numerator div a.denominator)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator < 0) = true →
  decide (a.denominator > 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator ≥ a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_8: isValidRatio(a) => a.numerator < 0 => a.denominator < 0 => (a.numerator div a.denominator) * a.denominator >= a.numerator => truncate(a) = (a.numerator div a.denominator)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator < 0) = true →
  decide (a.denominator < 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator ≥ a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator) = true ]

-- TRUNCATE_RND_TOWARDS_ZERO_9: isValidRatio(a) => a.numerator > 0 => a.denominator < 0 => (a.numerator div a.denominator) * a.denominator <= a.numerator => truncate(a) = (a.numerator div a.denominator)
#blaster (timeout: 60) [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  decide (a.numerator > 0) = true →
  decide (a.denominator < 0) = true →
  decide (Int.ediv a.numerator a.denominator * a.denominator ≤ a.numerator) = true →
  (truncate a == Int.ediv a.numerator a.denominator) = true ]

/- TruncateRecipBasics -/

-- TRUNCATE_RECIP_CONSTANT_1: 10 / R_ONE = 10
#blaster [ (truncateRecipRatio 10 R_ONE == 10) = true ]

-- TRUNCATE_RECIP_CONSTANT_2: 10 / R_HALF = 20
#blaster [ (truncateRecipRatio 10 R_HALF == 20) = true ]

-- TRUNCATE_RECIP_CONSTANT_3: 10 / (5/2) = 4
#blaster [ (truncateRecipRatio 10 (ratio 5 2) == 4) = true ]

-- TRUNCATE_RECIP_CONSTANT_4: 10 / (-5/2) = -4
#blaster [ (truncateRecipRatio 10 (ratio (-5) 2) == (-4)) = true ]

-- TRUNCATE_RECIP_CONSTANT_5: 16 / (5/3) = 9
#blaster [ (truncateRecipRatio 16 (ratio 5 3) == 9) = true ]

-- TRUNCATE_RECIP_CONSTANT_6: -16 / (5/3) = -9
#blaster [ (truncateRecipRatio (-16) (ratio 5 3) == (-9)) = true ]

-- TRUNCATE_RECIP_CONSTANT_7: 16 / (-5/3) = -9
#blaster [ (truncateRecipRatio 16 (ratio (-5) 3) == (-9)) = true ]

-- TRUNCATE_RECIP_CONSTANT_8: 16 / (5/-3) = -9
#blaster [ (truncateRecipRatio 16 (ratio 5 (-3)) == (-9)) = true ]

/- TruncateRecipValidity -/

-- TRUNCATE_RECIP_NONE_ZERO: isValidRatio(a) => not(eqRatio(a, R_ZERO)) => truncateRecipRatio(i, a) = truncate(mulRatio(fromInteger(i), recip(a)))
#blaster (timeout: 120) [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true → eqRatio a R_ZERO = false →
  (truncateRecipRatio i a == truncate (mulRatio (fromInteger i) (recip a))) = true ]

end Tests.Ratio.Truncate
