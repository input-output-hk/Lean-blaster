import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Misc

/- MinMaxTheorems -/

-- NaN_MIN_LEFT: a.isNaN => minRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (minRatio a b == R_NaN) = true ]

-- NaN_MIN_RIGHT: a.isNaN => minRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (minRatio a b == R_NaN) = true ]

-- MIN_ISVALID: minRatio(a, b) <> R_NaN => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  (minRatio a b != R_NaN) = true →
  (isValidRatio a && isValidRatio b) = true ]

-- MIN_GEQ_CORRECTNESS_1: geqRatio(a, b) => eqRatio(minRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  geqRatio a b = true →
  eqRatio (minRatio a b) b = true ]

-- MIN_GEQ_CORRECTNESS_2: geqRatio(b, a) => eqRatio(minRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  geqRatio b a = true →
  eqRatio (minRatio a b) a = true ]

-- MIN_GT_CORRECTNESS_1: gtRatio(a, b) => eqRatio(minRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  gtRatio a b = true →
  eqRatio (minRatio a b) b = true ]

-- MIN_GT_CORRECTNESS_2: gtRatio(b, a) => eqRatio(minRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  gtRatio b a = true →
  eqRatio (minRatio a b) a = true ]

-- MIN_LEQ_CORRECTNESS_1: leqRatio(a, b) => eqRatio(minRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  leqRatio a b = true →
  eqRatio (minRatio a b) a = true ]

-- MIN_LEQ_CORRECTNESS_2: leqRatio(b, a) => eqRatio(minRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  leqRatio b a = true →
  eqRatio (minRatio a b) b = true ]

-- MIN_LT_CORRECTNESS_1: ltRatio(a, b) => eqRatio(minRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  ltRatio a b = true →
  eqRatio (minRatio a b) a = true ]

-- MIN_LT_CORRECTNESS_2: ltRatio(b, a) => eqRatio(minRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  ltRatio b a = true →
  eqRatio (minRatio a b) b = true ]

-- NaN_MAX_LEFT: a.isNaN => maxRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (maxRatio a b == R_NaN) = true ]

-- NaN_MAX_RIGHT: a.isNaN => maxRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (maxRatio a b == R_NaN) = true ]

-- MAX_ISVALID: maxRatio(a, b) <> R_NaN => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  (maxRatio a b != R_NaN) = true →
  (isValidRatio a && isValidRatio b) = true ]

-- MAX_GEQ_CORRECTNESS_1: geqRatio(a, b) => eqRatio(maxRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  geqRatio a b = true →
  eqRatio (maxRatio a b) a = true ]

-- MAX_GEQ_CORRECTNESS_2: geqRatio(b, a) => eqRatio(maxRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  geqRatio b a = true →
  eqRatio (maxRatio a b) b = true ]

-- MAX_GT_CORRECTNESS_1: gtRatio(a, b) => eqRatio(maxRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  gtRatio a b = true →
  eqRatio (maxRatio a b) a = true ]

-- MAX_GT_CORRECTNESS_2: gtRatio(b, a) => eqRatio(maxRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  gtRatio b a = true →
  eqRatio (maxRatio a b) b = true ]

-- MAX_LEQ_CORRECTNESS_1: leqRatio(a, b) => eqRatio(maxRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  leqRatio a b = true →
  eqRatio (maxRatio a b) b = true ]

-- MAX_LEQ_CORRECTNESS_2: leqRatio(b, a) => eqRatio(maxRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  leqRatio b a = true →
  eqRatio (maxRatio a b) a = true ]

-- MAX_LT_CORRECTNESS_1: ltRatio(a, b) => eqRatio(maxRatio(a, b), b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  ltRatio a b = true →
  eqRatio (maxRatio a b) b = true ]

-- MAX_LT_CORRECTNESS_2: ltRatio(b, a) => eqRatio(maxRatio(a, b), a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  ltRatio b a = true →
  eqRatio (maxRatio a b) a = true ]

/- RatioConstructors -/

-- FROMINTEGER_DENOMINATOR: fromInteger(i).denominator = 1
#blaster [ ∀ (i : Int),
  ((fromInteger i).denominator == 1) = true ]

-- FROMINTEGER_NUMERATOR: fromInteger(i).numerator = i
#blaster [ ∀ (i : Int),
  ((fromInteger i).numerator == i) = true ]

-- FROMINTEGER_VALIDRATIO: isValidRatio(fromInteger(i))
#blaster [ ∀ (i : Int),
  isValidRatio (fromInteger i) = true ]

-- RATIO_ZERO_DENOMINATOR_NAN: a_d = 0 => ratio(a_n, a_d) = R_NaN
#blaster [ ∀ (a_n a_d : Int),
  (a_d == 0) = true →
  (ratio a_n a_d == R_NaN) = true ]

-- RATIO_NONZERO_DENOMINATOR_VALID: a_d <> 0 => isValidRatio(ratio(a_n, a_d))
#blaster [ ∀ (a_n a_d : Int),
  (a_d != 0) = true →
  isValidRatio (ratio a_n a_d) = true ]

-- RATIO_NONZERO_DENOMINATOR_POS: a_d <> 0 => ratio(a_n, a_d).denominator = absInt(a_d)
#blaster [ ∀ (a_n a_d : Int),
  (a_d != 0) = true →
  ((ratio a_n a_d).denominator == absInt a_d) = true ]

-- RATIO_NEG_DENOMINATOR: a_d < 0 => ratio(a_n, a_d).numerator = -a_n
#blaster [ ∀ (a_n a_d : Int),
  decide (a_d < 0) = true →
  ((ratio a_n a_d).numerator == -a_n) = true ]

-- RATIO_POS_DENOMINATOR: a_d > 0 => ratio(a_n, a_d).numerator = a_n
#blaster [ ∀ (a_n a_d : Int),
  decide (a_d > 0) = true →
  ((ratio a_n a_d).numerator == a_n) = true ]

/- RatioNaN -/

-- FROMINTEGER_NOT_NAN: fromInteger(i) <> R_NaN
#blaster [ ∀ (i : Int),
  (fromInteger i != R_NaN) = true ]

-- RATIO_NONZERO_DENOMINATOR_NOT_NAN: a_d <> 0 => a <> R_NaN
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  (a_d != 0) = true →
  (a != R_NaN) = true ]

-- ADD_NAN_LEFT: a.isNaN => addRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (addRatio a b == R_NaN) = true ]

-- ADD_NAN_RIGHT: a.isNaN => addRatio(b, a) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (addRatio b a == R_NaN) = true ]

-- SUB_NAN_LEFT: a.isNaN => subRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (subRatio a b == R_NaN) = true ]

-- SUB_NAN_RIGHT: a.isNaN => subRatio(b, a) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (subRatio b a == R_NaN) = true ]

-- MUL_NAN_LEFT: a.isNaN => mulRatio(a, b) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (mulRatio a b == R_NaN) = true ]

-- MUL_NAN_RIGHT: a.isNaN => mulRatio(b, a) = R_NaN
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  (mulRatio b a == R_NaN) = true ]

-- NEGATE_NAN: a.isNaN => negate(a) = R_NaN
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (negate a == R_NaN) = true ]

-- ABS_NAN: a.isNaN => absRatio(a) = R_NaN
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (absRatio a == R_NaN) = true ]

-- RECIP_ZERO_NUM_NAN: a_n = 0 => recip(a) = R_NaN
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  (a_n == 0) = true →
  (recip a == R_NaN) = true ]

-- RECIP_NAN: a.isNaN => recip(a) = R_NaN
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (recip a == R_NaN) = true ]

-- INTEGER_MUL_RATIO_NAN: a.isNaN => integerMulRatio(i, a) = R_NaN
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (integerMulRatio i a == R_NaN) = true ]

-- RECIP_MUL_RATIO_NAN: a.isNaN => recipMulRatio(i, a) = R_NaN
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (recipMulRatio i a == R_NaN) = true ]

-- RECIP_MUL_ZERO_INT_NAN: i = 0 => recipMulRatio(i, a) = R_NaN
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  (i == 0) = true →
  (recipMulRatio i a == R_NaN) = true ]

-- INTEGER_ADD_RATIO_NAN: a.isNaN => integerAddRatio(i, a) = R_NaN
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (integerAddRatio i a == R_NaN) = true ]

-- INTEGER_SUB_RATIO_NAN: a.isNaN => integerSubRatio(i, a) = R_NaN
#blaster [ ∀ (i a_n a_d : Int),
  let a := ratio a_n a_d
  a.isNaN = true →
  (integerSubRatio i a == R_NaN) = true ]

/- RelationalTheorems -/

-- NaN_EQ_LEFT: a.isNaN => not (eqRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  eqRatio a b = false ]

-- NaN_EQ_RIGHT: a.isNaN => not (eqRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  eqRatio b a = false ]

-- EQ_ISVALID: eqRatio(a, b) => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  eqRatio a b = true →
  (isValidRatio a && isValidRatio b) = true ]

-- STRUCT_EQ_IMP_EQRATIO: isValidRatio(a) => isValidRatio(b) => a = b => eqRatio(a, b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  eqRatio a b = true ]

-- EQ_REFLEXIVE: isValidRatio(a) => eqRatio(a, a)
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  eqRatio a a = true ]

-- EQ_SYMMETRIC: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => eqRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true →
  eqRatio b a = true ]

-- EQ_TRANSITIVE: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => eqRatio(b, c) => eqRatio(a, c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true → eqRatio b c = true →
  eqRatio a c = true ]

-- EQ_LEQ_LEFT: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => leqRatio(a, b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true →
  leqRatio a b = true ]

-- EQ_LEQ_RIGHT: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => leqRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true →
  leqRatio b a = true ]

-- EQ_GEQ_LEFT: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => geqRatio(a, b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true →
  geqRatio a b = true ]

-- EQ_GEQ_RIGHT: isValidRatio(a) => isValidRatio(b) => eqRatio(a, b) => geqRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → eqRatio a b = true →
  geqRatio b a = true ]

-- NaN_LEQ_LEFT: a.isNaN => not (leqRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  leqRatio a b = false ]

-- NaN_LEQ_RIGHT: a.isNaN => not (leqRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  leqRatio b a = false ]

-- LEQ_ISVALID: leqRatio(a, b) => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  leqRatio a b = true →
  (isValidRatio a && isValidRatio b) = true ]

-- STRUCT_EQ_IMP_LEQ: isValidRatio(a) => isValidRatio(b) => a = b => ( leqRatio(a, b) and leqRatio(b, a) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (leqRatio a b && leqRatio b a) = true ]

-- LEQ_REFLEXIVE: isValidRatio(a) => leqRatio(a, a)
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  leqRatio a a = true ]

-- LEQ_ANTISYMMETRIC: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => leqRatio(b, a) => eqRatio(a, b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true → leqRatio b a = true →
  eqRatio a b = true ]

-- LEQ_TRANSITIVE: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => leqRatio(b, c) => leqRatio(a, c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true → leqRatio b c = true →
  leqRatio a c = true ]

-- LEQ_IMP_EQ_OR_LT: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => ( ltRatio(a, b) or eqRatio(a, b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true →
  (ltRatio a b || eqRatio a b) = true ]

-- LEQ_IMP_GEQ: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => geqRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true →
  geqRatio b a = true ]

-- LEQ_IMP_NOT_LT: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => not(ltRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true →
  ltRatio b a = false ]

-- LEQ_IMP_NOT_GT: isValidRatio(a) => isValidRatio(b) => leqRatio(a, b) => not(gtRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → leqRatio a b = true →
  gtRatio a b = false ]

-- NaN_LT_LEFT: a.isNaN => not (ltRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  ltRatio a b = false ]

-- NaN_LT_RIGHT: a.isNaN => not (ltRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  ltRatio b a = false ]

-- LT_ISVALID: ltRatio(a, b) => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  ltRatio a b = true →
  (isValidRatio a && isValidRatio b) = true ]

-- STRUCT_EQ_IMP_NOT_LT: isValidRatio(a) => isValidRatio(b) => a = b => ( not(ltRatio(a, b)) and not(ltRatio(b, a)) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (!ltRatio a b && !ltRatio b a) = true ]

-- LT_NOT_REFLEXIVE: isValidRatio(a) => not(ltRatio(a, a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ltRatio a a = false ]

-- LT_ANTISYMMETRIC: isValidRatio(a) => isValidRatio(b) => ltRatio(a, b) => not(ltRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a b = true →
  ltRatio b a = false ]

-- LT_TRANSITIVE: isValidRatio(a) => isValidRatio(b) => ltRatio(a, b) => ltRatio(b, c) => ltRatio(a, c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a b = true → ltRatio b c = true →
  ltRatio a c = true ]

-- LT_IMP_GT: isValidRatio(a) => isValidRatio(b) => ltRatio(a, b) => gtRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a b = true →
  gtRatio b a = true ]

-- LT_IMP_NOT_LEQ: isValidRatio(a) => isValidRatio(b) => ltRatio(a, b) => not(leqRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a b = true →
  leqRatio b a = false ]

-- LT_IMP_NOT_GEQ: isValidRatio(a) => isValidRatio(b) => ltRatio(a, b) => not(geqRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → ltRatio a b = true →
  geqRatio a b = false ]

-- NaN_GEQ_LEFT: a.isNaN => not (geqRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  geqRatio a b = false ]

-- NaN_GEQ_RIGHT: a.isNaN => not (geqRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  geqRatio b a = false ]

-- GEQ_ISVALID: geqRatio(a, b) => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  geqRatio a b = true →
  (isValidRatio a && isValidRatio b) = true ]

-- STRUCT_EQ_IMP_GEQ: isValidRatio(a) => isValidRatio(b) => a = b => ( geqRatio(a, b) and geqRatio(b, a) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (geqRatio a b && geqRatio b a) = true ]

-- GEQ_REFLEXIVE: isValidRatio(a) => geqRatio(a, a)
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  geqRatio a a = true ]

-- GEQ_ANTISYMMETRIC: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => geqRatio(b, a) => eqRatio(a, b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true → geqRatio b a = true →
  eqRatio a b = true ]

-- GEQ_TRANSITIVE: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => geqRatio(b, c) => geqRatio(a, c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true → geqRatio b c = true →
  geqRatio a c = true ]

-- GEQ_IMP_EQ_OR_GT: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => ( gtRatio(a, b) or eqRatio(a, b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true →
  (gtRatio a b || eqRatio a b) = true ]

-- GEQ_IMP_LEQ: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => leqRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true →
  leqRatio b a = true ]

-- GEQ_IMP_NOT_GT: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => not(gtRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true →
  gtRatio b a = false ]

-- GEQ_IMP_NOT_LT: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) => not(ltRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → geqRatio a b = true →
  ltRatio a b = false ]

-- NaN_GT_LEFT: a.isNaN => not (gtRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  gtRatio a b = false ]

-- NaN_GT_RIGHT: a.isNaN => not (gtRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  a.isNaN = true →
  gtRatio b a = false ]

-- GT_ISVALID: gtRatio(a, b) => ( isValidRatio(a) and isValidRatio(b) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  gtRatio a b = true →
  (isValidRatio a && isValidRatio b) = true ]

-- STRUCT_EQ_IMP_NOT_GT: isValidRatio(a) => isValidRatio(b) => a = b => ( not(gtRatio(a, b)) and not(gtRatio(b, a)) )
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → (a == b) = true →
  (!gtRatio a b && !gtRatio b a) = true ]

-- GT_NOT_REFLEXIVE: isValidRatio(a) => not(gtRatio(a, a))
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  gtRatio a a = false ]

-- GT_ANTISYMMETRIC: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) => not(gtRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a b = true →
  gtRatio b a = false ]

-- GT_TRANSITIVE: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) => gtRatio(b, c) => gtRatio(a, c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a b = true → gtRatio b c = true →
  gtRatio a c = true ]

-- GT_IMP_LT: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) => ltRatio(b, a)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a b = true →
  ltRatio b a = true ]

-- GT_IMP_NOT_LEQ: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) => not(leqRatio(a, b))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a b = true →
  leqRatio a b = false ]

-- GT_IMP_NOT_GEQ: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) => not(geqRatio(b, a))
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → gtRatio a b = true →
  geqRatio b a = false ]

-- GT_LT_IFF: isValidRatio(a) => isValidRatio(b) => gtRatio(a, b) = ltRatio(b, a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (gtRatio a b == ltRatio b a) = true ]

-- GEQ_LEQ_IFF: isValidRatio(a) => isValidRatio(b) => geqRatio(a, b) = leqRatio(b, a)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (geqRatio a b == leqRatio b a) = true ]

end Tests.Ratio.Misc
