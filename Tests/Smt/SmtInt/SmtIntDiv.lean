import Blaster
namespace Test.SmtIntDiv

/-! # Test cases to validate Int8 (signed) division and modulo semantics
    Path A: Int8.div → BitVec.sdiv (wrapped for x/0=0), Int8.mod → BitVec.srem (T-division) -/

-- div by one: identity
#blaster [∀ (x : Int8), x / 1 = x]

-- exact division: -6 / 2 = -3 (same for all rounding directions)
#blaster [((-6 : Int8)) / 2 = -3]

-- NON-EXACT division: -7 / 2 = -3 (T-division toward zero = -3; F-division would give -4)
-- This verifies that Lean's T-division (truncation) is correctly mapped to BitVec.sdiv
-- Lean: #eval ((-7 : Int8)) / 2  => -3
#blaster [((-7 : Int8)) / 2 = -3]

-- div by zero: Lean Int8 x/0 = 0 (SMT bvsdiv would give allOnes; wrapper corrects this)
#blaster [∀ (x : Int8), x / 0 = 0]

-- mod by zero: Lean Int8 x%0 = x (Int8.mod uses BitVec.srem; SMT bvsrem with divisor 0 = dividend)
#blaster [∀ (x : Int8), x % 0 = x]

-- signed remainder: T-division means remainder has same sign as dividend
-- Lean: #eval ((-7 : Int8)) % 2  => -1
#blaster [((-7 : Int8)) % 2 = -1]
