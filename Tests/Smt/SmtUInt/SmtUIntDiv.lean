import Blaster
namespace Test.SmtUIntDiv

/-! # Test cases to validate UInt division and modulo semantics
    Path A: UInt8.div → BitVec.udiv (wrapped for x/0=0), UInt8.mod → BitVec.umod -/

-- div by zero: Lean UInt8 x/0 = 0 (SMT bvudiv would give allOnes; wrapper corrects this)
#blaster [∀ (x : UInt8), x / 0 = 0]

-- mod by zero: Lean UInt8 x%0 = x (SMT bvurem with divisor 0 natively returns dividend)
#blaster [∀ (x : UInt8), x % 0 = x]

-- div by one: identity
#blaster [∀ (x : UInt8), x / 1 = x]

-- remainder strictly less than divisor (unsigned)
#blaster [∀ (x y : UInt8), y ≠ 0 → x % y < y]

-- falsifiable: x/0 = 255 is false (Lean gives 0, not allOnes)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x / 0 = 255]
