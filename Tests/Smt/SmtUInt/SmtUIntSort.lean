import Blaster

namespace Test.SmtUIntSort

/-! # Test cases to validate UInt/Int sort translation -/

#blaster [∀ (x y : UInt8), x = y → y = x]

#blaster [∀ (x : UInt32) (y : UInt64), x = x ∧ y = y]

#blaster [∀ (x y : Int8), x = y → y = x]

#blaster [∀ (x : USize), x = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : UInt8), x = y]

-- Regression: same-width mixed types share (_ BitVec 8) but use distinct qualifier names
-- so Z3 must not see duplicate define-fun for the predicate
#blaster [∀ (a : UInt8) (b : Int8) (c : BitVec 8), a = a ∧ b = b ∧ c = c]
