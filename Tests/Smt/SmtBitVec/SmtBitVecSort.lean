import Blaster

namespace Test.SmtBitVecSort

/-! # Test cases to validate BitVec sort translation -/

#blaster [∀ (x y : BitVec 8), x = y → y = x]

#blaster [∀ (x : BitVec 8) (y : BitVec 16), x = x ∧ y = y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x = y]
