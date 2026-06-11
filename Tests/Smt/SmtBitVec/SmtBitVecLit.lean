import Blaster

namespace Test.SmtBitVecLit

/-! # Test cases to validate BitVec literal translation -/

#blaster [∀ (x : BitVec 8), x = 254#8 → x ≠ 255#8]

#blaster [∀ (x : BitVec 8), x = 5#8 → x = 5#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≠ 200#8]

-- ofNat wraps modulo 2^w
#blaster [∀ (x : BitVec 8), x = 256#8 → x = 0#8]
