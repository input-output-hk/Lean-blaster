import Blaster

namespace Test.SmtBitVecFold

/-! # Test cases to validate BitVec constant folding (only-optimize: no solver) -/

#blaster (only-optimize: 1) [(200#8 + 100#8 : BitVec 8) = 44#8]

#blaster (only-optimize: 1) [(255#8 &&& 15#8 : BitVec 8) = 15#8]

#blaster (only-optimize: 1) [(~~~0#8 : BitVec 8) = 255#8]

#blaster (only-optimize: 1) [(7#8 * 100#8 : BitVec 8) = 188#8]

#blaster (only-optimize: 1) [(5#8 / 0#8 : BitVec 8) = 0#8]

#blaster (only-optimize: 1) [∀ (x : BitVec 8), x + 0#8 = x]

#blaster (only-optimize: 1) [∀ (x : BitVec 8), 0#8 ||| x = x]

#blaster (only-optimize: 1) [∀ (x : BitVec 8), x * 0#8 = 0#8]

#blaster (only-optimize: 1) [∀ (x : BitVec 8), x ^^^ x = 0#8]

#blaster (only-optimize: 1) [∀ (x : BitVec 8), x - x = 0#8]

end Test.SmtBitVecFold
