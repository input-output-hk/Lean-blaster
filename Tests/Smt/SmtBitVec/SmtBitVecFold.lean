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

-- Regression tests for Issue3 / BEqString: literal BitVec.toNat and literal
-- comparisons must fold in the optimizer (BitVec.toNat was made opaque for
-- bv-by-bv shifts; LT.lt/LE.le on BitVec was made opaque via isOpaqueRelational).
#blaster (only-optimize: 1) [(5#8).toNat = 5]

#blaster (only-optimize: 1) [(3#8 < 5#8)]

-- Signed comparison: 200#8 = -56 as Int8, so slt 5#8 = true
#blaster (only-optimize: 1) [((200#8).slt 5#8) = true]

-- String literal comparison exercises the String path (not BitVec fold directly)
#blaster (only-optimize: 1) ["ab" < "ac"]

end Test.SmtBitVecFold
