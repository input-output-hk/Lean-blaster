import Blaster

namespace Test.SmtBitVecStructure

/-! # Test cases to validate BitVec concat/extract/extend/rotate -/

#blaster [∀ (x : BitVec 8), (0#8 ++ x).extractLsb 7 0 = x]

#blaster [(0xAB#8 ++ 0xCD#8 : BitVec 16) = 0xABCD#16]

#blaster [∀ (x : BitVec 8), x.zeroExtend 16 ≤ 255#16]

-- signExtend of a negative value keeps the sign
#blaster [(255#8).signExtend 16 = 0xFFFF#16]

#blaster [(255#8).zeroExtend 16 = 0x00FF#16]

-- setWidth grows (zero-extends) and shrinks (truncates)
#blaster [(255#8).setWidth 16 = 0x00FF#16]

#blaster [(0xABCD#16).setWidth 8 = 0xCD#8]

#blaster [∀ (x : BitVec 8), x.rotateLeft 8 = x]

#blaster [(0x81#8).rotateLeft 1 = 0x03#8]

#blaster [(0x81#8).rotateRight 1 = 0xC0#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x.rotateLeft 1 = x]
