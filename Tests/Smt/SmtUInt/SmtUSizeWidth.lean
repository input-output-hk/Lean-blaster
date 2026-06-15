import Blaster
namespace Test.SmtUSizeWidth

-- default width 64: reflexivity always holds
#blaster [∀ (x : USize), x = x]

-- default width 64: zero literal
#blaster [(0 : USize) = 0]

-- explicit 32-bit: 2^32 wraps to 0 mod 2^32
#blaster (usize-width: 32) [(4294967296 : USize) = 0]

-- at the default 64-bit, 2^32 is NOT 0 (it fits in 64 bits)
#blaster (gen-cex: 0) (solve-result: 1) [(4294967296 : USize) = 0]

end Test.SmtUSizeWidth
