import Blaster

namespace Test.SmtBitVecArith

/-! # Test cases to validate BitVec arithmetic/bitwise semantics -/

#blaster [∀ (x y : BitVec 8), x + y = y + x]

#blaster [∀ (x y z : BitVec 8), (x + y) + z = x + (y + z)]

#blaster [∀ (x : BitVec 8), x + 0#8 = x]

-- wrap-around: adding 255 is subtracting 1 mod 2^8
#blaster [∀ (x : BitVec 8), x + 255#8 = x - 1#8]

#blaster [∀ (x : BitVec 8), x - x = 0#8]

#blaster [∀ (x : BitVec 8), -x = 0#8 - x]

#blaster [∀ (x y : BitVec 8), x * y = y * x]

-- de Morgan
#blaster [∀ (x y : BitVec 8), ~~~(x &&& y) = ~~~x ||| ~~~y]

#blaster [∀ (x : BitVec 8), x ^^^ x = 0#8]

#blaster [∀ (x : BitVec 8), x &&& 255#8 = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x + y = x]
