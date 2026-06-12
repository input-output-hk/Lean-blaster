import Blaster

namespace Test.SmtBitVecDiv

/-! # Test cases to validate BitVec division semantics (Lean: x/0 = 0) -/

#blaster [∀ (x : BitVec 8), x / 0#8 = 0#8]

#blaster [∀ (x : BitVec 8), x % 0#8 = x]

#blaster [∀ (x : BitVec 8), x / 1#8 = x]

#blaster [∀ (x y : BitVec 8), y ≠ 0#8 → x / y ≤ x]

#blaster [∀ (x y : BitVec 8), y ≠ 0#8 → x % y < y]

#blaster [∀ (x : BitVec 8), x.sdiv 0#8 = 0#8]

#blaster [∀ (x : BitVec 8), x.smod 0#8 = x]

#blaster [∀ (x : BitVec 8), x.srem 0#8 = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x / 0#8 = 255#8]
