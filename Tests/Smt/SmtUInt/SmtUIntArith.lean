import Blaster
namespace Test.SmtUIntArith

#blaster [∀ (x y : UInt8), x + y = y + x]
#blaster [∀ (x : UInt8), x + 0 = x]
#blaster [∀ (x : UInt8), x + 255 = x - 1]
#blaster [∀ (x y : UInt8), x &&& y = y &&& x]
#blaster [∀ (x : UInt8), x ^^^ x = 0]
#blaster [∀ (x y : UInt8), x < y → ¬ (y < x)]
#blaster [∀ (x : UInt8), x ≤ 255]
#blaster [∀ (x : UInt8), x <<< 1 = x * 2]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : UInt8), x + y = x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x ≤ x + 1]
