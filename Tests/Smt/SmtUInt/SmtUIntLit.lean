import Blaster

namespace Test.SmtUIntLit

#blaster [∀ (x : UInt8), x = 254 → x ≠ 255]

#blaster [∀ (x : UInt8), x = 5 → x.toBitVec = 5#8]

#blaster [(5 : UInt8).toBitVec = 5#8]

#blaster [(256 : UInt8) = 0]

#blaster [∀ (x : Int8), x = 5 → x ≠ 6]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x ≠ 200]

-- USize literals: System.Platform.numBits is opaque → special platform-width literal path
#blaster [∀ (x : USize), x = 5 → x ≠ 6]

-- ISize literals: double-wrapped (ISize.ofUSize (USize.ofBitVec …)) — recursion unwinds
#blaster [∀ (x : ISize), x = 5 → x ≠ 6]

end Test.SmtUIntLit
