import Blaster

namespace Test.SmtUIntConv

-- Round-trip: widen UInt8 → UInt32 then narrow back → same value
#blaster [∀ (x : UInt8), x.toUInt32.toUInt8 = x]

-- Zero-extension bound: zero-extended value ≤ 255
#blaster [∀ (x : UInt8), x.toUInt32 ≤ 255]

-- Concrete zero-extend: 255 stays 255 (no sign bit set)
#blaster [(255 : UInt8).toUInt32 = 255]

-- Same-width reinterpret: 255 as UInt8 reinterpreted as Int8 = -1
#blaster [(255 : UInt8).toInt8 = -1]

-- Sign-extend: -1 as Int8 extended to Int16 stays -1
#blaster [((-1 : Int8)).toInt16 = -1]

-- Narrow: low byte of 0xABCD
#blaster [(0xABCD : UInt32).toUInt8 = 0xCD]

-- Falsified: UInt8 zero-extended to UInt32 cannot equal 256
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x.toUInt32 = 256]

-- Sign-extension discriminator (symbolic): negative Int8 stays negative after sign-extend to Int16
#blaster [∀ (x : Int8), x < 0 → x.toInt16 < 0]

-- Zero-extension: UInt8 zero-extended to UInt32 is always ≥ 0 (trivially true via Lean LE on UInt32,
-- but exercises the symbolic zero-extend path)
#blaster [∀ (x : UInt8), x.toUInt32 ≥ 0]

-- UInt8 → UInt16 round-trip
#blaster [∀ (x : UInt8), x.toUInt16.toUInt8 = x]

-- USize same-width identity: cannot force every UInt64 to equal 0 as USize
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt64), x.toUSize = 0]

-- USize widen: UInt8 zero-extended to USize cannot always equal 256
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x.toUSize = 256]

end Test.SmtUIntConv
