import Blaster

namespace Test.SmtNatBitwise

/-! ## Test objectives to validate `Nat.land`, `Nat.lor` and `Nat.xor` with backend solver -/

/-! # Constant folding -/

#blaster (only-optimize: 1) [(0xf0 &&& 0x3c) ||| 0x01 = 0x31]

#blaster (only-optimize: 1) [0xff ^^^ 0x0f = 0xf0]

/-! # Identities -/

#blaster (only-optimize: 1) [∀ (x : Nat), x &&& 0 = 0]

#blaster (only-optimize: 1) [∀ (x : Nat), x ||| 0 = x]

#blaster (only-optimize: 1) [∀ (x : Nat), x ^^^ 0 = x]

#blaster (only-optimize: 1) [∀ (x : Nat), x &&& x = x]

#blaster (only-optimize: 1) [∀ (x : Nat), x ||| x = x]

#blaster (only-optimize: 1) [∀ (x : Nat), x ^^^ x = 0]

#blaster (only-optimize: 1) [∀ (x y : Nat), x &&& y = y &&& x]

/-! # Masks are rewritten to arithmetic -/

-- low mask: `x &&& (2^k - 1) = x % 2^k`
#blaster (only-optimize: 1) [∀ (x : Nat), x &&& 0xff = x % 256]

#blaster [∀ (x : Nat), x &&& (2^160 - 1) = x % 2^160]

-- contiguous mask: `x &&& (2^m - 2^k) = 2^k * ((x % 2^m) / 2^k)`
#blaster [∀ (x : Nat), x &&& 0xff00 = 256 * ((x % 65536) / 256)]

#blaster [∀ (x : Nat), x < 2^256 → x &&& (2^256 - 2^160) = x - x % 2^160]

/-! # Operands with disjoint bits: `|||` and `^^^` become `+`, `&&&` becomes `0` -/

#blaster (only-optimize: 1) [∀ (x y : Nat), (256 * x) ||| (y % 256) = 256 * x + y % 256]

#blaster (only-optimize: 1) [∀ (x y : Nat), (256 * x) ^^^ (y % 256) = 256 * x + y % 256]

#blaster (only-optimize: 1) [∀ (x y : Nat), (256 * x) &&& (y % 256) = 0]

-- read-modify-write of a 160-bit field in a 256-bit word (Solidity's storage packing)
#blaster [∀ (old new : Nat), old < 2^256 → new < 2^256 →
  ((old &&& (2^256 - 2^160)) ||| (new &&& (2^160 - 1))) &&& (2^160 - 1) = new % 2^160]

#blaster [∀ (old new : Nat), old < 2^256 → new < 2^256 →
  ((old &&& (2^256 - 2^160)) ||| (new &&& (2^160 - 1))) / 2^160 = old / 2^160]

-- a mask with two runs of ones (Solidity clearing one packed field: `not(shl(160, 0xff))`)
#blaster (only-optimize: 1) [∀ (x : Nat),
  x &&& (2^256 - 1 - 255 * 2^160) = x % 2^160 + 2^168 * ((x % 2^256) / 2^168)]

-- writing a packed byte field and reading the neighbours back
#blaster [∀ (old b : Nat), old < 2^256 → b < 256 →
  let new := (old &&& (2^256 - 1 - 255 * 2^160)) ||| (b * 2^160)
  new % 2^160 = old % 2^160 ∧ (new / 2^160) % 256 = b ∧ new / 2^168 = old / 2^168]

-- `x % m` for `m` not a power of two does not keep the bits of `x` (4 % 3 = 1)
#blaster [∀ (x : Nat), x = 4 → (x % 3) &&& 1 = 1]

/-! # Bit fields: `% 2^k` and `/ 2^k` of sums of parts with known bit positions -/

#blaster (only-optimize: 1) [∀ (x y : Nat), (x + y * 2^8) % 2^8 = x % 2^8]

#blaster (only-optimize: 1) [∀ (x y : Nat), (x % 2^8 + y * 2^8) / 2^8 = y]

#blaster (only-optimize: 1) [∀ (x y : Nat), (x % 2^8 + 2^16 * y) / 2^8 = 2^8 * y]

-- bounds from the hypotheses count as bit positions
#blaster (only-optimize: 1) [∀ (x y : Nat), x < 2^8 → (x + y * 2^8) / 2^8 = y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x + y * 2^8) % 2^9 = x % 2^9]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x + y * 2^8) / 2^8 = y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x % 2^9 + y * 2^8) / 2^8 = y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x % 2^9 + y * 2^8) / 2^9 = y / 2]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), (x % 6) / 4 = 0]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (old b : Nat), old < 2^256 → b < 512 →
  let new := (old &&& (2^256 - 1 - 255 * 2^160)) ||| (b * 2^160)
  new / 2^168 = old / 2^168]

/-! # Adjacent bit fields of the same value merge (a word read byte by byte) -/

#blaster (only-optimize: 1) [∀ (x : Nat), ((x / 2^8) % 2^8) * 2^8 + x % 2^8 = x % 2^16]

#blaster (only-optimize: 1) [∀ (x : Nat),
  ((x / 2^16) % 2^8) * 2^24 + ((x / 2^8) % 2^8) * 2^16 + (x % 2^8) * 2^8 = (x % 2^24) * 2^8]

#blaster (only-optimize: 1) [∀ (x : Nat), x < 2^24 →
  (x / 2^16) * 2^16 + ((x / 2^8) % 2^8) * 2^8 + x % 2^8 = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), ((x / 2^9) % 2^8) * 2^8 + x % 2^8 = x % 2^16]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), ((x / 2^8) % 2^8) * 2^9 + x % 2^8 = x % 2^16]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ((y / 2^8) % 2^8) * 2^8 + x % 2^8 = x % 2^16]

/-! # Remaining applications use the exact recursive Smt definitions -/

#blaster (timeout: 10) [∀ (x : Nat), x < 4 → x &&& 5 = x % 2]

#blaster (timeout: 10) [∀ (x y : Nat), x < 4 → y < 4 → x ^^^ y < 4]

-- NOTE: requires induction over the recursive definition
#blaster (timeout: 5) (solve-result: 2) [∀ (x y : Nat), x &&& y ≤ x]

/-! # A value below the modulus is not changed by `%` (bound taken from the hypotheses) -/

#blaster (only-optimize: 1) [∀ (x : Nat), x < 2^160 → x &&& (2^160 - 1) = x]

#blaster (only-optimize: 1) [∀ (x y : Nat), x < 2^256 → y = x % 2^256 → y = x]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x ^^^ y = x ||| y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x &&& y = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x &&& 0xff00 = x % 65536]

end Test.SmtNatBitwise
