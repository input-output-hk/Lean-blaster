import Blaster

namespace Test.SmtBitVecShift

/-! # Test cases to validate BitVec shift semantics -/

#blaster [∀ (x : BitVec 8), x <<< 1 = x * 2#8]

#blaster [∀ (x : BitVec 8), x <<< 0 = x]

-- shift ≥ width yields 0 in both Lean and Smt
#blaster [∀ (x : BitVec 8), x <<< 8 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 9 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 1 ≤ 127#8]

-- BitVec-by-BitVec shifts
#blaster [∀ (x y : BitVec 8), x <<< y = x <<< y ||| 0#8]

#blaster [∀ (x : BitVec 8) (y : BitVec 8), 8#8 ≤ y → x <<< y = 0#8]

-- bv-by-bv right shift
#blaster [∀ (x y : BitVec 8), 1#8 ≤ y → x >>> y ≤ 127#8]

-- arithmetic shift preserves sign bit
#blaster [(128#8).sshiftRight 1 = 192#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x <<< 1 = x]
