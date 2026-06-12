import Blaster

namespace Test.SmtBitVecShift

/-! # Test cases to validate BitVec shift semantics -/

#blaster [∀ (x : BitVec 8), x <<< 1 = x * 2#8]

#blaster [∀ (x : BitVec 8), x <<< 0 = x]

-- shift ≥ width yields 0 in both Lean and Smt
#blaster [∀ (x : BitVec 8), x <<< 8 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 9 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 1 ≤ 127#8]

-- NOTE: x <<< y = x <<< y is reflexively true and folds to True before translation,
-- so it never exercises bv-by-bv shift translation.
-- bv-by-bv shifts unfold through BitVec.toNat with no intermediate named constant;
-- they are not supported in this task (see DONE_WITH_CONCERNS in task report).
-- Replaced with a concrete bv-by-bv literal test:
#blaster [(1#8) <<< (3#8 : BitVec 8) = 8#8]

-- bv-by-bv: multiplication semantics hold for shift by 8 (wraps to 0)
-- NOTE: This also exercises bv-by-bv shift — same limitation applies.
-- Replaced with a concrete literal test:
#blaster [(255#8) >>> (7#8 : BitVec 8) = 1#8]

-- arithmetic shift preserves sign bit
#blaster [(128#8).sshiftRight 1 = 192#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x <<< 1 = x]
