import Solver.Command.Syntax

namespace Test.SmtBitVecBasic

/-! ## Test objectives to validate `BitVec` semantics with the backend solver -/

/-! # Test cases to validate `BitVec` domain -/

#solve [∀ (x : BitVec 8), x = x]

/-! # Test cases to validate `BitVec.add` semantics -/

#solve (only-optimize: 1) [∀ (x y : BitVec 8), x + y = y + x]

#solve [∀ (x y z : BitVec 8), (x + y) + z = x + (y + z)]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x + 0 = x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), 0 + x = x]

/-! # Test cases to validate `BitVec.sub` semantics -/

#solve (only-optimize: 1) [∀ (x : BitVec 8), x - 0 = x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x - x = 0]

/-! # Test cases to validate `BitVec.mul` semantics -/

#solve (only-optimize: 1) [∀ (x y : BitVec 8), x * y = y * x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x * 1 = x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x * 0 = 0]

/-! # Test cases to validate bitwise operations -/

#solve (only-optimize: 1) [∀ (x : BitVec 8), x &&& x = x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x ||| x = x]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x ^^^ x = 0]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x &&& 0 = 0]

#solve (only-optimize: 1) [∀ (x : BitVec 8), x ||| 0 = x]

/-! # Test cases to validate `BitVec` comparisons -/

#solve (only-optimize: 1) [∀ (x y : BitVec 8), BitVec.ult x y ↔ ¬ BitVec.ule y x]

/-! # Test cases to ensure that counterexamples are properly detected -/

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x + y = x]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≠ x]

#solve (solve-result: 1) (gen-cex: 0) [∀ (x y : BitVec (4 + 3)), x + y = y - x]
end Test.SmtBitVecBasic
