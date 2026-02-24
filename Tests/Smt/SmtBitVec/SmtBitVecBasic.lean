import Solver.Command.Syntax

namespace Test.SmtBitVecBasic

/-! ## Test objectives to validate `BitVec` semantics with the backend solver -/

/-! # Test cases to validate `BitVec` domain -/

#solve [∀ (x : BitVec 8), x = x]

/-! # Test cases to validate `BitVec.add` semantics -/

#solve (only-optimize: 1) [∀ (x y : BitVec 8), x + y = y + x]

#solve [∀ (x y z : BitVec 8), (x + y) + z = x + (y + z)]

#solve [∀ (x : BitVec 8), x + 0 = x]

#solve [∀ (x : BitVec 8), 0 + x = x]

/-! # Test cases to validate `BitVec.sub` semantics -/

#solve [∀ (x : BitVec 8), x - 0 = x]

#solve [∀ (x : BitVec 8), x - x = 0]

/-! # Test cases to validate `BitVec.mul` semantics -/

#solve [∀ (x y : BitVec 8), x * y = y * x]

#solve [∀ (x : BitVec 8), x * 1 = x]

#solve [∀ (x : BitVec 8), x * 0 = 0]

/-! # Test cases to validate bitwise operations -/

#solve [∀ (x : BitVec 8), x &&& x = x]

#solve [∀ (x : BitVec 8), x ||| x = x]

#solve [∀ (x : BitVec 8), x ^^^ x = 0]

#solve [∀ (x : BitVec 8), x &&& 0 = 0]

#solve [∀ (x : BitVec 8), x ||| 0 = x]

/-! # Test cases to validate `BitVec` comparisons -/

#solve [∀ (x y : BitVec 8), BitVec.ult x y ↔ ¬ BitVec.ule y x]

/-! # Test cases to ensure that counterexamples are properly detected -/

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x + y = x]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≠ x]

end Test.SmtBitVecBasic
