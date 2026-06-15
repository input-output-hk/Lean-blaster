import Blaster

namespace Test.SmtArraySort

open Blaster

/-! # Test cases to validate SMTArray sort translation -/

#blaster [∀ (a b : SMTArray Int), a = b → b = a]

#blaster [∀ (a : SMTArray (BitVec 8)), a = a]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : SMTArray Int), a = b]

-- Regression: two distinct element sorts in one query must not cause Z3 redefinition errors.
#blaster [∀ (a : SMTArray Int) (b : SMTArray (BitVec 8)), a = a ∧ b = b]
