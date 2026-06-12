import Blaster

namespace Test.SmtBitVecCompare

/-! # Test cases to validate BitVec comparison semantics -/

#blaster [∀ (x y : BitVec 8), x < y → ¬ (y < x)]

#blaster [∀ (x y : BitVec 8), x ≤ y ∨ y ≤ x]

#blaster [∀ (x : BitVec 8), x ≤ 255#8]

#blaster [∀ (x y : BitVec 8), x.ult y → x ≠ y]

-- signed: 255#8 is -1, so slt 0
#blaster [(255#8).slt 0#8 = true]

#blaster [∀ (x y : BitVec 8), x.sle y ∨ y.sle x]

-- CRITICAL soundness guards: wrap-around breaks Int-style order reasoning.
-- These MUST be Falsified; if any reports Valid, BitVec leaked into the
-- relational rewriting rules (see relationalCompatibleTypes).
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≤ x + 1#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x < x + 1#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x < y → x + 1#8 ≤ y + 1#8]

-- mixed Nat and BitVec comparisons in one goal must not share SMT symbols
-- (funInstCache collision regression)
-- LE.le tests: optimizer rewrites ≤ to ¬(<), so no cache collision via LE.le path
#blaster [∀ (n : Nat) (x : BitVec 8), n ≤ n + 1 → x ≤ 255#8]

#blaster [∀ (x : BitVec 8) (n : Nat), x ≤ 255#8 → n ≤ n + 1]

-- LT.lt collision reproducer: BitVec < first caches bvultSymbol under LT.lt;
-- without Fix 1 the Nat < operands then get bvult, causing a Z3 wrong-sort error.
-- Must be Falsified (a=0,b=255,n=0,m=1 is a counterexample).
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : BitVec 8) (n m : Nat), a < b → n < m → a < b + 1#8]
