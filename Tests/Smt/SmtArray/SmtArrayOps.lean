import Blaster

namespace Test.SmtArrayOps

open Blaster

/-! # Test cases to validate SMTArray get/set (array theory) -/

#blaster [∀ (a : SMTArray Int) (i j : Nat) (v : Int), i ≠ j → (a.set i v).get j = a.get j]

-- out-of-bounds set is a no-op, so unguarded double-write is NOT valid; with in-bounds guard it IS valid
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i : Nat) (v w : Int), ((a.set i v).set i w).get i = w]
#blaster [∀ (a : SMTArray Int) (i : Nat) (v w : Int), i < a.size → ((a.set i v).set i w).get i = w]

-- out-of-bounds set is a no-op for BitVec 8 elements too
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), (a.set i v).get i = v]
#blaster [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), i < a.size → (a.set i v).get i = v]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i j : Nat) (v : Int), (a.set i v).get j = v]

/-! ## Documented limitation: no size/`default` modeling (spec §SMTArray).

SMT arrays are total over `Int`; we do not model `Array.size` or the `default`
returned by `getD` out of bounds. A read from an unwritten index is an
*unconstrained* (but type-qualified) element, NOT provably `default`. This is an
over-approximation in the safe direction: a property depending on the `default`
value is not proven (Falsified/Undetermined — a spurious counterexample, never a
false proof). The test pins that we do NOT wrongly prove an unwritten element
equals a particular value. -/
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i : Nat), a.get i = 0]

-- SOUND: out-of-bounds set is a no-op, so the unguarded statement is NOT valid (countermodel exists)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i : Nat) (v : Int), (a.set i v).get i = v]
-- SOUND positive: with an in-bounds guard it IS valid
#blaster [∀ (a : SMTArray Int) (i : Nat) (v : Int), i < a.size → (a.set i v).get i = v]
