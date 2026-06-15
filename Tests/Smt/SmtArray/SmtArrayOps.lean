import Blaster

namespace Test.SmtArrayOps

open Blaster

/-! # Test cases to validate SMTArray get/set (array theory) -/

#blaster [∀ (a : SMTArray Int) (i : Nat) (v : Int), (a.set i v).get i = v]

#blaster [∀ (a : SMTArray Int) (i j : Nat) (v : Int), i ≠ j → (a.set i v).get j = a.get j]

#blaster [∀ (a : SMTArray Int) (i : Nat) (v w : Int), ((a.set i v).set i w).get i = w]

#blaster [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), (a.set i v).get i = v]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i j : Nat) (v : Int), (a.set i v).get j = v]
