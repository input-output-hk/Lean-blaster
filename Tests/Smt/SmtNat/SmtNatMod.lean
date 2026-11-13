import Blaster

namespace Test.SmtNatMod

/-! ## Test objectives to validate `Nat.mod` semantics with backend solver -/

/-! # Test cases to validate `Nat.mod` semantics with backend solver -/

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat),  x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x : Nat), x % 0 = x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x : Nat), x % x = 0]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x : Nat), x % 1 = 0]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), x < y → x % y = x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x : Nat), 1 % x = 0 ↔ x = 1]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x : Nat), (0 = 1 % x ↔ x = 1)]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), x ≥ y → x % y = (x - y) % y]

/-- A named reconstruction example whose proof can be inspected in the Infoview. -/
theorem mod_lt (x y : Nat) (h : 0 < y) : x % y < y := by
  blaster (gen-proof: 1) (timeout: 10)

-- Count the proof including generated auxiliary lemmas, without printing it.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let root := ``mod_lt
  let info ← getConstInfo root
  let proof ← deltaExpand info.value! (fun n => root.isPrefixOf n)
  let (nodes, _) := Blaster.Reconstruct.SmtProof.dagStats proof
  logInfo m!"mod_lt proof: {nodes} distinct nodes"

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), 0 < x → x - y % x + y % x = x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), x % y ≤ x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), x % y + y * (x / y) = x]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), x % y = x - y * (x / y)]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), (x + y) % y = x % y]

#blaster (gen-proof: 1) (timeout: 10) (random-seed: 2) [∀ (x y z : Nat), (x + y * z) % y = x % y]

#blaster (gen-proof: 1) (timeout: 10) [∀ (x y : Nat), (x * y) % x = 0]

#blaster (gen-proof: 1) (timeout: 10) (random-seed: 3) [∀ (x y z : Nat), (z * x) % (z * y) = z * (x % y)]


/-! # Test cases to ensure that counterexample are properly detected -/


#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → x % y ≠ x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 1 → x % y ≠ 0]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y ≥ y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x ≥ y → x % y ≠ (x - y) % y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y > x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y + y * (x / y) ≠ x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x + y) % y ≠ x % y]

end Test.SmtNatMod
