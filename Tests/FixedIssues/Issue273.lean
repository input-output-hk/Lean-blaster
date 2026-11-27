import Lean
import Blaster
import Tests.Utils

namespace Tests.Issue273
-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/273
--        Smt translation error obtained when theorem makes reference to Nat.log2
-- Diagnosis: Nat.log2 is not a native recursive function. It uses Nat.rec recursor.
--            We need to opacify Nat.log2 and add a specific smt definition.

set_option warn.sorry false

/-- ! Constant evaluation -/
example : Nat.log2 8 = 3 := by blaster (only-optimize: 1)
example : Nat.log2 4096 = 12 := by blaster (only-optimize: 1)
example : Nat.log2 299 = 8 := by blaster (only-optimize: 1)


-- Counterexample expected by blaster
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [Nat.log2 100 = 1]

-- Counterexample expected by blaster
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [Nat.log2 4096 = 10]

-- Counterexample expected by blaster
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [Nat.log2 128 = 2]

/-- ! Validating Nat.log2 semantics -/
example (n : Nat) : n.log2 = if 2 ≤ n then (n / 2).log2 + 1 else 0 := by blaster

end Tests.Issue273
