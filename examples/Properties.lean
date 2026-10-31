import Blaster

namespace CliDemo

-- A tactic invocation, captured under its enclosing declaration.
theorem reflexive (n : Nat) : n = n := by blaster

-- A false property with concrete counterexample inputs.
def subtractionRoundTrip : Prop :=
  ∀ a b : Nat, a - b + b = a

#blaster (solve-result: 1) [subtractionRoundTrip]

-- A true property deliberately left unresolved by stopping before SMT solving.
#blaster (only-optimize: 1) (solve-result: 2)
  [∀ a b c : Nat, a < b → b < c → a < c]

end CliDemo
