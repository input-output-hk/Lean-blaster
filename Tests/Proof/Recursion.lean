import Blaster
import Tests.Proof.Support

namespace Tests.Recursion
def count : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + count xs

open Lean Elab Tactic
elab "constructor_blaster" : tactic => do
  Blaster.Optimize.withUninterpretedRecursion #[``count] <|
    evalTactic (← `(tactic| blaster (timeout: 10)))

example : count [] = 0 := by constructor_blaster
example (x : Nat) (xs : List Nat) : count (x :: xs) = 1 + count xs := by
  constructor_blaster

#reject "Goal was falsified" in
example (xs : List Nat) : count xs = 0 := by constructor_blaster
end Tests.Recursion
