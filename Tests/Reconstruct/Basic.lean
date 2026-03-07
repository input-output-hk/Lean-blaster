import Blaster.Reconstruct

open Blaster.Reconstruct

example (x : Nat) : x + 0 = x := by
  reconstruct [.Rewrite `Nat.add_zero]

example (x : Nat) : 0 + x = x := by
  reconstruct [.Rewrite `Nat.zero_add]

example (x : Nat) : 0 + x + 0 = x := by
  reconstruct [.Rewrite `Nat.zero_add, .Rewrite `Nat.add_zero]
