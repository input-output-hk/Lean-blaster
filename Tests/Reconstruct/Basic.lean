import Blaster

example : ∀ {x : Nat}, 0 + x = x := by blaster

example : ∀ {x : Nat}, 0 + (0 + x) = x := by blaster
