import Blaster
import Tests.Proof.Support

/-! Kernel proofs justify the changed arithmetic and quantified-image expectations. -/
namespace Tests.Normalization

example (x : Nat) : (100 + x) - 101 = x - 1 := by omega
example (x : Nat) : (100 + x) - 180 = x - 80 := by omega
example (x : Nat) : (2 + x) - 4 = x - 2 := by omega

theorem quantified_toNat_image (p : Nat → Prop) :
    (∀ i : Int, p i.toNat) ↔ ∀ n : Nat, p n := by
  constructor
  · intro h n
    simpa using h (Int.ofNat n)
  · intro h i
    exact h i.toNat

-- Retaining a conditional inside any constructor preserves its value.
theorem constructor_choice {α β : Type} (ctor : α → β) (c : Prop)
    (yes no : α) [Decidable c] :
    ctor (if c then yes else no) =
      Blaster.dite' c (fun _ => ctor yes) (fun _ => ctor no) := by
  symm
  dsimp [Blaster.dite']
  split
  · rename_i h
    have hc : c := (Blaster.decide'_true c).mp h
    simp [hc]
  · rename_i h
    have hc : ¬ c := (Blaster.decide'_false c).mp h
    simp [hc]

-- Observing the integer itself must prevent image-binder replacement.
#reject "Goal was falsified" in
example : ∀ i : Int, i.toNat = 0 → i = 0 := by
  blaster (timeout: 10)

-- A runtime lambda retains its Int domain.
example : (fun i : Int => i.toNat) (-1) = 0 := by blaster

#print axioms quantified_toNat_image
#print axioms constructor_choice
end Tests.Normalization
