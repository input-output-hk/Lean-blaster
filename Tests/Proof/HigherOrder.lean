import Blaster
import Tests.Proof.Support

/-!
Higher-order values stored inside constructors must retain their function-type
declarations when the translator applies a constructor field.
-/

namespace Tests.HigherOrder

theorem option_map_bind {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) (x : α) (y : β) :
    ((some x).map f).bind (fun g => (some y).map g) = some (f x y) := by
  blaster

-- The original upstream regression: list induction leaves a function-valued
-- Option in the zipWith equation.
theorem getElem_zipWith {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ)
    (l₁ : List α) (l₂ : List β) (i : Nat) :
    (List.zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind (fun g => l₂[i]?.map g) := by
  induction l₁ generalizing l₂ i <;> blaster

-- Reaching the higher-order encoding must still refute a false claim.
#reject "Goal was falsified" in
theorem option_map_bind_false {α β : Type} (f : α → β → Bool) (x : α) (y : β) :
    ((some x).map f).bind (fun g => (some y).map g) = some true := by
  blaster (timeout: 10)

#print axioms option_map_bind
#print axioms getElem_zipWith

end Tests.HigherOrder
