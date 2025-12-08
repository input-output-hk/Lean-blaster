import Lean
import Blaster

namespace Tests.Issue20

-- Issue: Unexpected counterexample
-- Diagnosis : We need to generate extensionality assertion for each HOF function
--             i.e., ∀ x, f x = g x → f = g

theorem funextEq {α β : Type} (f g : α → β) : (f = g) = ∀ x, f x = g x := by
      apply propext
      constructor
      { intro h ; simp only [h, implies_true] }
      { intro h ; apply funext h }

#blaster [funextEq]

end Tests.Issue20
