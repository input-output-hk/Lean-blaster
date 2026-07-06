import Lean
import Blaster

namespace Tests.Issue20

-- Issue: Unexpected counterexample
-- Diagnosis : We need to generate extensionality assertion for each HOF function
--             i.e., ∀ x, f x = g x → f = g

theorem funextEq_poly {α β : Type} (f g : α → β) : (f = g) = ∀ x, f x = g x := by
      apply propext
      constructor
      { intro h ; simp only [h, implies_true] }
      { intro h ; apply funext h }

#blaster [funextEq_poly]
#blaster (solver: cvc5) [funextEq_poly]

theorem funextEq_one_inst {β : Type} (f g : Nat → β) : (f = g) = ∀ x, f x = g x := by
      apply propext
      constructor
      { intro h ; simp only [h, implies_true] }
      { intro h ; apply funext h }

#blaster [funextEq_one_inst]
#blaster (solver: cvc5) [funextEq_one_inst]

theorem funextEq_two_inst (f g : Nat → Int) : (f = g) = ∀ x, f x = g x := by
      apply propext
      constructor
      { intro h ; simp only [h, implies_true] }
      { intro h ; apply funext h }

#blaster [funextEq_two_inst]
#blaster (solver: cvc5) [funextEq_two_inst]

end Tests.Issue20
