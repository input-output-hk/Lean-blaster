import Lean
import Blaster

open Lean Meta
namespace Tests.Issue31

-- Issue: Unexpected Valid
-- Diagnosis: We need to create a unique type universe at the SMT level for each sort.

set_option warn.sorry false
-- Valid expected
theorem sort_unification_thm1 :
  (∀ (β : Type) (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type) (x : α) (f : α → Nat), f x > 10) := by
  intro h1 α x f
  apply h1 α x f

#blaster [sort_unification_thm1]

-- Counterexample expected as β has Type u while α has Type 1
theorem sort_unification_thm2 :
  (∀ (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type) (x : α) (f : α → Nat), f x > 10) := by sorry
   -- intro h1 α x f
   -- apply h1 α x f can't apply h1

#blaster (gen-cex: 0) (solve-result: 1) [sort_unification_thm2]

-- Valid expected
theorem sort_unification_thm3 :
  (∀ (β : Type u) (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type u) (x : α) (f : α → Nat), f x > 10) := by
   intro h1 α x f
   apply h1 α x f

#blaster [sort_unification_thm3]

-- Counterexample expected as β has Type u + 1 while α has Type v + 1
theorem sort_unification_thm4 :
  (∀ (β : Type u) (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type v) (x : α) (f : α → Nat), f x > 10) := by sorry
   -- intro h1 α x f
   -- apply h1 α x f can't apply h1

#blaster (gen-cex: 0) (solve-result: 1) [sort_unification_thm4]

-- Valid expected
theorem sort_unification_thm5 :
  (∀ (β : Type u) (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type u) (x : α) (f : α → Nat), f x > 10) := by
   intro h1 α x f
   apply h1 α x f

#blaster [sort_unification_thm5]

-- Valid expected
theorem sort_unification_thm6 :
  (∀ (α : Type u) (β : Type v) (x : α) (f : α → β) (g : β → Nat), g (f x) > 10) →
  (∀ (A : Type u) (B : Type v) (x : A) (m : A → B) (n : B → Nat), n (m x) > 10) := by
  intro h1 α β x f g
  apply h1 α β x f g

#blaster [sort_unification_thm6]

-- Counterexample expected as β has Type v + 1 while B has Type v + 2
theorem sort_unification_thm7 :
  (∀ (α : Type u) (β : Type v) (x : α) (f : α → β) (g : β → Nat), g (f x) > 10) →
  (∀ (A : Type u) (B : Type (v + 1)) (x : A) (m : A → B) (n : B → Nat), n (m x) > 10) := by sorry
  -- intro h1 α β x f g
  -- apply h1 α β x f g -- can't apply h1

#blaster (gen-cex: 0) (solve-result: 1) [sort_unification_thm7]

end Tests.Issue31
