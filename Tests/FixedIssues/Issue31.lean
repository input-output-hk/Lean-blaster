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
-- and we can't provide an instance for β. Therefore we can't derive
-- false from the hypothesis.
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

-- Can be proved due to false hypothesis
theorem sort_unification_thm4 :
  (∀ (β : Type u) (x : β) (f : β → Nat), f x > 10) →
  (∀ (α : Type v) (x : α) (f : α → Nat), f x > 10) := by
   intro h1 α x f
   have h2 := h1 PUnit ⟨⟩ (λ _ => 0)
   simp at h2

-- Valid expected by blaster
#blaster (solve-result: 0) [sort_unification_thm4]

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

-- Can be proved due to false hypothesis
theorem sort_unification_thm7 :
  (∀ (α : Type u) (β : Type v) (x : α) (f : α → β) (g : β → Nat), g (f x) > 10) →
  (∀ (A : Type u) (B : Type (v + 1)) (x : A) (m : A → B) (n : B → Nat), n (m x) > 10) := by
  intro h1 α β x f g
  have h2 := h1 PUnit PUnit ⟨⟩ (λ _ => ⟨⟩) (λ _ => 0)
  simp at h2

-- Valid expected by blaster
#blaster (solve-result: 0) (random-seed: 1) [sort_unification_thm7]

-- Counterexample expected as β and α are within the same scope and
-- therefore represent different types. Moreover, we can't provide an instance for B.
-- Hence, we can't derive false from the hypothesis.
variable (B : Type u)
theorem sort_unification_thm8 :
  (∀ (x : B) (f : B → Nat), f x > 10) →
  (∀ (α : Type u) (x : α) (f : α → Nat), f x > 10) := by sorry
  -- intro h α x f
  -- apply h x f -- can't apply h

#blaster (gen-cex: 0) (solve-result: 1) [sort_unification_thm8]


theorem exists_must_match_forall :
  ∀ (α : Type u), (∃ (β : Type u), α = β) := by
  intro α
  exact ⟨α, rfl⟩

#blaster [exists_must_match_forall]

theorem exist_nat_type : ∃ (α : Type), α = Nat := by exact ⟨Nat, rfl⟩

#blaster [exist_nat_type]

theorem exist_nat_type_with_instance: ∃ (a : Type) (_x : a), a = Nat := by exists Nat; exists 0
#blaster [exist_nat_type_with_instance]

-- Counterexample expect as there is no instance for Empty
theorem exist_empty_type_with_instance : ∃ (a : Type) (x : a), a = Empty := by sorry
  -- exists Empty;
  -- can't provide an instance for x
#blaster (gen-cex: 0) (solve-result: 1) [exist_empty_type_with_instance]

theorem exist_type_with_instance : ∀ (b : Type), ∃ (a : Type) (_x : a), a = b := by sorry
  -- intro b
  -- exists b;
  -- can't provide an instance for x
#blaster (gen-cex: 0) (solve-result: 1) [exist_type_with_instance]

theorem exist_list_nat_type : ∃ (a : Type), a = List Nat := by exists (List Nat)
#blaster [exist_list_nat_type]

theorem exist_list_nat_type_with_instance : ∃ (a : Type) (_x: a), a = List Nat := by exists (List Nat); exists []
#blaster [exist_list_nat_type_with_instance]

theorem exist_list_gen_type_with_instance : ∀ (b : Type), ∃ (a : Type) (_x: a), a = List b := by
  intro b;
  exists (List b); exists []

#blaster [exist_list_gen_type_with_instance]

theorem exist_punit_type_1 : ∃ (α : Type), α = PUnit := by exact ⟨PUnit, rfl⟩
#blaster [exist_punit_type_1]

theorem exist_punit_type_2 : ∃ (α : Type u), α = PUnit := by exact ⟨PUnit, rfl⟩
#blaster [exist_punit_type_2]

theorem exist_punit_type_3 : ∃ (α : Type (u + 1)), α = PUnit := by exact ⟨PUnit, rfl⟩
#blaster [exist_punit_type_3]

theorem exist_punit_type_1_wth_instance : ∃ (α : Type) (_x : α), α = PUnit := by exists PUnit; exists ⟨⟩
#blaster [exist_punit_type_1_wth_instance]


theorem exist_punit_type_2_wth_instance : ∃ (α : Type u) (_x : α), α = PUnit := by exists PUnit; exists ⟨⟩
#blaster [exist_punit_type_2_wth_instance]

theorem exist_punit_type_3_wth_instance : ∃ (α : Type (u + 1)) (_x : α), α = PUnit := by exists PUnit; exists ⟨⟩
#blaster [exist_punit_type_3_wth_instance]

end Tests.Issue31
