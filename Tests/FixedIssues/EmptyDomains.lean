import Blaster
import Tests.Utils

namespace Tests.EmptyDomains

-- Kernel-checked counterexamples. None uses Blaster or sorry.
theorem empty_type_counterexample : ¬ (∀ α : Type, (∀ _ : α, False) → False) := by
  intro h
  exact h Empty Empty.elim

theorem empty_arrow_counterexample : ¬ (∀ α β : Type, (∀ _ : α → β, False) → False) := by
  intro h
  exact h Unit Empty (fun f => Empty.elim (f ()))

theorem empty_class_counterexample : ¬ (∀ α : Type, ∃ _ : Inhabited α, True) := by
  intro h
  obtain ⟨inst, _⟩ := h Empty
  exact Empty.elim inst.default

theorem erased_class_counterexample : ¬ (∀ α : Type, (∀ _ : Inhabited α, False) → False) := by
  intro h
  exact h Empty (fun inst => Empty.elim inst.default)

-- Preserve vacuous quantifiers both during optimization and SMT translation.
#testOptimize ["KeepEmptyTypeDomain"]
  (∀ α : Type, (∀ _ : α, False) → False) ===>
  (∀ α : Type, ¬ ∀ _ : α, False)
#testOptimize ["KeepEmptyClassDomain"]
  (∀ α : Type, ∃ _ : Inhabited α, True) ===>
  (∀ α : Type, ∃ _ : Inhabited α, True)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, (∀ _ : α, False) → False]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α β : Type, (∀ _ : α → β, False) → False]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, ∃ _ : Inhabited α, True]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, (∀ _ : Inhabited α, False) → False]

-- An instance encountered in an earlier, now closed binder must not provide
-- an inhabitant for a later binder over the same type.
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, (∀ _ : Inhabited α, True) → (∀ _ : α, False) → False]

-- Positive coverage: construct inhabitants of ordinary classes and functions
-- from their fields, rather than assuming that every class has an instance.
#testOptimize ["InhabitedRelationClass"]
  (∀ α : Type, ∃ _ : LT α, True) ===> True
#testOptimize ["InhabitedEqualityClass"]
  (∀ α : Type, ∃ _ : BEq α, True) ===> True

inductive Color where
  | red
inductive Box (α : Type) where
  | wrap : Color → Box α

#testOptimize ["InhabitedConstructorFields"]
  (∀ α : Type, ∃ _ : Box α, True) ===> True
#testOptimize ["InhabitedFunctionCodomain"]
  (∀ α : Type, ∃ _ : α → Color, True) ===> True

end Tests.EmptyDomains
