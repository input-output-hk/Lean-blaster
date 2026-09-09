import Blaster

namespace Tests.Issue196

-- Opaque functions constrain results only on members of their Lean domains.
opaque hiddenId {α : Type} (x : α) : α := x
example : ¬ (∀ α : Type, (∀ x : α, hiddenId x = x) → ∃ _ : α, True) := by
  intro h
  obtain ⟨x, _⟩ := h Empty (fun x => Empty.elim x)
  exact Empty.elim x
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, (∀ x : α, hiddenId x = x) → ∃ _ : α, True]

-- Also guard later arguments when an earlier domain is inhabited.
opaque hiddenSecond {α β : Type} (_x : α) (y : β) : β := y
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ β : Type, (∀ y : β, hiddenSecond () y = y) → ∃ _ : β, True]

-- A cached erased function can be used at several unrelated generic domains.
opaque hiddenNat {α : Type} (_x : α) : Nat := 0
#blaster [∀ (α β : Type) (x : α) (y : β),
  Int.ofNat (hiddenNat x) + Int.ofNat (hiddenNat y) ≥ 0]
#blaster [∀ β : Type, (∀ (α : Type) (x : α), hiddenNat x = 0) →
  ∀ y : β, hiddenNat y = 0]

end Tests.Issue196
