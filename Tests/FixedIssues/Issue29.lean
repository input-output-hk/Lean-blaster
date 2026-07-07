import Lean
import Blaster

namespace Tests.Issue29

-- Issue: Unexpected counterexample
-- Diagnosis : We need to add codomain constraint for undeclared/axiom functions.

set_option warn.sorry false

class ToNat (α : Type u) where
  toNat : α → Nat

theorem toNat_cstr (α : Type) (β : Type) (_h1 : ToNat α) (_h2 : ToNat β) (x : α) (y : β) :
  Int.ofNat (ToNat.toNat x) + Int.ofNat (ToNat.toNat y) ≥ 0 := by blaster (solver: all)

axiom natCast : α → Nat

theorem natCast_cstr (α : Type) (β : Type) (x : α) (y : β) :
  Int.ofNat (natCast x) + Int.ofNat (natCast y) ≥ 0 := by blaster (solver: all)

end Tests.Issue29
