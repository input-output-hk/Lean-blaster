import Blaster

namespace Test.SmtFinOps

/-! # Test cases to validate Fin.val/Fin.mk identity + comparisons -/

#blaster [∀ (x y : Fin 5), x.val = y.val → x = y]

#blaster [(⟨0, by decide⟩ : Fin 5).val = 0]

#blaster [∀ (x y : Fin 8), x < y → x.val < y.val]

#blaster [∀ (x y : Fin 8), x > 0 → x < y ∨ y <= x]

#blaster [∀ (h : (3:Nat) < 5), (Fin.mk 3 h).val = 3]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), x.val = y.val]
