import Blaster

namespace Test.SmtFinArith

/-! # Test cases to validate Fin modular arithmetic -/

-- 3 + 4 = 7 ≡ 2 (mod 5)
#blaster [(⟨3, by decide⟩ + ⟨4, by decide⟩ : Fin 5) = ⟨2, by decide⟩]

#blaster [∀ (x : Fin 5), x + ⟨0, by decide⟩ = x]

-- modular wrap keeps result in range
#blaster [∀ (x y : Fin 5), (x + y).val < 5]

#blaster [∀ (x y : Fin 7), x * y = y * x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), (x + y).val = x.val + y.val]

-- modular subtraction: 1 - 3 ≡ -2 ≡ 3 (mod 5)
#blaster [(⟨1, by decide⟩ - ⟨3, by decide⟩ : Fin 5) = ⟨3, by decide⟩]

#blaster [∀ (x : Fin 5), x - x = ⟨0, by decide⟩]

-- sub/add are modular inverses
#blaster [∀ (x y : Fin 7), (x - y) + y = x]

-- modular sub differs from Nat truncated sub
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), (x - y).val = x.val - y.val]

-- modular mul differs from plain Nat mul (guards the % n reduction)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), (x * y).val = x.val * y.val]
