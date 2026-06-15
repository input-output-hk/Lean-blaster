import Blaster

namespace Test.SmtFinSort

/-! # Test cases to validate Fin sort + range qualifier -/

#blaster [∀ (x : Fin 5), x.val < 5]

#blaster [∀ (x : Fin 5), 0 ≤ x.val]

#blaster [∀ (x : Fin 0), x.val = 99]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Fin 5), x.val < 4]
