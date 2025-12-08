import Lean
import Blaster

namespace Tests.Issue28

-- Issue: Optimization not properly applied
-- Diagnosis : We need to update inHypMap to consider zero relational for Int and Nat
--             We also need to add normalization rule `0 < -a ===> a < 0`.

set_option warn.sorry false
theorem thm1 : ∀ (a : Int), a < 0 → 0 < -a := by sorry
theorem thm2 : ∀ (a : Int), a < 0 → 0 ≠ -a := by sorry
theorem thm3 : ∀ (a : Int), 0 < a → 0 ≠ -a := by sorry
theorem thm4 : ∀ (a : Int), 0 < -a → a < 0 := by sorry
theorem thm5 : ∀ (a : Nat), 0 < a → 0 ≠ a := by sorry
theorem thm6 : ∀ (a : Nat), 0 ≠ a → 0 < a := by sorry
theorem thm7 : ∀ (a : Int), 0 ≠ -a → 0 < a := by sorry
theorem thm8 : ∀ (a : Int), 0 ≠ -a → 0 < a := by sorry

#blaster (only-optimize: 1) [ thm1 ]
#blaster (only-optimize: 1) [ thm2 ]
#blaster (only-optimize: 1) [ thm3 ]
#blaster (only-optimize: 1) [ thm4 ]
#blaster (only-optimize: 1) [ thm5 ]
#blaster (only-optimize: 1) [ thm6 ]
#blaster (gen-cex: 0) (solve-result: 1) [ thm7 ]
#blaster (gen-cex: 0) (solve-result: 1) [ thm8 ]

end Tests.Issue28
