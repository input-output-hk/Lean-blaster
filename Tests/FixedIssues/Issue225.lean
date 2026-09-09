import Blaster
import Tests.Utils

namespace Tests.Issue225

structure ProofBox where
  value : Nat
  proof : True ∨ True

-- The kernel checks this without Blaster or any axioms: proof fields do not
-- distinguish constructor values, even when their proof constructors differ.
theorem boxes_equal :
    ProofBox.mk 7 (.inl .intro) = ProofBox.mk 7 (.inr .intro) := rfl

#testOptimize ["ProofFieldsEqual"]
  ProofBox.mk 7 (.inl .intro) = ProofBox.mk 7 (.inr .intro) ===> True
#testOptimize ["ProofFieldsNotUnequal"]
  ProofBox.mk 7 (.inl .intro) ≠ ProofBox.mk 7 (.inr .intro) ===> False
#testOptimize ["ProofFieldsInsideList"]
  [ProofBox.mk 7 (.inl .intro)] = [ProofBox.mk 7 (.inr .intro)] ===> True
#testOptimize ["DataFieldsStillDistinct"]
  ProofBox.mk 7 (.inl .intro) = ProofBox.mk 8 (.inr .intro) ===> False
#testOptimize ["ProofEquality"]
  (Or.inl True.intro : True ∨ True) = Or.inr True.intro ===> True

-- Negative solver regressions must actually be falsified, not merely unknown.
#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1)
  [ProofBox.mk 7 (.inl .intro) ≠ ProofBox.mk 7 (.inr .intro)]
#blaster (gen-cex: 0) (solve-result: 1)
  [[ProofBox.mk 7 (.inl .intro)] ≠ [ProofBox.mk 7 (.inr .intro)]]

end Tests.Issue225
