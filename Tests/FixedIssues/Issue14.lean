import Lean
import Blaster

namespace Tests.Issue14

-- Issue: Unexpected smt error: (error "line 11 column 36: invalid declaration, function '@isPUnit'
--        (with the given signature) already declared") for (declare-fun @isPUnit ( @PUnit) Bool)
-- Diagnosis: We need to infer the type of a constructor in function `translateCtor` instead of
-- using the type obtained from ctorInfo. Indeed, the ctorInfo type is not instantiated properly.


theorem thm1: ∀ (x y : Unit), x = y ∧ x = () := by simp

#blaster [thm1]

end Tests.Issue14
