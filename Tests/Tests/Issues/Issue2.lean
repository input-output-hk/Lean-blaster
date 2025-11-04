import Lean
import PlutusCore.ByteString
import Solver.Command.Syntax

namespace Tests.Issue2

open PlutusCore.ByteString (ByteString)

-- Issue: synthesize instance error and application type mismatch
-- Diagnosis 1: Lean4 can't infer Decidable instance after definition unfolding/optimization
--              We therefore keep the Decidable constraint on the unfolded/optimized definition as is.
-- Diagnosis 2: We can't translate dite on Bool to boolean expression as we will not more
--              properly reference the if dependent hypothesis.
--              We therefore remove this simplification and added new ones on equality, forall, And and Or.

-- NOTE: remove solver options when instance parameters on inductive datatype supported
#solve [ ∀ (x y : ByteString), (if x < y then y.length else x.length + 1) > 0 ]

end Tests.Issue2
