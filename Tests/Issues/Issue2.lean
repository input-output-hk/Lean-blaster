import Lean
import Solver.Command.Syntax

namespace Tests.Issue2

-- Issue: synthesize instance error and application type mismatch
-- Diagnosis 1: Lean4 can't infer Decidable instance after definition unfolding/optimization
--              We therefore keep the Decidable constraint on the unfolded/optimized definition as is.
-- Diagnosis 2: We can't translate dite on Bool to boolean expression as we will not more
--              properly reference the if dependent hypothesis.
--              We therefore remove this simplification and added new ones on equality, forall, And and Or.

/-- LT instance for ByteArray -/
instance LTByteArray : LT ByteArray where
  lt x y := x.data < y.data

/-- Decidable LT instance for ByteArray -/
instance : (x y : ByteArray) → Decidable (x < y) :=
 fun x y => inferInstanceAs (Decidable (x.data < y.data))

-- NOTE: remove solver options when instance parameters on inductive datatype supported
#solve (only-optimize: 1) (solve-result: 2)
  [ ∀ (x y : ByteArray), (if x < y then y.size else x.size + 1) > 0 ]

end Tests.Issue2
