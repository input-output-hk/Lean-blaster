import Lean
import Solver.Command.Syntax

namespace Tests.Issue1

-- Issue: removeNamedPatternExpr: unexpected pattern expression
-- Diagnosis: avoid unfolding of class contraints instances

-- NOTE: remove solver options when instance parameters on inductive datatype supported
#solve (only-optimize: 1) (solve-result: 2)
  [ ∀ (x y : List UInt8), (if x < y then y.length else x.length) > 0 ]

end Tests.Issue1
