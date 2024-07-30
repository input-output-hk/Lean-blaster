import Lean
open Lean Elab Command

namespace Solver

/--
Type introducing the options passed on to the solver.
-/
structure SolverOptions where
  /-- The number of unfolding steps to be considered when
      unfolding a recursive function. It is set to 100 by default. -/
  unfoldDepth : Nat := 100
  /-- The solving timeout in seconds. It is set to 'none' by default (i.e., unlimited). -/
  timeout : Option Nat := none
  /-- The verbosity level. It is set to zero by default (i.e., no verbosity). -/
  verbose : Nat := 0
 deriving Repr, Inhabited

end Solver

