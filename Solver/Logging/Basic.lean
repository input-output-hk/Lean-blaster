import Lean
import Solver.Command.Options

open Lean Meta Solver.Options

namespace Solver

/-- Log the representation of `e` when verbose is set to 3. -/
def logReprExpr (sOpts : SolverOptions) (msg : String) (e : Expr) : MetaM Unit :=
  if sOpts.verbose == 3
  then do
    logInfo f!"{msg}: {reprStr e}"
  else pure ()

/-- Pretty print and log `e` when verbose is set to 3. -/
def logPPExpr (sOpts : SolverOptions) (msg : String) (e : Expr) : MetaM Unit :=
  if sOpts.verbose == 3
  then do
    logInfo f!"{msg}: {← ppExpr e}"
  else pure ()

end Solver
