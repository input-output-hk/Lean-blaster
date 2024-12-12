import Lean
import Solver.Optimize.Env

open Lean Meta Solver.Options Solver.Optimize

namespace Solver

/-- Log the representation of `e` when verbose is set to 3. -/
def logReprExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose == 3
  then do
    logInfo f!"{msg}: {reprStr e}"
  else pure ()

/-- Pretty print and log `e` when verbose is set to 3. -/
def logPPExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose == 3
  then do
    logInfo f!"{msg}: {← ppExpr e}"
  else pure ()

end Solver
