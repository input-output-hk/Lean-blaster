import Lean
import Solver.Optimize.Env

open Lean Meta Solver.Options Solver.Optimize

namespace Solver

/-- Log the representation of `e` when verbose is set to 3. -/
def logReprExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose == 3 then
    logInfo f!"{msg}: {reprStr e}"
  else return ()

/-- Pretty print and log `e` when verbose is set to 3. -/
def logPPExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose == 3 then
    logInfo f!"{msg}: {← ppExpr e}"
  else return ()

/-- Dumps to `stdout` the smt commands submitted to the backend solver
    when option `dumpSmtLib` is set to `true`. -/
def logSmtQuery : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.dumpSmtLib then
    IO.println f!"Smt Query:"
    (← get).smtEnv.smtCommands.forM (λ c => IO.println f!"{c}")
  else pure ()


end Solver
