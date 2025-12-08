import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Options Blaster.Optimize

namespace Blaster

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
    (← get).smtEnv.smtCommands.forM (λ c => IO.println s!"{c}")
  else pure ()


/-- Profile Task `msg` when verbose is greater than verboseLevel by displaying
    the time taken by `msg`.
-/
@[always_inline, inline]
def profileTask (msg : String) (p : TranslateEnvT α) (verboseLevel := 1) : TranslateEnvT α := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose ≥ verboseLevel then
    let startTime ← IO.monoMsNow
    IO.println f!"[Start]: {msg}"
    (← IO.getStdout).flush
    let res ← p
    let stopTime ← IO.monoMsNow
    let elapseTime := (stopTime - startTime).toFloat / 1000.0
    IO.println f!"[End]: {msg} ({reprPrec elapseTime 2}s)"
    return res
  else p

end Blaster
