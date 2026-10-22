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

/-- Print runnable SMT transcripts when dumping is requested, or as part of the
    level-3 diagnostic pipeline. Concurrent runs are labeled per backend and
    combine backend setup with the one canonical logical query. -/
def logSmtQuery : TranslateEnvT Unit := do
  let env ← get
  let sOpts := env.optEnv.options.solverOptions
  unless sOpts.dumpSmtLib || sOpts.verbose ≥ 3 do return
  let records := [SmtSolver.z3, SmtSolver.cvc5].filterMap fun solver =>
    env.smtEnv.solverRecords.find? (·.solver == solver)
  for record in records do
    if records.length == 1 && sOpts.solverMode == .single then
      IO.println "Smt Query:"
    else
      IO.println s!"SMT Query [{record.solver}]:"
    record.setupCommands.forM (fun command => IO.println s!"{command}")
    env.smtEnv.smtCommands.forM (fun command => IO.println s!"{command}")
    if let some command := record.checkCommand then IO.println s!"{command}"
    record.modelCommands.forM (fun command => IO.println command)
    IO.println "(exit)"


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
