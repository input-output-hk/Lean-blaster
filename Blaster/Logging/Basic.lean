import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Options Blaster.Optimize

namespace Blaster

/-! ### Shared IO helpers -/

def stdOutPrintln (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-! ### JSON helpers using Lean.Json -/

/-- Build a Json object with a depth field and monotonic timestamp. -/
def mkJsonObj (fields : List (String × Json)) (depth : Option Nat := none) : IO Json := do
  let ts ← IO.monoMsNow
  let depthJson : Json := match depth with | none => .null | some n => .num n
  let allFields := fields ++ [("depth", depthJson), ("timestamp", .num ts)]
  return Json.mkObj allFields

/-- Render a Json value as a compact single-line string (JSONL). -/
def jsonLine (j : Json) : String := j.compress

/-! ### Logger factory functions

    To add a new output mode, create a new `mkXxxLogger` factory function
    below and wire it into `mkLogger`.
-/

/-- Textual output via Lean diagnostics (logInfoAt/logWarningAt/logErrorAt). -/
def mkTextualLogInfoLogger : BlasterLogger where
  emitInfo     := fun ref msg _ _ => logInfoAt ref msg
  emitWarning  := fun ref msg _ _ => logWarningAt ref msg
  emitError    := fun ref msg _ _ => logErrorAt ref msg
  emitProgress := fun msg _ => do
    IO.println msg
    (← IO.getStdout).flush
  emitProfile  := fun task duration => do
    IO.println s!"[End]: {task} ({reprPrec duration 2}s)"

/-- Textual output via stdout (IO.println). -/
def mkTextualStdOutLogger : BlasterLogger where
  emitInfo     := fun _ msg _ _ => do stdOutPrintln (toString (← msg.format))
  emitWarning  := fun _ msg _ _ => do stdOutPrintln (toString (← msg.format))
  emitError    := fun _ msg _ _ => do stdOutPrintln (toString (← msg.format))
  emitProgress := fun msg _ => stdOutPrintln msg
  emitProfile  := fun task duration => stdOutPrintln s!"[End]: {task} ({reprPrec duration 2}s)"

/-- JSONL output via Lean diagnostics (logInfoAt). -/
def mkJsonLLogInfoLogger : BlasterLogger where
  emitInfo     := fun ref _ fields depth => do
    logInfoAt ref (jsonLine (← mkJsonObj fields depth))
  emitWarning  := fun ref _ fields depth => do
    logWarningAt ref (jsonLine (← mkJsonObj fields depth))
  emitError    := fun ref _ fields depth => do
    logErrorAt ref (jsonLine (← mkJsonObj fields depth))
  emitProgress := fun msg depth => do
    let j ← mkJsonObj [("type", "progress"), ("message", .str msg)] depth
    logInfo (jsonLine j)
  emitProfile  := fun task duration => do
    let durationMs := (duration * 1000).toUInt64.toNat
    let j ← mkJsonObj [("type", "profile"), ("task", .str task), ("durationMs", .num durationMs)] none
    logInfo (jsonLine j)

/-- JSONL output via stdout (IO.println). -/
def mkJsonLStdOutLogger : BlasterLogger where
  emitInfo     := fun _ _ fields depth => do
    stdOutPrintln (jsonLine (← mkJsonObj fields depth))
  emitWarning  := fun _ _ fields depth => do
    stdOutPrintln (jsonLine (← mkJsonObj fields depth))
  emitError    := fun _ _ fields depth => do
    stdOutPrintln (jsonLine (← mkJsonObj fields depth))
  emitProgress := fun msg depth => do
    let j ← mkJsonObj [("type", "progress"), ("message", .str msg)] depth
    stdOutPrintln (jsonLine j)
  emitProfile  := fun task duration => do
    let durationMs := (duration * 1000).toUInt64.toNat
    let j ← mkJsonObj [("type", "profile"), ("task", .str task), ("durationMs", .num durationMs)] none
    stdOutPrintln (jsonLine j)

/-- Create a logger from the given output mode and representation. -/
def mkLogger (mode : OutputMode) (repr : OutputRepr) : BlasterLogger :=
  match repr, mode with
  | .Textual, .LogInfo => mkTextualLogInfoLogger
  | .Textual, .StdOut  => mkTextualStdOutLogger
  | .JsonL,   .LogInfo => mkJsonLLogInfoLogger
  | .JsonL,   .StdOut  => mkJsonLStdOutLogger

/-! ### Emit helpers (delegate through handler in TranslateEnvT state) -/

private def getLogger : TranslateEnvT BlasterLogger := do
  return (← get).logger

private def getBlasterOpts : TranslateEnvT BlasterOptions := do
  return (← get).optEnv.options.solverOptions

/-- Emit an info-level message via the configured logger. -/
def emitInfo (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit := do
  (← getLogger).emitInfo ref textMsg jsonFields depth

/-- Emit a warning-level message via the configured logger. -/
def emitWarning (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit := do
  (← getLogger).emitWarning ref textMsg jsonFields depth

/-- Emit an error-level message via the configured logger. -/
def emitError (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit := do
  (← getLogger).emitError ref textMsg jsonFields depth

/-- Emit a progress message via the configured logger. -/
def emitProgress (msg : String) (depth : Option Nat := none) : TranslateEnvT Unit := do
  (← getLogger).emitProgress msg depth

/-- Emit a profile timing message via the configured logger. -/
def emitProfile (task : String) (duration : Float) : TranslateEnvT Unit := do
  (← getLogger).emitProfile task duration

/-! ### Refactored existing functions -/

/-- Log the representation of `e` when verbose is set to 3. -/
def logReprExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  if sOpts.verbose == 3 then
    logInfo f!"{msg}: {reprStr e}"
  else return ()

/-- Pretty print and log `e` when verbose is set to 3. -/
def logPPExpr (msg : String) (e : Expr) : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  if sOpts.verbose == 3 then
    logInfo f!"{msg}: {← ppExpr e}"
  else return ()

/-- Dumps to `stdout` the smt commands submitted to the backend solver
    when option `dumpSmtLib` is set to `true`. -/
def logSmtQuery : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  if sOpts.dumpSmtLib then
    match sOpts.outputMode with
    | .StdOut =>
      stdOutPrintln "Smt Query:"
      (← get).smtEnv.smtCommands.forM (λ c => stdOutPrintln s!"{c}")
    | .LogInfo =>
      IO.println f!"Smt Query:"
      (← get).smtEnv.smtCommands.forM (λ c => IO.println s!"{c}")
  else pure ()


/-- Profile Task `msg` when verbose is greater than verboseLevel by displaying
    the time taken by `msg`.
-/
@[always_inline, inline]
def profileTask (msg : String) (p : TranslateEnvT α) (verboseLevel := 1) : TranslateEnvT α := do
  let sOpts ← getBlasterOpts
  if sOpts.verbose ≥ verboseLevel then
    let startTime ← IO.monoMsNow
    -- In JsonL mode, suppress [Start] and only emit final profile object
    if sOpts.outputRepr == .Textual then
      match sOpts.outputMode with
      | .StdOut  => stdOutPrintln s!"[Start]: {msg}"
      | .LogInfo =>
        IO.println f!"[Start]: {msg}"
        (← IO.getStdout).flush
    let res ← p
    let stopTime ← IO.monoMsNow
    let elapseTime := (stopTime - startTime).toFloat / 1000.0
    emitProfile msg elapseTime
    return res
  else p

end Blaster
