import Lean
import Blaster.Logging.Handler
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

/-! ### Helper: read options from TranslateEnvT state -/

private def getBlasterOpts : TranslateEnvT BlasterOptions := do
  return (← get).optEnv.options.solverOptions

/-! ### MonadBlasterLog instance for TranslateEnvT

    Dispatches on `outputMode` and `outputRepr` read from `BlasterOptions` in state.
    To add a new output format (e.g. XML), extend `OutputRepr` and add branches here.
-/

private def emitMsg (severity : MessageSeverity) (ref : Syntax) (textMsg : MessageData)
    (jsonFields : List (String × Json)) (depth : Option Nat) : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  match sOpts.outputRepr, sOpts.outputMode with
  | .Textual, .LogInfo =>
    match severity with
    | .information => logInfoAt ref textMsg
    | .warning     => logWarningAt ref textMsg
    | .error       => logErrorAt ref textMsg
  | .Textual, .StdOut => do
    stdOutPrintln (toString (← textMsg.format))
  | .JsonL, .LogInfo => do
    let line := jsonLine (← mkJsonObj jsonFields depth)
    match severity with
    | .information => logInfoAt ref line
    | .warning     => logWarningAt ref line
    | .error       => logErrorAt ref line
  | .JsonL, .StdOut => do
    stdOutPrintln (jsonLine (← mkJsonObj jsonFields depth))

private def emitProgressImpl (msg : String) (depth : Option Nat) : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  match sOpts.outputRepr, sOpts.outputMode with
  | .Textual, .LogInfo => do
    IO.println msg
    (← IO.getStdout).flush
  | .Textual, .StdOut =>
    stdOutPrintln msg
  | .JsonL, .LogInfo => do
    let j ← mkJsonObj [("type", "progress"), ("message", .str msg)] depth
    logInfo (jsonLine j)
  | .JsonL, .StdOut => do
    let j ← mkJsonObj [("type", "progress"), ("message", .str msg)] depth
    stdOutPrintln (jsonLine j)

private def emitProfileImpl (task : String) (duration : Float) : TranslateEnvT Unit := do
  let sOpts ← getBlasterOpts
  let durationMs := (duration * 1000).toUInt64.toNat
  match sOpts.outputRepr, sOpts.outputMode with
  | .Textual, .LogInfo => do
    IO.println s!"[End]: {task} ({reprPrec duration 2}s)"
  | .Textual, .StdOut =>
    stdOutPrintln s!"[End]: {task} ({reprPrec duration 2}s)"
  | .JsonL, .LogInfo => do
    let j ← mkJsonObj [("type", "profile"), ("task", .str task), ("durationMs", .num durationMs)] none
    logInfo (jsonLine j)
  | .JsonL, .StdOut => do
    let j ← mkJsonObj [("type", "profile"), ("task", .str task), ("durationMs", .num durationMs)] none
    stdOutPrintln (jsonLine j)

instance : MonadBlasterLog TranslateEnvT where
  emitInfo     := emitMsg .information
  emitWarning  := emitMsg .warning
  emitError    := emitMsg .error
  emitProgress := emitProgressImpl
  emitProfile  := emitProfileImpl

/-! ### Convenience aliases (shorter names for call sites) -/

def emitInfo (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit :=
  MonadBlasterLog.emitInfo ref textMsg jsonFields depth

def emitWarning (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit :=
  MonadBlasterLog.emitWarning ref textMsg jsonFields depth

def emitError (ref : Syntax) (textMsg : MessageData) (jsonFields : List (String × Json))
    (depth : Option Nat := none) : TranslateEnvT Unit :=
  MonadBlasterLog.emitError ref textMsg jsonFields depth

def emitProgress (msg : String) (depth : Option Nat := none) : TranslateEnvT Unit :=
  MonadBlasterLog.emitProgress msg depth

def emitProfile (task : String) (duration : Float) : TranslateEnvT Unit :=
  MonadBlasterLog.emitProfile task duration

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
