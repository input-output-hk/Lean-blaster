import Blaster.Cli.Types
import Blaster.Smt.Translate

open Lean Meta Blaster.Optimize Blaster.Smt

register_option blaster.cli.capture : Bool := {
  defValue := false
  descr := "collect structured results for the lean-blaster executable" }

namespace Blaster.Cli

/-- One executable invocation owns the session. Normal Lean elaboration never enables capture.
    Ref updates are atomic because command/tactic elaboration may use worker threads. -/
structure CaptureSession where
  config : Config := {}
  report : Report := {}
  onStage : String → IO Unit := fun _ => pure ()
  onResult : CheckResult → IO Unit := fun _ => pure ()

instance : Inhabited CaptureSession := ⟨{}⟩

initialize captureSession : IO.Ref CaptureSession ← IO.mkRef {}

def capturing : CoreM Bool := return blaster.cli.capture.get (← getOptions)

def selected (cfg : Config) (property : String) : Bool :=
  cfg.declarations.isEmpty || cfg.declarations.contains property

/-- Capture the actual invocation, without re-running a theorem's tactic proof. -/
def runCaptured (e : Expr) (options : Options.BlasterOptions) (property invocation : String)
    (logUndetermined := true) (locationOverride : Option Location := none) : MetaM ((Result × Expr) × TranslateEnv) := do
  let enabled ← capturing
  let session ← captureSession.get
  let opts := if enabled then session.config.solverOptions options else options
  let env := { (default : TranslateEnv) with optEnv.options.solverOptions := opts }
  if !enabled then
    return ← Translate.main e logUndetermined |>.run env
  let ref ← getRef
  let pos := (← getFileMap).toPosition (ref.getPos?.getD 0)
  let location : Location := locationOverride.getD {
    file := (← readThe Core.Context).fileName
    line := pos.line
    column := pos.column + 1 }
  let reportThis := enabled && selected session.config property
  let goalText ← if reportThis then pure (some (← ppExpr e).pretty) else pure none
  let onStage := if reportThis then
    fun stage => session.onStage s!"I'm {stage} {property}"
    else fun _ => pure ()
  let start ← IO.monoMsNow
  try
    let answer@((result, _), finalEnv) ←
      Translate.main e logUndetermined (!enabled) onStage |>.run env
    if reportThis then
      let origin := if finalEnv.smtEnv.smtProc.isSome then "smt" else
        if opts.onlySmtLib && !opts.onlyOptimize && isUndeterminedResult result then "translation"
        else "optimization"
      let status := match result with
        | .Valid => "valid"
        | .Falsified _ => "falsified"
        | .Undetermined => "undetermined"
      let cex := match result with
        | .Falsified values => values.toArray
        | _ => #[]
      let reason := if status == "undetermined" then
        some (if opts.onlyOptimize then "I couldn't resolve this property through optimization alone" else
          if opts.onlySmtLib then "I translated this property without invoking Z3 (only-smt-lib is enabled)" else
          "Z3 couldn't determine whether this property holds; no specific reason was reported")
        else none
      let record : CheckResult := {
        property := property
        invocation := invocation
        status := status
        origin := origin
        location := location
        elapsedMs := (← IO.monoMsNow) - start
        solverTimeoutSeconds := opts.timeout
        goal := goalText
        counterexample := cex
        reason := reason }
      captureSession.modify fun s => { s with report.results := s.report.results.push record }
      session.onResult record
    return answer
  catch ex =>
    if reportThis then
      let record : CheckResult := {
        property := property, invocation := invocation, status := "error", origin := "pipeline"
        location := location, elapsedMs := (← IO.monoMsNow) - start, solverTimeoutSeconds := opts.timeout
        goal := goalText
        reason := some (← ex.toMessageData.toString) }
      captureSession.modify fun s => { s with report.results := s.report.results.push record }
      session.onResult record
    throw ex
  finally
    if reportThis then session.onStage "I'm elaborating the Lean file"

end Blaster.Cli
