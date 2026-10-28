import Tests.FiniteField.Routing
import Tests.FiniteField.RoutingLifecycle
import Tests.FiniteField.Model
import Tests.Smt.ResponseLifecycle
import Tests.Smt.CrashLifecycle
import Blaster.Smt.Translate.FiniteField

/-! Pure M1 integration boundaries. Imported component suites retain backend
policy (explicit/environment Z3 and binary-free cvc5), rejection before broadcast,
model decoding, and concurrent response/cleanup regressions. The scenarios below
join admission, real polynomial translation, optional evidence and ownership.
The shell is a protocol fixture, not a qualified solver or a proof producer;
these checks make no verified-native claim and do not cross blasterProven's trust
boundary. M2, proof-profile/rule auditing and FF optimizer rewrites remain separate. -/
namespace Test.FiniteFieldOutcomeIntegration

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

private def inTempDirectory (action : System.FilePath → MetaM Unit) : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      action directory
    finally
      IO.Process.setCurrentDir original

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

-- Builtins only: stalled replies never leave a descendant holding a pipe.
private def spawnChild (path : System.FilePath) (verdict model : String) : IO PipedChild := do
  IO.FS.writeFile path ""
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c",
      "while IFS= read -r line; do " ++
      s!"printf '%s\\n' \"$line\" >> '{path}'; " ++
      "case \"$line\" in '(check-sat)') " ++
      (if verdict == "stall" then ":; " else s!"printf '%s\\n' '{verdict}'; ") ++
      ";; '(get-value ('*) " ++
      s!"printf '%s\\n' '{model}'; " ++
      ";; '(exit)') exit 0;; *) echo success;; esac; done"]
    stdin := .piped, stdout := .piped, stderr := .piped }

private def environment (mode : SolverMode) (sessions : Array SolverSession) : TranslateEnv :=
  { (default : TranslateEnv) with
    optEnv.options.solverOptions := {
      solver := if mode == .single then some .cvc5 else none
      solverMode := mode, generateCex := true, timeout := some 1 }
    smtEnv.sessions := sessions
    smtEnv.emitProc := sessions[0]?.map (·.process)
    smtEnv.configuredSolvers := sessions.map (·.solver)
    smtEnv.singleSolver := if mode == .single then some .cvc5 else none
    smtEnv.solverRecords := sessions.map fun session =>
      { solver := session.solver, version := "integration fixture",
        commandLine := "shell builtins", setupCommands := #[], timeoutMs := some 0 } }

private def runOwned (env : TranslateEnv) (action : TranslateEnvT Result) :
    MetaM (Except String Result × TranslateEnv) := do
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  try
    let result ← (do
      try
        return (Except.ok (← withSmtSessionOwner action) : Except String Result)
      catch error : Exception =>
        return Except.error (← error.toMessageData.toString)).run env
    let finalEnv := result.2.smtEnv
    unless finalEnv.sessions.isEmpty && finalEnv.emitProc.isNone &&
        finalEnv.deferredSessions.isEmpty && !finalEnv.nativeFieldQualified do
      throwError "integrated outcome retained solver ownership"
    unless finalEnv.solverRecords.size == env.smtEnv.solverRecords.size do
      throwError "integrated outcome discarded producing-session provenance"
    return result
  finally
    Core.setMessageLog saved
    for session in env.smtEnv.sessions do
      let status ← IO.Process.output {
        cmd := "/bin/kill", args := #["-0", toString session.process.pid] }
      unless status.exitCode != 0 do
        throwError "integrated outcome left {session.solver} alive or unreaped"

private def query : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), x + 1 = x

private def fieldOutcome (verdict : String) : MetaM Unit :=
  IO.FS.withTempDir fun directory => do
    let path := directory / "cvc5.input"
    -- Well-framed but invalid FF evidence must not undo the SAT verdict.
    let child ← spawnChild path verdict "((wrong #f7m7))"
    let sessions := #[{ solver := .cvc5, process := child }]
    let .defnInfo info ← getConstInfo ``query | throwError "missing integrated query"
    let probes ← IO.mkRef (0 : Nat)
    let (result, finalEnv) ← runOwned (environment .single sessions) do
      let candidate ← preflightFiniteFields info.value do
        probes.modify (· + 1)
        pure { cmd := "/injected/not-spawned-cvc5" }
      unless candidate.isSome && (← get).smtEnv.nativeFieldQualified do
        throwError "admission lost injected qualification"
      let some term ← translatePolynomial info.value
        | throwError "admitted polynomial fell through native translation"
      assertTerm (notSmt term)
      checkSat
    unless (← probes.get) == 1 do throwError "wrong qualification count"
    let text ← IO.FS.readFile path
    for fragment in ["(_ FiniteField 7)", "ff.add", "(assert (not ", "(check-sat)"] do
      unless contains text fragment do throwError "missing integrated command {fragment}: {text}"
    let some record := finalEnv.smtEnv.solverRecords[0]?
      | throwError "missing integrated solver record"
    unless record.version == "integration fixture" && record.checkCommand.isSome do
      throwError "integrated outcome lost check provenance"
    if verdict == "sat" then
      let .ok (.Falsified values) := result
        | throwError "malformed optional FF evidence changed SAT: {reprStr result}"
      unless !values.isEmpty && values.all (contains · "<counterexample unavailable>") &&
          record.failedStage == some "model evidence" &&
          record.failureResponse.any (fun diagnostic => diagnostic.utf8ByteSize ≤ 256) &&
          !record.modelCommands.isEmpty && record.modelResponses == #["((wrong #f7m7))\n"] do
        throwError "malformed evidence lost bounded failure or escaped as a value"
    else if verdict == "unknown" then
      let .ok .Undetermined := result
        | throwError "unknown changed verdict: {reprStr result}"
      unless record.modelCommands.isEmpty && record.stdout.contains "unknown\n" do
        throwError "unknown requested evidence or lost its response"
    else
      let .error message := result | throwError "protocol error became a verdict"
      unless contains message "check protocol" && record.failedStage == some "check protocol" &&
          record.modelCommands.isEmpty do
        throwError "protocol failure lost stage or requested evidence: {message}"

-- No field occurs here: the native policy must not disable ordinary concurrency.
-- Both stalled children exercise the real hard deadline, not a synthetic result.
private def nonFieldOutcome (mode : SolverMode) (verdict : String) : MetaM Unit :=
  inTempDirectory fun directory => do
    let z3 ← spawnChild (directory / "z3.input") verdict "()"
    let cvc5 ← spawnChild (directory / "cvc5.input") verdict "()"
    let sessions := #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    let (result, finalEnv) ← runOwned (environment mode sessions) do
      let candidate ← preflightFiniteFields (mkConst ``True)
        (throw <| IO.userError "non-FF query probed native capability")
      unless candidate.isNone do throwError "non-FF query selected native candidate"
      checkSat
    if verdict == "stall" then
      let .error message := result | throwError "timeout became a logical verdict"
      unless contains message "check timeout" && finalEnv.smtEnv.solverRecords.all
          (fun record => record.failedStage == some "check timeout" && record.modelCommands.isEmpty) do
        throwError "timeout lost diagnostics: {message}"
    else
      let .ok .Undetermined := result
        | throwError "ordinary concurrent unknown changed result: {reprStr result}"
      unless finalEnv.smtEnv.solverRecords.all
          (fun record => record.stdout.contains "unknown\n" && record.modelCommands.isEmpty) do
        throwError "concurrent unknown lost producing-session responses"

#eval fieldOutcome "sat"
#eval fieldOutcome "unknown"
#eval fieldOutcome "not-a-verdict"
#eval nonFieldOutcome .first "unknown"
#eval nonFieldOutcome .agree "unknown"
#eval nonFieldOutcome .first "stall"

end Test.FiniteFieldOutcomeIntegration
