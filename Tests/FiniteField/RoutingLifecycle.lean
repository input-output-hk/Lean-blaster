import Tests.Pure
import Blaster.Smt.FiniteFieldPreflight

namespace Test.FiniteFieldRoutingLifecycle

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

-- Shell builtins only: no descendant can hold a pipe open after retirement.
-- This is the actual input received by each solver, not a reconstructed record.
private def spawnChild (path : System.FilePath) : IO PipedChild := do
  IO.FS.writeFile path ""
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c",
      "while IFS= read -r line; do " ++
      s!"printf '%s\\n' \"$line\" >> '{path}'; " ++
      "case \"$line\" in '(exit)') exit 0;; *) echo success;; esac; done"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
    setsid := true
  }

private def environment (mode : SolverMode) (sessions : Array SolverSession) : TranslateEnv :=
  let base : TranslateEnv := default
  { base with
    optEnv.options.solverOptions := { solverMode := mode }
    smtEnv.sessions := sessions
    smtEnv.emitProc := sessions[0]?.map (·.process)
    smtEnv.deferredSessions := sessions.map (·.solver)
    smtEnv.configuredSolvers := sessions.map (·.solver)
    smtEnv.solverRecords := sessions.map fun session =>
      { solver := session.solver, version := "retained fake version",
        commandLine := "shell builtins", setupCommands := #[] } }

private def residual : MetaM Expr := do
  let carrier := mkApp (mkConst ``Residue) (mkRawNatLit 7)
  withLocalDeclD `x carrier fun x =>
    withLocalDeclD `y carrier fun y => do
      mkForallFVars #[x, y] (← mkEq x y)

private def assertRetired (env : TranslateEnv) (sessions : Array SolverSession) : MetaM Unit := do
  unless env.smtEnv.sessions.isEmpty && env.smtEnv.emitProc.isNone &&
      env.smtEnv.deferredSessions.isEmpty do
    throwError "native finite-field rejection retained active or deferred ownership"
  unless env.smtEnv.smtCommands.isEmpty do
    throwError "native finite-field rejection emitted canonical SMT commands"
  unless env.smtEnv.solverRecords.size == sessions.size do
    throwError "native finite-field rejection discarded solver records"
  for session in sessions do
    let some record := env.smtEnv.solverRecords.find? (·.solver == session.solver)
      | throwError "native finite-field rejection lost {session.solver} record"
    unless record.version == "retained fake version" && record.commandLine == "shell builtins" do
      throwError "native finite-field rejection replaced {session.solver} provenance"
    let status ← IO.Process.output {
      cmd := "/bin/kill", args := #["-0", toString session.process.pid] }
    unless status.exitCode != 0 do
      throwError "native finite-field rejection left {session.solver} alive or unreaped"

private def assertTranscript (path : System.FilePath) (expectExit : Bool) : MetaM Unit := do
  let text ← IO.FS.readFile path
  if expectExit && !(text.splitOn "\n").contains "(exit)" then
    throwError "native finite-field rejection did not send exit: {text}"
  for forbidden in ["declare", "define", "assert", "check-sat", "FiniteField", "#f"] do
    if contains text forbidden then
      throwError "native finite-field rejection sent forbidden input {forbidden}: {text}"

private def withoutLoggedMessages (action : MetaM α) : MetaM α := do
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  try action
  finally Core.setMessageLog saved

private def testConcurrentRejection (mode : SolverMode) : MetaM Unit :=
  withoutLoggedMessages <| IO.FS.withTempDir fun directory => do
    let z3Path := directory / "z3.input"
    let cvc5Path := directory / "cvc5.input"
    let z3 ← spawnChild z3Path
    let cvc5 ← spawnChild cvc5Path
    let sessions := #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    let probeCalled ← IO.mkRef false
    let probe : IO SolverCandidate := do
      probeCalled.set true
      throw <| IO.userError "unexpected finite-field capability probe"
    let evidenceType := mkApp (mkConst ``PrimeModulus) (mkRawNatLit 7)
    withLocalDecl `hp .instImplicit evidenceType fun _ => do
      let expression ← residual
      let action : TranslateEnvT Unit := withSmtSessionOwner do
        let message ← try
          discard <| preflightFiniteFields expression probe
          pure none
        catch error : Exception =>
          -- These checks deliberately run before the surrounding owner finalizer.
          assertRetired (← get) sessions
          assertTranscript z3Path true
          assertTranscript cvc5Path true
          pure (some (← error.toMessageData.toString))
        let some message := message
          | throwError "native finite-field {mode} unexpectedly passed preflight"
        unless contains message "native finite-field" && contains message (toString mode) do
          throwError "wrong native finite-field {mode} diagnostic: {message}"
        if ← probeCalled.get then
          throwError "native finite-field {mode} probed before rejecting concurrent mode"
      discard <| action.run (environment mode sessions)

-- Admission can fail before the concurrent-policy check. The existing owner
-- must still retire its already-running children when that exception escapes.
private def testAdmissionFailureOwner : MetaM Unit :=
  withoutLoggedMessages <| IO.FS.withTempDir fun directory => do
    let path := directory / "cvc5.input"
    let child ← spawnChild path
    let sessions := #[{ solver := .cvc5, process := child }]
    let probeCalled ← IO.mkRef false
    let probe : IO SolverCandidate := do
      probeCalled.set true
      throw <| IO.userError "unexpected admission-failure capability probe"
    let expression ← residual
    -- No deferred failure is present in this single-session owner scenario.
    let env := { environment .single sessions with smtEnv.deferredSessions := #[] }
    let action : TranslateEnvT Unit := do
      let message ← try
        withSmtSessionOwner do
          discard <| preflightFiniteFields expression probe
        pure none
      catch error : Exception => pure (some (← error.toMessageData.toString))
      let some message := message
        | throwError "native finite-field admission unexpectedly accepted missing evidence"
      unless contains message "missing checked PrimeModulus" do
        throwError "wrong finite-field admission diagnostic: {message}"
      assertRetired (← get) sessions
      assertTranscript path false
      if ← probeCalled.get then
        throwError "native finite-field admission failure probed a solver"
    discard <| action.run env

#eval testConcurrentRejection .first
#eval testConcurrentRejection .agree
#eval testAdmissionFailureOwner

end Test.FiniteFieldRoutingLifecycle
