import Blaster.Smt.Env

open Lean Blaster.Optimize Blaster.Smt

#eval IO.FS.withTempFile fun output path => do
  let response := "(some \"(\"\n)\n"
  let marker := "end-of-response"
  output.putStr ((response ++ marker ++ "\n").replace "\n" "\r\n" ++ "(partial\n")
  output.flush
  let input ← IO.FS.Handle.mk path .read
  let actual ← readResponseUntil input marker
  unless actual == response do
    throw (IO.userError s!"Unexpected SMT response {repr actual}")
  match ← (readResponseUntil input marker).toBaseIO with
  | .error e =>
    unless e.toString.endsWith "Unexpected EOF while reading SMT response" do throw e
  | .ok _ => throw (IO.userError "Accepted an SMT response without an end marker")

run_elab do
  let process ← createBlasterProcess
  try
    for (command, reply) in [
        ("(set-option :print-success true)", "success\n"),
        ("(declare-datatype Box ((box (payload String))))", "success\n"),
        ("(declare-const x Box)", "success\n"),
        ("(assert (= x (box \"(\")))", "success\n"),
        ("(check-sat)", "sat\n")] do
      process.stdin.putStrLn command
      process.stdin.flush
      unless (← process.stdout.getLine) == reply do
        throwError "Unexpected Z3 reply to {command}"
    let action : TranslateEnvT Unit := do
      let value ← evalTerm (smtSimpleVarId (mkNormalSymbol "x"))
      unless value == "(box \"(\")\n" do
        throwError "Unexpected quoted model value: {repr value}"
      let value ← evalTerm (smtSimpleVarId (mkNormalSymbol "x"))
      unless value == "(box \"(\")\n" do
        throwError "The next model read did not start at its response: {repr value}"
    discard <| action.run { (default : TranslateEnv) with smtEnv.smtProc := some process }
  finally
    try process.kill catch _ => pure ()
    try discard process.wait catch _ => pure ()
