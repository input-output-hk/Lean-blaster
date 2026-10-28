import Blaster

/-! Run live source-to-solver model checks from the repository root without
importing the parent Tests library or crossing into its ordinary solver profile.
`make test-cvc5-ff` supplies the pinned, offline-qualified executable; the child
inherits that environment and rejects a missing solver rather than falling back.
Checked small-prime evidence is self-contained in ModelSource.lean. -/
private def runModelSource : IO Unit := do
  let result ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "ff-tests/ModelSource.lean"], cwd := some ".." }
  IO.print result.stdout
  unless result.exitCode == 0 do
    throw <| IO.userError s!"native model cases failed:\n{result.stdout}\n{result.stderr}"
  unless result.stderr.isEmpty do
    throw <| IO.userError s!"native model cases wrote stderr:\n{result.stderr}"

#eval runModelSource
