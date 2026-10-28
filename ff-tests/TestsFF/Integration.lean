import Blaster

/-! Execute the integrated source in the root package, matching the polynomial,
division and model wrappers without building the parent Tests library. The
staged backend and nonzero live SAT/UNSAT counts are mandatory, never skipped. -/
private def runIntegrationSource : IO Unit := do
  let result ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "ff-tests/IntegrationSource.lean"], cwd := some ".." }
  IO.print result.stdout
  unless result.exitCode == 0 do
    throw <| IO.userError s!"native integration cases failed:\n{result.stdout}\n{result.stderr}"
  unless result.stderr.isEmpty do
    throw <| IO.userError s!"native integration cases wrote stderr:\n{result.stderr}"

#eval runIntegrationSource
