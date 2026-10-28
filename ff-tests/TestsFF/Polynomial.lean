import Blaster

/-! Run the source-to-solver cases from the repository root. Importing a module
of the parent Tests library here would make Lake build that entire library's
shared facet, crossing the pure/native test boundary into ordinary Z3 tests.
Only the checked large-prime fixture is built explicitly; no solver fallback
or capability skip is permitted. -/
private def runPolynomialSource : IO Unit := do
  let fixture ← IO.Process.output {
    cmd := "lake", args := #["build", "Tests.FiniteField.LargePrime"], cwd := some ".." }
  unless fixture.exitCode == 0 do
    throw <| IO.userError s!"checked prime fixture build failed:\n{fixture.stdout}\n{fixture.stderr}"
  let result ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "ff-tests/PolynomialSource.lean"], cwd := some ".." }
  IO.print result.stdout
  unless result.exitCode == 0 do
    throw <| IO.userError s!"native polynomial cases failed:\n{result.stdout}\n{result.stderr}"
  unless result.stderr.isEmpty do
    throw <| IO.userError s!"native polynomial cases wrote stderr:\n{result.stderr}"

#eval runPolynomialSource
