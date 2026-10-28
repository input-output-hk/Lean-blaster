import Blaster

/-! Keep the live division source in the root package, following the polynomial
and model harnesses, without building the parent Tests library or ordinary Z3
suite. The staged backend is mandatory; no fallback or capability skip. -/
private def runDivisionSource : IO Unit := do
  let result ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "ff-tests/DivisionSource.lean"], cwd := some ".." }
  IO.print result.stdout
  unless result.exitCode == 0 do
    throw <| IO.userError s!"native division cases failed:\n{result.stdout}\n{result.stderr}"
  unless result.stderr.isEmpty do
    throw <| IO.userError s!"native division cases wrote stderr:\n{result.stderr}"

#eval runDivisionSource
