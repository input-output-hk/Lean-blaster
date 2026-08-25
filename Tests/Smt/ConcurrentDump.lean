import Blaster

namespace Test.ConcurrentDump

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def source : String :=
  "import Blaster\n" ++
  "#blaster (solver-mode: first) (dump-smt-lib: 1) (solve-result: 1) [∀ (x : Int), x ≠ 3]\n"

private def testLabeledRunnableTranscripts : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr source
    handle.flush
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #[path.toString]
    }
    unless output.exitCode == 0 do
      throw <| IO.userError <| "concurrent dump subprocess failed\n" ++ output.stdout ++ output.stderr
    for expected in ["SMT Query [z3]:", "SMT Query [cvc5]:", "(check-sat)"] do
      unless contains output.stdout expected do
        throw <| IO.userError s!"concurrent dump omitted {expected}\n{output.stdout}"

#eval testLabeledRunnableTranscripts

end Test.ConcurrentDump
