import Blaster

namespace Test.SolverModeConfiguration

private def rejectsOptions (options : String) : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr s!"import Blaster\n#blaster {options} (only-optimize: 1) [True]\n"
    handle.flush
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #[path.toString]
    }
    unless output.exitCode != 0 do
      throw <| IO.userError s!"Invalid options were accepted: {options}"

#eval rejectsOptions "(solver: z3) (solver-mode: first)"
#eval rejectsOptions "(solver-mode: agree) (only-smt-lib: 1)"

-- `only-optimize` never starts either solver, even with a concurrent mode.
#blaster (solver-mode: first) (only-optimize: 1) [∀ (x : Int), x = x]
#blaster (solver: cvc5) (solver-mode: single) (only-optimize: 1) [∀ (x : Int), x = x]


#blaster (solver: cvc5) (only-smt-lib: 1) (solve-result: 2) [∀ (x : Int), x ≠ 3]

end Test.SolverModeConfiguration
