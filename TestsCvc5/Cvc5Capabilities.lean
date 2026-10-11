import Blaster

namespace Test.Cvc5Capabilities

open Blaster.Options Blaster.Smt

/-! Live capability validation against the installed cvc5 executable.
    The pure acceptance policy (present / missing / absent capability) is
    covered in `Tests.Smt.SolverVersion`; this module checks that the cvc5
    found on PATH passes it, i.e. that `cvc5 --show-config` reports
    `cocoa : yes`, and that discovery accepts it. -/

/-- info: some "yes" -/
#guard_msgs in
#eval show IO (Option String) from do
  let desc := SmtSolver.cvc5.descriptor
  match ← probeSolverCapabilities desc desc.candidates[0]! with
  | .ran 0 config => return configCapability? config "cocoa"
  | _ => return none

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let desc := SmtSolver.cvc5.descriptor
  match ← validateSolverCandidate desc desc.candidates[0]! with
  | .ok _ => return true
  | .error log => do IO.eprintln log; return false

end Test.Cvc5Capabilities
