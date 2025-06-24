import Lean
open Lean Elab Command

namespace Solver.Options

/-- Expected solve result -/
inductive ExpectedResult where
  | ExpectedValid
  | ExpectedFalsified
  | ExpectedUndetermined
deriving Repr, DecidableEq

def isExpectedValid : ExpectedResult -> Bool
| .ExpectedValid => true
| _ => false

def isExpectedFalsified : ExpectedResult -> Bool
| .ExpectedFalsified => true
| _ => false

def isExpectedUndetermined : ExpectedResult -> Bool
| .ExpectedUndetermined => true
| _ => false

/-- Type introducing the options passed on to the solver. -/
structure SolverOptions where
  /-- The number of unfolding steps to be considered when
      unfolding a recursive function. It is set to 100 by default. -/
  unfoldDepth : Nat := 100

  /-- The solving timeout in seconds. It is set to 'none' by default (i.e., unlimited). -/
  timeout : Option Nat := none

  /-- The verbosity level. It is set to zero by default (i.e., no verbosity).
        - Verbosity Level 0
           - Description: Default verbosity level that only displays the solve result.
           - Usage: This level is to be used when you do not want any extra output during the execution of commands.
        - Verbosity Level 1
           - Description: In addition to Level 0, displays solving progression (e.g., tactics applied or BMC step)
           - Usage: This level is useful mainly when you want to display the different solving steps.
        - Verbosity Level 2
           - Description: In addition to Level 1, displays solving statistics provided by the backend SMT solver.
           - Usage: This level is useful only for the tool maintainer.
        - Verbosity Level 3
           - Description: In addition to Level 2, displays the rewriting rules applied on the theorems to be solved.
           - Usage: This level is to be used mainly for debugging purposes.
   TODO: This description will be updated as new functionalities are introduced.
  -/
  verbose : Nat := 0

  /-- When set to `true`, only perform translation to smt-lib without invoking the backend smt solver. -/
  onlySmtLib : Bool := false

  /-- When set to `true`, only perform optimization on the lean specification and do not translate to smt-lib. -/
  onlyOptimize : Bool := false

  /-- When set to `true`, dump the smt query to stdout. -/
  dumpSmtLib : Bool := false

  /-- When set to `true`, generate the counterexample produced for a falsified theorem when
  the backend SMT solver is invoked. -/
  generateCex : Bool := true

  /-- When set to `true`, trigger an error if the #solve command does not return a Falisifed status. -/
  solveResult : ExpectedResult := .ExpectedValid

  /-- Maximum analysis depth to be considered when performing BMC and K-Induction.
      It is set to 100 by default. -/
  maxDepth : Nat := 100
 deriving Repr

instance : Inhabited SolverOptions where
  default := {}

end Solver.Options

