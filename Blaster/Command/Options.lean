import Lean
open Lean Elab Command

namespace Blaster.Options

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

/-- Backend SMT solver used to discharge the translated goals. -/
inductive SmtSolver where
  | z3
  | cvc5
deriving Repr, DecidableEq

instance : ToString SmtSolver where
  toString
    | .z3 => "z3"
    | .cvc5 => "cvc5"

/-- Parse an `SmtSolver` from its name (as used in the `solver:` option and
    the `BLASTER_SOLVER` environment variable). -/
def SmtSolver.ofString? : String → Option SmtSolver
  | "z3" => some .z3
  | "cvc5" => some .cvc5
  | _ => none

/-- How Blaster uses the configured SMT backends. `single` preserves the
    selected-backend behavior; `first` races Z3 and cvc5; `agree` requires
    both backends to return compatible verdicts. -/
inductive SolverMode where
  | single
  | first
  | agree
deriving Repr, DecidableEq

instance : ToString SolverMode where
  toString
    | .single => "single"
    | .first => "first"
    | .agree => "agree"

def SolverMode.ofString? : String → Option SolverMode
  | "single" => some .single
  | "first" => some .first
  | "agree" => some .agree
  | _ => none

/-- Type introducing the options passed on to the solver. -/
structure BlasterOptions where
  /-- The number of unfolding steps to be considered when
      unfolding a recursive function. It is set to 100 by default. -/
  unfoldDepth : Nat := 100

  /-- The solving timeout in seconds. An explicit value wins; otherwise,
      `BLASTER_TIMEOUT` is trimmed. An unset or blank value means unlimited,
      while any nonblank value must be a natural number of seconds or resolution fails. -/
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
           - Description: In addition to Level 2, displays rewriting rules and the full SMT/model diagnostic pipeline.
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

  /-- Seed for the random number generator used in the solver.
      It is set to `none` by default (i.e., no seed). -/
   randomSeed : Option Nat := none

  /-- Backend SMT solver to be used (`z3` or `cvc5`).
      When set to `none` (the default), the solver is taken from the
      `BLASTER_SOLVER` environment variable if defined, and defaults to `z3` otherwise. -/
  solver : Option SmtSolver := none

  /-- Solver execution policy. Concurrent modes always use both Z3 and cvc5;
      there is deliberately no environment-variable override for this field. -/
  solverMode : SolverMode := .single

  /-- When set to `true`, trigger an error if the #solve command does not return a Falsified status. -/
  solveResult : ExpectedResult := .ExpectedValid

  /-- Permit cvc5 to return `Undetermined` for an explicitly allowlisted test while
      retaining `solveResult` as the expected result when the solver decides it. -/
  allowCvc5Undetermined : Bool := false

  /-- Maximum analysis depth to be considered when performing BMC and K-Induction.
      It is set to 10 by default. -/
  maxDepth : Nat := 10
 deriving Repr

instance : Inhabited BlasterOptions where
  default := {}

end Blaster.Options
