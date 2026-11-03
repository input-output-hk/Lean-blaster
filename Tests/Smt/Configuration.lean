import Blaster.Smt.Env

namespace Test.Configuration

open Blaster.Options Blaster.Smt

private def solverOptions (solver : SmtSolver) : BlasterOptions :=
  { solver := some solver }

private def timeoutOptions (timeout : Nat) : BlasterOptions :=
  { timeout := some timeout }

private def errorContains (fragment : String) : Except String α → Bool
  | .ok _ => false
  | .error message => (message.splitOn fragment).length > 1

private def resolvesToSolver (expected : SmtSolver) : Except String SmtSolver → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def resolvesToTimeout (expected : Option Nat) : Except String (Option Nat) → Bool
  | .ok actual => actual == expected
  | .error _ => false

/-! Solver precedence and parsing. Environment values accept surrounding
    whitespace, while solver names remain case-sensitive. -/

private def envUnsetSelectsZ3 : Bool :=
  resolvesToSolver .z3 (resolveSolverConfig default none)

private def cvc5EnvironmentSelectsCvc5 : Bool :=
  resolvesToSolver .cvc5 (resolveSolverConfig default (some "cvc5"))

private def explicitZ3OverridesCvc5Environment : Bool :=
  resolvesToSolver .z3 (resolveSolverConfig (solverOptions .z3) (some "cvc5"))

private def explicitSolverSkipsInvalidEnvironment : Bool :=
  resolvesToSolver .z3 (resolveSolverConfig (solverOptions .z3) (some "yices"))

private def surroundingSolverWhitespaceIsAccepted : Bool :=
  resolvesToSolver .cvc5 (resolveSolverConfig default (some "  cvc5 \t"))

private def mixedCaseSolverIsRejected : Bool :=
  errorContains "CVC5" (resolveSolverConfig default (some "CVC5"))

private def invalidSolverNamesValidChoices : Bool :=
  let result := resolveSolverConfig default (some "yices")
  errorContains "yices" result && errorContains "z3" result && errorContains "cvc5" result

private def emptySolverIsRejected : Bool :=
  errorContains "BLASTER_SOLVER" (resolveSolverConfig default (some "  "))

#guard envUnsetSelectsZ3
#guard cvc5EnvironmentSelectsCvc5
#guard explicitZ3OverridesCvc5Environment
#guard explicitSolverSkipsInvalidEnvironment
#guard surroundingSolverWhitespaceIsAccepted
#guard mixedCaseSolverIsRejected
#guard invalidSolverNamesValidChoices
#guard emptySolverIsRejected

/-! Timeout precedence and parsing. Environment values are trimmed; unset,
    empty, and whitespace-only values mean unlimited. Other values must be
    natural numbers of seconds. -/

private def unsetTimeoutIsUnlimited : Bool :=
  resolvesToTimeout none (resolveTimeoutConfig default none)

private def explicitTimeoutOverridesEnvironment : Bool :=
  resolvesToTimeout (some 7) (resolveTimeoutConfig (timeoutOptions 7) (some "99"))

private def explicitTimeoutSkipsInvalidEnvironment : Bool :=
  resolvesToTimeout (some 7) (resolveTimeoutConfig (timeoutOptions 7) (some "forever"))

private def surroundingTimeoutWhitespaceIsAccepted : Bool :=
  resolvesToTimeout (some 30) (resolveTimeoutConfig default (some "  30 \t"))

private def emptyTimeoutIsUnlimited : Bool :=
  resolvesToTimeout none (resolveTimeoutConfig default (some " \t "))

private def nonnumericTimeoutIsRejected : Bool :=
  let result := resolveTimeoutConfig default (some "forever")
  errorContains "forever" result && errorContains "number of seconds" result

#guard unsetTimeoutIsUnlimited
#guard explicitTimeoutOverridesEnvironment
#guard explicitTimeoutSkipsInvalidEnvironment
#guard surroundingTimeoutWhitespaceIsAccepted
#guard emptyTimeoutIsUnlimited
#guard nonnumericTimeoutIsRejected

end Test.Configuration
