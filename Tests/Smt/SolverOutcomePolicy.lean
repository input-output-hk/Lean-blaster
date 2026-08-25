import Blaster.Smt.Env

namespace Test.SolverOutcomePolicy

open Blaster.Options Blaster.Smt

private def outcome
    (solver : SmtSolver) (verdict : Option SolverVerdict)
    (status : SolverRunStatus := .completed)
    (counterexample : Option (List String) := none) : SolverOutcome :=
  { solver, verdict, status, counterexample }

private def agreesWith
    (expectedVerdict : SolverVerdict) (expectedStatus : SolverRunStatus)
    (result : Except AgreementFailure AgreementDecision) : Bool :=
  match result with
  | .ok decision => decision.verdict == expectedVerdict && decision.status == expectedStatus
  | .error _ => false

private def failsWith
    (expected : AgreementFailureKind)
    (result : Except AgreementFailure AgreementDecision) : Bool :=
  match result with
  | .ok _ => false
  | .error failure => failure.kind == expected

#guard agreesWith .valid .completed <|
  aggregateAgreement (outcome .z3 (some .valid)) (outcome .cvc5 (some .valid))

#guard agreesWith .falsified .completed <|
  aggregateAgreement (outcome .z3 (some .falsified)) (outcome .cvc5 (some .falsified))

#guard failsWith .hardDisagreement <|
  aggregateAgreement (outcome .z3 (some .valid)) (outcome .cvc5 (some .falsified))

#guard failsWith .incompleteDisagreement <|
  aggregateAgreement (outcome .z3 (some .valid)) (outcome .cvc5 (some .undetermined))

#guard failsWith .incompleteDisagreement <|
  aggregateAgreement (outcome .z3 (some .undetermined)) (outcome .cvc5 (some .falsified))

#guard agreesWith .undetermined .completed <|
  aggregateAgreement (outcome .z3 (some .undetermined)) (outcome .cvc5 (some .undetermined))

#guard failsWith .infrastructureFailure <|
  aggregateAgreement
    (outcome .z3 none .processFailed)
    (outcome .cvc5 (some .valid))

#guard failsWith .infrastructureFailure <|
  aggregateAgreement
    (outcome .z3 (some .valid))
    (outcome .cvc5 none .protocolFailed)

#guard failsWith .infrastructureFailure <|
  aggregateAgreement
    (outcome .z3 (some .undetermined) .timedOut)
    (outcome .cvc5 (some .undetermined))

private def modelFailurePreservesFalsified : Bool :=
  match aggregateAgreement
      (outcome .z3 (some .falsified) .modelFailed)
      (outcome .cvc5 (some .falsified) .completed (some ["x: 1"])) with
  | .ok decision =>
      decision.verdict == .falsified && decision.status == .modelFailed &&
        decision.counterexample == some ["x: 1"]
  | .error _ => false

#guard modelFailurePreservesFalsified

private def z3EvidenceWinsRegardlessOfCompletionOrder : Bool :=
  let z3 := outcome .z3 (some .falsified) .completed (some ["x: 3"])
  let cvc5 := outcome .cvc5 (some .falsified) .completed (some ["x: 4"])
  match aggregateAgreement cvc5 z3 with
  | .ok decision => decision.counterexample == some ["x: 3"]
  | .error _ => false

#guard z3EvidenceWinsRegardlessOfCompletionOrder

private def concurrentCvc5AllowanceDoesNotApply : Bool :=
  let options : BlasterOptions :=
    { solverMode := .agree, allowCvc5Undetermined := true }
  undeterminedAction options none false == .strictError

#guard concurrentCvc5AllowanceDoesNotApply

private def isError : Except String Unit → Bool
  | .error _ => true
  | .ok () => false

private def isOk (result : Except String Unit) : Bool := !isError result

private def explicitSolverConflictsWithFirst : Bool :=
  let options : BlasterOptions := { solver := some .z3, solverMode := .first }
  isError (validateSolverOptions options)

private def explicitSolverConflictsWithAgree : Bool :=
  let options : BlasterOptions := { solver := some .cvc5, solverMode := .agree }
  isError (validateSolverOptions options)

private def onlySmtLibConflictsWithConcurrentModes : Bool :=
  let first : BlasterOptions := { solverMode := .first, onlySmtLib := true }
  let agree : BlasterOptions := { solverMode := .agree, onlySmtLib := true }
  isError (validateSolverOptions first) && isError (validateSolverOptions agree)

#guard explicitSolverConflictsWithFirst
#guard explicitSolverConflictsWithAgree
#guard onlySmtLibConflictsWithConcurrentModes
#guard isOk (validateSolverOptions (default : BlasterOptions))

end Test.SolverOutcomePolicy
