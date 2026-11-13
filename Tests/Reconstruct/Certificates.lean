import Blaster
import Blaster.Reconstruct.SmtProof.Farkas
import Blaster.Reconstruct.SmtProof.Encoding

set_option warningAsError true

namespace Tests.Reconstruct.Certificates

open Lean Meta Elab Tactic Blaster.Reconstruct.SmtProof in
elab "certificate_farkas " coefficients:str : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let cs ← ofExcept (parseSExprs coefficients.getString)
    let mut facts := #[]
    for d in ← getLCtx do
      if !d.isImplementationDetail && (← isProp d.type) then
        facts := facts.push (d.type, d.toExpr)
    let step : Step := { rule := "th-lemma", attrs := #[.atom "arith", .atom "farkas"] ++ cs,
                         concl := .sym "unused" }
    let target ← goal.getType
    let some proof ← Farkas.replay? step facts target
      | throwError "certificate rejected"
    if let some error ← Blaster.Reconstruct.kernelCheck target proof then throwError error
    goal.assign proof
    replaceMainGoal []

theorem strict_conflict (x : Int) (h₁ : 0 ≤ x) (h₂ : x < 0) : False := by
  certificate_farkas "1 1"

theorem transitive_bound (x y z : Int) (h₁ : x + 2 ≤ y) (h₂ : y + 3 ≤ z) : x + 5 ≤ z := by
  certificate_farkas "1 1 1"

theorem clause (x : Int) : 0 ≤ x ∨ x ≤ 0 := by
  certificate_farkas "1 1"

theorem signed_equality (x : Int) (h₁ : x = 0) (h₂ : 1 ≤ x) : False := by
  certificate_farkas "-1 1"

theorem rational_weights (x : Int) (h₁ : 2 * x < 0) (h₂ : 0 ≤ x) : False := by
  certificate_farkas "(/ 1 2) 1"

theorem decimal_weights (x : Int) (h₁ : 2 * x < 0) (h₂ : 0 ≤ x) : False := by
  certificate_farkas "0.5 1.0"

-- Rejection is checked on an actually contradictory context: another tactic
-- could solve it, but this certificate-directed path must reject bad hints.
theorem altered_certificates (x : Int) (h₁ : 0 ≤ x) (h₂ : x < 0) : False := by
  fail_if_success certificate_farkas "1 2"
  fail_if_success certificate_farkas "0 0"
  fail_if_success certificate_farkas "1"
  fail_if_success certificate_farkas "1 (/ 1 0)"
  fail_if_success certificate_farkas "bad 1"
  certificate_farkas "1 1"

-- A nonnegative constant is not a contradiction, and an unproved premise is
-- never recovered by a tactic portfolio in this test command.
example (x : Int) (_h₁ : 0 ≤ x) (_h₂ : x ≤ 1) : True := by
  fail_if_success
    have impossible : False := by certificate_farkas "1 1"
  trivial

-- The input bridge is certified without a solver proof. Incorrect provenance
-- and an unrelated assertion must both fail to obtain an encoding contract.
open Lean Meta Elab Command Blaster.Reconstruct.SmtProof in
run_cmd liftTermElabM do
  withLocalDeclD `x (mkConst ``Int) fun x =>
    withLocalDeclD `y (mkConst ``Int) fun y => do
      let source := mkIntLe x y
      let syms := ({} : Std.HashMap String SymInterp) |>.insert "x" (.expr x) |>.insert "y" (.expr y)
      let table : SymTable := { syms }
      let commands ← ofExcept (parseSExprs "(assert (not (<= x y)))")
      let some _ ← prepareGoalEncoding? source source commands table {}
        | throwError "valid input encoding was rejected"
      if (← prepareGoalEncoding? source (mkIntLe y x) commands table {}).isSome then
        throwError "incorrect source provenance was accepted"
      let bad ← ofExcept (parseSExprs "(assert false)")
      if (← prepareGoalEncoding? source source bad table {}).isSome then
        throwError "an unrelated input assertion was accepted"

open Lean Elab Command in
run_cmd do
  for name in [``strict_conflict, ``transitive_bound, ``clause, ``signed_equality,
      ``rational_weights, ``decimal_weights, ``altered_certificates,
      ``Z3Certificate.IntFarkas.check_sound] do
    let axioms ← liftCoreM (collectAxioms name)
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected axioms for {name}: {axioms.toList}"

end Tests.Reconstruct.Certificates
