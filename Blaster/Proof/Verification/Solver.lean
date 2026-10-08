import Blaster.Command.Tactic
import Blaster.Proof.Verification.Recursors

namespace Blaster.Proof.Verification.Solver
open Lean Meta Elab Blaster.Options Blaster.Smt Blaster.Optimize

/-- An actual Blaster optimizer/SMT invocation. Every unresolved verification
condition must receive `Valid`; timeout or translation-only modes cannot prove
an obligation. No application-specific prover callback is accepted. -/
def prove (target : Expr) (config : BlasterOptions) : TermElabM Expr := do
  if config.onlyOptimize || config.onlySmtLib || config.solveResult != .ExpectedValid then
    throwError "blaster verification requires solving every obligation with expected result Valid"
  let original := target
  let target ← Recursors.normalize target
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := config}
  let ((result, _), _) ←
    withTheReader Core.Context (fun context => {context with maxHeartbeats := 0}) do
      IO.setNumHeartbeats 0
      (Translate.main target (logUndetermined := false)).run env
  match result with
  | .Valid =>
    let proof := mkApp (mkConst ``Blaster.Tactic.blasterProven [← getLevel target]) target
    -- The solver checked the normalized representation. This annotation
    -- requires Lean to check its definitional equality to the original goal.
    return mkLet `originalGoal original proof (mkBVar 0)
  | .Falsified _ => throwError "blaster verification: Goal was falsified"
  | .Undetermined => throwError "blaster verification: obligation was not proved (Undetermined)"

end Blaster.Proof.Verification.Solver
