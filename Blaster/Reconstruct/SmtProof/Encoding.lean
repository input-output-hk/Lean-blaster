import Blaster.Reconstruct.Checked
import Blaster.Reconstruct.SmtProof.Bridge

/-! A checked contract for the main assertion, prepared before Z3 is called. -/

open Lean Meta Elab Term

namespace Blaster.Reconstruct.SmtProof

/-- Source provenance and a kernel-checked transport for an SMT input assertion.
    `transport` proves `¬source → proposition` in the current Lean context. -/
structure CheckedGoalEncoding where
  source : Expr
  formula : STerm
  proposition : Expr
  transport : Expr

/-- Certify the main, final assertion of the translated query. Unsupported
    encodings keep the existing reconstruction path during this experiment. -/
def prepareGoalEncoding? (source translated : Expr) (commands : Array SExpr)
    (table : SymTable) (cfg : Bridge.Cfg) : TermElabM (Option CheckedGoalEncoding) := do
  let saved ← saveState
  tryCatchRuntimeEx (do
    let some (.list #[.atom "assert", assertion]) := commands.back?
      | throwError "encoding contract: missing main assertion"
    unless ← withDefault (isDefEq source translated) do
      throwError "encoding contract: source and translated goal differ"
    let formula ← ofExcept (STerm.ofSExpr {} assertion)
    let proposition ← (interpProp formula).run { table }
    unless ← isProp proposition do throwError "encoding contract: expected a proposition"
    let transport ← withLocalDeclD `hneg (mkNot source) fun h => do
      let proof ← if ← withDefault (isDefEq (mkNot source) proposition) then
        mkExpectedTypeHint h proposition
      else do
        let (some equality, _) ← Bridge.prove cfg (mkNot translated) proposition
          | throwError "encoding contract: unsupported bridge"
        mkEqMP equality (← mkExpectedTypeHint h (mkNot translated))
      mkLambdaFVars #[h] proof
    let expected ← mkArrow (mkNot source) proposition
    if let some error ← Blaster.Reconstruct.kernelCheck expected transport then throwError error
    return some { source, formula, proposition, transport }) fun _ => do
      saved.restore
      return none

end Blaster.Reconstruct.SmtProof
