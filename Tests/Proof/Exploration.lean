import Blaster.Proof.Explore.Search
import Blaster.Proof.Explore.Success

open Lean Meta Elab Command Blaster.Proof.Explore

def explorationAccept (_ : Nat) : Prop := True
theorem explorationAccept_eq : explorationAccept = fun _ => True := rfl

run_cmd Command.liftTermElabM do
  withLocalDeclD `fuel (mkConst ``Nat) fun fuel => do
    let pred : Pred := {body := ← Lean.getConstInfoDefn ``explorationAccept >>= fun d => pure d.value,
                        arity := 0, eqn? := some ``explorationAccept_eq}
    let machine : Machine := {preds := ({} : Std.HashMap Name Pred).insert ``explorationAccept pred, fuel, pad := 1}
    let result ← Blaster.Proof.Explore.run machine (mkConst ``explorationAccept)
    unless result.search.stats.accepts == 1 do throwError "expected one accepting state"
