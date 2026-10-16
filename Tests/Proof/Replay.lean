import Tests.Proof.Exploration
import Blaster.Proof.Explore.Proof

open Lean Meta Elab Command Blaster.Proof.Explore

run_cmd Command.liftTermElabM do
  withLocalDeclD `fuel (mkConst ``Nat) fun fuel => do
    let pred : Pred := {body := ← Lean.getConstInfoDefn ``explorationAccept >>= fun d => pure d.value,
                        arity := 0, eqn? := some ``explorationAccept_eq}
    let machine : Machine := {preds := ({} : Std.HashMap Name Pred).insert ``explorationAccept pred, fuel, pad := 1}
    let result ← Blaster.Proof.Explore.run machine (mkConst ``explorationAccept)
    let go : ExM Unit := do
      let plan ← mkPlan result (mkConst ``True) #[] (fun _ => pure (mkConst ``True))
      let proof ← inCtx <| mkAppM ``True.intro #[]
      let hobs ← inCtx <| mkExpectedTypeHint proof (mkApp (mkConst ``explorationAccept) (mkNatLit 1))
      let replayed ← provePlan plan hobs (mkNatLit 1) fun vc => do
        let g ← mkFreshExprMVar vc
        let tacticStx ← `(tactic| simp_all)
        let remaining ← (Elab.Tactic.run g.mvarId! <| Elab.Tactic.evalTactic tacticStx).run' {} {}
        unless remaining.isEmpty do throwError "unproved replay condition"
        instantiateMVars g
      let pr ← instantiateMVars replayed.proof
      inCtx <| check pr
      if replayed.hasSorry || pr.hasSorry then throwError "incomplete replay"
    discard <| go.run result.core
