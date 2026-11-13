import Blaster.Reconstruct.OptimizeReplay
import Blaster.Reconstruct.Checked
import Blaster.Reconstruct.SmtProof.Driver

/-!
Connect TxPipe's optimizer certificates to Seungheon Oh's Z3 proof replay.
Only the goals actually left by certificate replay are sent to the proof backend.
This module does not use Seungheon's optimizer evidence engine.
-/
open Lean Meta Elab Term Blaster.Options Blaster.Optimize

namespace Blaster.Reconstruct

/-- Lower elaborated arithmetic operators to the SMT translator's vocabulary.
Every replacement is checked by definitional equality, including instance arguments.
Propositional optimizer rewrites must be justified by the certificate replay instead. -/
def lowerOperators (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun
    | .letE _ _ value body _ => return .visit (body.instantiate1 value)
    | e => return if e.isHeadBetaTarget then .visit e.headBeta else .continue) (post := fun t => do
    let args := t.getAppArgs
    let mut candidate := t
    let ty := args[0]?.getD (mkSort 0)
    let coreBin? (nat int : Name) : MetaM (Option Expr) := do
      if args.size != 6 then return none
      if ty.isConstOf ``Nat then return some (mkApp2 (mkConst nat) args[4]! args[5]!)
      if ty.isConstOf ``Int then return some (mkApp2 (mkConst int) args[4]! args[5]!)
      return none
    match t.getAppFn.constName? with
    | some ``OfNat.ofNat =>
        if args.size == 3 then
          if ty.isConstOf ``Nat then candidate := args[1]!
          else if ty.isConstOf ``Int then candidate := mkApp (mkConst ``Int.ofNat) args[1]!
    | some ``HAdd.hAdd => candidate := (← coreBin? ``Nat.add ``Int.add).getD t
    | some ``HMul.hMul => candidate := (← coreBin? ``Nat.mul ``Int.mul).getD t
    | some ``HSub.hSub =>
        candidate := (← coreBin? ``Nat.sub ``Int.sub).getD t
        if ty.isConstOf ``Int && args.size == 6 then
          candidate := mkApp2 (mkConst ``Int.add) args[4]! (mkApp (mkConst ``Int.neg) args[5]!)
    | some ``HDiv.hDiv => candidate := (← coreBin? ``Nat.div ``Int.ediv).getD t
    | some ``HMod.hMod => candidate := (← coreBin? ``Nat.mod ``Int.emod).getD t
    | some ``HPow.hPow => candidate := (← coreBin? ``Nat.pow ``Int.pow).getD t
    | some ``HAppend.hAppend =>
        if ty.isConstOf ``String && args.size == 6 then
          candidate := mkApp2 (mkConst ``String.append) args[4]! args[5]!
    | some ``Option.isSome | some ``Ne | some ``GE.ge | some ``GT.gt =>
        candidate := ((← unfoldDefinition? t).getD t).headBeta
    | some ``Neg.neg =>
        if ty.isConstOf ``Int && args.size == 3 then candidate := mkApp (mkConst ``Int.neg) args[2]!
    | some ``Nat.cast =>
        if ty.isConstOf ``Int && args.size == 3 then candidate := mkApp (mkConst ``Int.ofNat) args[2]!
    | some ``Int.le | some ``Nat.le =>
        if args.size == 2 then candidate ← mkAppM ``LE.le args
    | some ``Int.lt | some ``Nat.lt =>
        if args.size == 2 then candidate ← mkAppM ``LT.lt args
    | _ => pure ()
    if candidate != t && (← withDefault <| isDefEq t candidate) then return .visit candidate
    return .done t)

/-- Prove the exact remaining goal, closing over its local declarations in dependency order. -/
def proveLeaf (g : MVarId) (sOpts : BlasterOptions) : TermElabM Unit := g.withContext do
  let target ← instantiateMVars (← g.getType)
  unless ← isProp target do throwError "Z3 reconstruction left a non-propositional metavariable"
  -- Do not turn an elaborator's recursive self reference into an SMT hypothesis.
  -- Include implementation-detail declarations only when an actual input depends on them.
  let inputs := (← getLCtx).decls.toArray.filterMap fun d =>
    d.bind fun d => if d.isImplementationDetail then none else some d.toExpr
  let decls ← fvarClosure (inputs.push target)
  let vars := decls.map (·.toExpr)
  let args := (decls.filter (!·.isLet)).map (·.toExpr)
  let original ← mkForallFVars vars target
  let closed ← lowerOperators original
  unless ← withDefault <| isDefEq original closed do
    throwError "SMT operator lowering changed the residual proposition"
  let result ← SmtProof.proveBySmtProof closed sOpts
  let r ← match result with
    | .ok r => pure r
    | .error msg => throwError "Z3 proof replay failed: {msg}"
  try
    if let some msg ← SmtProof.awaitKernelChecks r.kernelChecks then throwError msg
    let checked ← IO.mkRef r.sorryFree
    let proof ← match ← checkedProof checked closed r.proof with
      | .ok p => pure p
      | .error msg => throwError msg
    g.assign (mkAppN proof args)
    if let some file ← IO.getEnv "BLASTER_SMTPROOF_LOG" then
      let handle ← IO.FS.Handle.mk file .append
      let map ← getFileMap
      let line := ((← getRef).getPos?.map fun pos => (map.toPosition pos).line).getD 0
      handle.putStrLn (Json.compress (Json.mkObj
        [("kind", toJson "residual"), ("ok", toJson true), ("backend", toJson r.backend),
         ("steps", toJson r.steps), ("file", toJson (← getFileName)), ("line", toJson line)]))
    if sOpts.verbose > 0 then logInfo m!"Z3 proof replay: {r.backend}, {r.steps} steps"
  catch ex =>
    r.kernelChecks.cancel
    throw ex

/-- A complete proof of the original proposition, or a diagnostic. No trusted fallback here. -/
def reconstructGoal (goal : Expr) (steps : Array ProofStep) (binders : Array FVarId)
    (optimizerClosed : Bool) (sOpts : BlasterOptions) : TermElabM (Except MessageData Expr) := do
  let saved ← saveState
  tryCatchRuntimeEx (do
    let proof ← Blaster.Tactic.proveGoalByProofStack goal steps binders optimizerClosed
      (admit := false) (allowHoles := true)
    let pending ← getMVars (← instantiateMVars proof)
    for hole in pending do
      unless ← hole.isAssigned do proveLeaf hole sOpts
    let proof ← instantiateMVars proof
    if proof.hasMVar then throwError "the combined proof has unresolved metavariables"
    if ← dependsOnSorry proof then throwError "the combined proof depends on sorryAx"
    if let some msg ← kernelCheck goal proof then throwError msg
    let axioms ← exprAxioms proof
    if axioms.any (fun n => n == ``sorryAx || n.getString! == "blasterProven") then
      throwError "the combined proof contains a trusted-result axiom"
    if sOpts.genProof then
      match ← checkProofAxioms proof with
      | .error msg => throwError msg
      | .ok axs => logInfo m!"📜 Proof generated (axioms: {axs.toList})"
    else logInfo "🔒 Kernel-checked proof reconstructed"
    return .ok proof)
    (fun ex => do saved.restore; return .error ex.toMessageData)

/-- Checked command path; ordinary commands retain their existing solver behavior. -/
def command (sOpts : BlasterOptions) (stx : Syntax) : TermElabM Unit := do
  let e ← elabTermAndSynthesize stx none
  let goal ← match e.getAppFn with
    | .const n _ =>
        match ← getConstInfo n with
        | .thmInfo info => pure info.type
        | _ => pure e
    | _ => pure e
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let ((result, optExpr), finalEnv) ← Blaster.Smt.Translate.main goal |>.run env
  if result matches .Undetermined then
    if sOpts.reconstruct ≥ 2 && isExpectedValid sOpts.solveResult && !sOpts.onlySmtLib then
      throwError "blaster: strict reconstruction requires a valid result; got Undetermined"
  if result matches .Valid then
    match ← reconstructGoal goal finalEnv.optEnv.proofStack finalEnv.optEnv.optBinders
        (optExpr.isConstOf ``True) sOpts with
    | .ok _ => pure ()
    | .error msg =>
        if sOpts.reconstruct ≥ 2 then throwError msg
        logWarning m!"blaster: checked reconstruction failed: {msg}"

end Blaster.Reconstruct
