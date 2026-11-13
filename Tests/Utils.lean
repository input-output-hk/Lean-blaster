import Lean
import Blaster.Command.Tactic

open Lean Elab Command Term Meta Blaster.Options Blaster.Syntax Blaster.Tactic

namespace Tests
/-- Parse a term syntax. -/
def parseTerm (stx : Syntax) : TermElabM Expr := elabTermAndSynthesize stx none

/-- Run the optimizer on an elaborated expression -/
def optimizeExpr (sOpts : BlasterOptions) (e : Expr) :
  TermElabM (Expr × Blaster.Optimize.TranslateEnv) :=
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
      Blaster.Optimize.command sOpts e

/-- Parse a term syntax and call optimize, returning both the optimized expression
    and the translation environment (which contains the proof stack). -/
def callOptimize (sOpts : BlasterOptions) (stx : Syntax) :
    TermElabM (Expr × Blaster.Optimize.TranslateEnv) := do
    optimizeExpr sOpts (← parseTerm stx)

/-! ## Definition of #testOptimize command to write unit test for Blaster.optimize
    The #testOptimize usage is as follows:
     #testOptimize [ "TestName" ] (verbose: num)? (norm-result: num)? TermToOptimize ===> OptimizedTerm
     #testOptimize [ "TestName", proof ] (verbose: num)? (norm-result: num)? TermToOptimize ===> OptimizedTerm

    with options:
     - verbose: activate debug info
     - norm-result: apply nat literal normalization, beta reduction on lambda application
                    and structure projection normalization on expected result.
     - proof: require that proof reconstruction succeeds for this test case.
              The optimizer's proof stack is replayed and the resulting goal
              must close via `refl` or `ac_rfl`, mirroring the `blaster` tactic.

    E.g.
     #testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ===> ∀ (a : Prop), a
     #testOptimize [ "NatAddZero", proof ] ∀ (x : Nat), 0 + x = x ===> True
-/
syntax testName := "[" str ("," "proof")? "]"
syntax termReducedTo := term  "===>" term
syntax normNatLitOption := ("(norm-result:" num ")")?
syntax (name := testOptimize) "#testOptimize" testName solveOption* normNatLitOption termReducedTo : command

/-- Parse test name and optional `proof` flag. -/
def parseTestName : TSyntax `testName → CommandElabM (String × Bool)
  | `(testName| [ $s:str , proof ]) => pure (s.getString, true)
  | `(testName| [ $s:str ]) => pure (s.getString, false)
  | _ => throwUnsupportedSyntax

def parseTermReducedTo : TSyntax `termReducedTo -> CommandElabM (Syntax × Syntax)
|`(termReducedTo | $t1 ===> $t2) => pure (t1.raw, t2.raw)
| _ => throwUnsupportedSyntax

def parseNormNatLitOption : TSyntax `normNatLitOption -> CommandElabM Bool
 | `(normNatLitOption| (norm-result: $n:num)) => do
       match n.getNat with
        | 0 => return false
        | 1 => return true
        | _ => throwUnsupportedSyntax
 | `(normNatLitOption| ) => return false
 | _ => throwUnsupportedSyntax


/-- Remove metadata annotations from `e`. -/
def removeAnnotations (e : Expr) : Expr :=
 let rec visit (e : Expr) (k : Expr → Expr) :=
   match e with
   | Expr.app f arg =>
       visit f
         (fun f' =>
           visit arg
             (fun arg' =>
               k (Expr.updateApp! e f' arg') ) )
   | Expr.lam _ t b bi =>
       visit t
         (fun t' =>
           visit b
             (fun b' =>
               k (Expr.updateLambda! e bi t' b') ) )
   | Expr.forallE _ t b bi =>
       visit t
         (fun t' =>
           visit b
             (fun b' =>
               k (Expr.updateForall! e bi t' b') ) )
   | Expr.letE _ t v b _ =>
         visit t
           (fun t' =>
             visit v
              (fun v' =>
                 visit b
                   (fun b' =>
                     k (Expr.updateLetE! e t' v' b') ) ) )
   | Expr.mdata _ e => k e
   | Expr.proj _ _ p =>
       visit p (fun p' => k (Expr.updateProj! e p'))
   | _ => k e
  visit e id

/-- Apply the following normalization on expected result:
     - normalize Nat literals in `e`
     - Beta reduced lambda application.
     - Normalize structure projection
-/
partial def normNatLitAndLambdaBeta (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.const ``Nat.zero _ => return (mkRawNatLit 0)
    | Expr.app .. =>
       Expr.withApp e fun f args => do
        let mut margs := args
        for i in [:args.size] do
          margs ← margs.modifyM i visit
        match f with
        | Expr.const n l =>
            match n with
            | `OfNat.ofNat =>
               let cInfo@(ConstantInfo.defnInfo _) ← getConstInfo n
                 | throwError "normNatLit: defnInfo expected for OfNat.ofNat"
               let fbody ← instantiateValueLevelParams cInfo l
               visit (Expr.beta fbody margs)
            | _ =>
              match ← getConstInfo n with
              | cInfo@(ConstantInfo.defnInfo _) =>
                  let fbody ← instantiateValueLevelParams cInfo l
                  let reduced := Expr.beta fbody margs
                  match reduced with
                  | Expr.proj n _idx _s =>
                     if isStructureLike (← getEnv) n
                     then return reduced
                     else return mkAppN f margs
                  | _ => return mkAppN f margs
              | _ => return mkAppN f margs


        | _ =>
          if f.isLambda
          then return Expr.beta f args
          else return mkAppN f margs
    | Expr.lam n t b bi =>
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          mkLambdaFVars #[x] (← visit (b.instantiate1 x))
    | Expr.forallE n t b bi =>
        withLocalDecl n bi (← visit t) fun x => do
          mkForallFVars #[x] (← visit (b.instantiate1 x))
    | Expr.letE n t v b _ =>
       withLetDecl n (← visit t) (← visit v) fun x => do
         mkLetFVars #[x] (← visit (b.instantiate1 x))
    | Expr.mdata _ e => return e
    | Expr.proj `OfNat _ _ =>
       let some re ← reduceProj? e
         | throwError "normNatLit: ofNat projection expected to be reduced !!!"
       return re
    | _ => return e
  visit e

/-- Return `true` if the expression contains `sorryAx` anywhere.
    Tail recursive on a stack of pending subterms, so a deep `e` cannot overflow. -/
private partial def containsSorry (e : Expr) : Bool :=
  go [e]
where
  go : List Expr → Bool
  | [] => false
  | .const ``sorryAx _ :: _ => true
  | .app f a :: es => go (f :: a :: es)
  | .lam _ t b _ :: es => go (t :: b :: es)
  | .forallE _ t b _ :: es => go (t :: b :: es)
  | .letE _ t v b _ :: es => go (t :: v :: b :: es)
  | .mdata _ e :: es => go (e :: es)
  | .proj _ _ e :: es => go (e :: es)
  | _ :: es => go es

/-- Prove `inputExpr = expected`, or `inputExpr` when `expected` is `True`, from the proof stack
    of `inputExpr` with `proveGoalByProofStack`, the path of `blaster`, and `admit := false`.
    `expected` is the term the test writes, so the goal has the user binder names, as for
    `blaster` on `inputExpr = expected`.
    The proof is accepted only if it is complete, sorry-free, has no fvar outside the context,
    passes `Meta.check` and has the goal type. Returns the failure reason, if any. -/
private def checkReconstruction (inputExpr : Expr) (expected : Expr)
    (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) : TermElabM (Option MessageData) := do
  let optimizerClosed := expected.isConstOf ``True
  let goalType ← if optimizerClosed then pure inputExpr else mkEq inputExpr expected
  try
    let pf ← instantiateMVars
      (← proveGoalByProofStack goalType proofStack optBinders optimizerClosed (admit := false))
    if pf.hasMVar then return some m!"the proof term has unassigned metavariables"
    if containsSorry pf then return some m!"the proof term contains sorry"
    let lctx ← getLCtx
    if (collectFVars {} pf).fvarIds.any (fun f => !lctx.contains f) then
      return some m!"the proof term has loose free variables"
    check pf
    unless ← isDefEq (← inferType pf) goalType do
      return some m!"type {← inferType pf} does not match the goal {goalType}"
    return none
  catch ex => return some ex.toMessageData

@[command_elab testOptimize]
def testOptimizeImp : CommandElab := fun stx => do
  let (name, requireProof) ← parseTestName ⟨stx[1]⟩
  let sOpts ← parseVerbose default ⟨stx[2]⟩
  let normNatFlag ← parseNormNatLitOption ⟨stx[3]⟩
  let (t1, t2) ← parseTermReducedTo ⟨stx[4]⟩
  withoutModifyingEnv $ runTermElabM fun _ => do
    -- create a local declaration name for the test case
    let m ← getMainModule
    withDeclName (m ++ name.toName) $ do
      let inputExpr ← parseTerm t1
      let (actual, env) ← optimizeExpr sOpts inputExpr
      let expected' := removeAnnotations (← parseTerm t2)
      -- keep the current name generator and restore it afterwards
      let ngen ← getNGen
      let expected ← if normNatFlag then normNatLitAndLambdaBeta expected' else pure expected'
      -- restore name generator
      setNGen ngen
      if actual == expected then
        if requireProof then
          let proofStack := env.optEnv.proofStack
          let optBinders := env.optEnv.optBinders
          match ← checkReconstruction inputExpr expected proofStack optBinders with
          | none => logInfo f!"{name} ✅ Success! [proof ✓]"
          | some msg => logError m!"{name} ❌ Failure! : proof reconstruction failed\n  {msg}"
        else
          logInfo f!"{name} ✅ Success!"
      else
        logError f!"{name} ❌ Failure! : expecting {reprStr expected} \nbut got {reprStr actual}"

end Tests
