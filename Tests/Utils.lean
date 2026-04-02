import Lean
import Blaster.Optimize.Basic
import Blaster

open Lean Elab Command Term Meta Blaster.Options Blaster.Syntax

namespace Tests
/-- Parse a term syntax. -/
def parseTerm (stx : Syntax) : TermElabM Expr := elabTermAndSynthesize stx none

/-- Parse a term syntax and call optimize, returning both the optimized expression
    and the translation environment (which contains the proof stack). -/
def callOptimize (sOpts : BlasterOptions) (stx : Syntax) :
    TermElabM (Expr × Blaster.Optimize.TranslateEnv) :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
    Blaster.Optimize.command sOpts (← parseTerm stx)

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

/-- Replay the proof stack and attempt to close the goal, mirroring the
    `blaster` tactic closing strategy exactly: try `refl`, otherwise report failure.
    Returns `true` when the goal is closed without sorry. -/
private def replayProofStack (inputExpr : Expr) (optimized : Expr)
    (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) : TermElabM Bool := do
  let isPropInput ← isProp inputExpr
  let isOptTrue := optimized.isConstOf ``True
  let (goalType, numBinders) ←
    if isPropInput && isOptTrue then
      let n ← forallTelescope inputExpr fun fvars _ => pure fvars.size
      pure (inputExpr, n)
    else if isPropInput then
      let n ← forallTelescope inputExpr fun fvars _ => pure fvars.size
      let gt ← forallTelescope inputExpr fun inputFvars inputBody => do
        let optBody ← forallBoundedTelescope optimized (some n) fun optFvars optBody =>
          pure (optBody.replaceFVars optFvars inputFvars)
        let eq ← mkEq inputBody optBody
        mkForallFVars inputFvars eq
      pure (gt, n)
    else
      let gt ← mkEq inputExpr optimized
      let n ← forallTelescope gt fun fvars _ => pure fvars.size
      pure (gt, n)
  let goal ← mkFreshExprMVar goalType
  let goalId := goal.mvarId!
  let (goalFVarIds, g) ← goalId.introNP numBinders
  let proofStack := Blaster.Tactic.substProofStackFVars proofStack optBinders goalFVarIds
  let g ← Blaster.Tactic.applyProofStack g proofStack
  if ← g.isAssigned then return true
  try g.refl; return true
  catch _ => return false

/-- Build the remaining goal after proof stack application (for error reporting). -/
private def showRemainingGoal (inputExpr : Expr) (optimized : Expr)
    (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) : TermElabM MessageData := do
  let isPropInput ← isProp inputExpr
  let isOptTrue := optimized.isConstOf ``True
  let (goalType, numBinders) ←
    if isPropInput && isOptTrue then
      let n ← forallTelescope inputExpr fun fvars _ => pure fvars.size
      pure (inputExpr, n)
    else if isPropInput then
      let n ← forallTelescope inputExpr fun fvars _ => pure fvars.size
      let gt ← forallTelescope inputExpr fun inputFvars inputBody => do
        let optBody ← forallBoundedTelescope optimized (some n) fun optFvars optBody =>
          pure (optBody.replaceFVars optFvars inputFvars)
        let eq ← mkEq inputBody optBody
        mkForallFVars inputFvars eq
      pure (gt, n)
    else
      let gt ← mkEq inputExpr optimized
      let n ← forallTelescope gt fun fvars _ => pure fvars.size
      pure (gt, n)
  let goal ← mkFreshExprMVar goalType
  let gid := goal.mvarId!
  let (goalFVarIds, g) ← gid.introNP numBinders
  let proofStack := Blaster.Tactic.substProofStackFVars proofStack optBinders goalFVarIds
  let g ← Blaster.Tactic.applyProofStack g proofStack
  if ← g.isAssigned then return "goal closed by proof stack"
  g.withContext (ppExpr (← g.getType))

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
      let (actual, env) ← callOptimize sOpts t1
      let expected' := removeAnnotations (← parseTerm t2)
      -- keep the current name generator and restore it afterwards
      let ngen ← getNGen
      let expected ← if normNatFlag then normNatLitAndLambdaBeta expected' else pure expected'
      -- restore name generator
      setNGen ngen
      if actual == expected then
        if requireProof then
          -- Re-elaborate to obtain the original (pre-optimization) expression
          let inputExpr ← parseTerm t1
          let proofStack := env.optEnv.proofStack
          let optBinders := env.optEnv.optBinders
          let closed ← replayProofStack inputExpr actual proofStack optBinders
          if closed then
            logInfo f!"{name} ✅ Success! [proof ✓]"
          else
            let remainingGoal ← showRemainingGoal inputExpr actual proofStack optBinders
            logError m!"{name} ❌ Failure! : proof reconstruction failed\n  remaining goal: {remainingGoal}"
        else
          logInfo f!"{name} ✅ Success!"
      else
        logError f!"{name} ❌ Failure! : expecting {reprStr expected} \nbut got {reprStr actual}"

end Tests
