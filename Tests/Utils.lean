import Lean
import Blaster.Optimize.Basic
import Blaster

open Lean Elab Command Term Meta Blaster.Options Blaster.Syntax

namespace Tests
/-- Parse a term syntax. -/
def parseTerm (stx : Syntax) : TermElabM Expr := elabTermAndSynthesize stx none

/-- Parse a term syntax and call optimize. -/
def callOptimize (sOpts : BlasterOptions) (stx : Syntax) : TermElabM Expr :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
    let optRes ← (Blaster.Optimize.command sOpts (← parseTerm stx))
    pure optRes.1

/-! ## Definition of #testOptimize command to write unit test for Blaster.optimize
    The #testOptimize usage is as follows:
     #testOptimize [ "TestName" ] (verbose: num)? (norm-result: num)? TermToOptimize ==> OptimizedTerm

    with options:
     - verbose: activate debug info
     - norm-result: apply nat literal normalization, beta reduction on lambda application
                    and structure projection normalization on expected result.

    E.g.
     #testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ==> ∀ (a : Prop), a
-/
syntax testName := "[" str "]"
syntax termReducedTo := term  "===>" term
syntax normNatLitOption := ("(norm-result:" num ")")?
syntax (name := testOptimize) "#testOptimize" testName solveOption* normNatLitOption termReducedTo : command

def parseTestName : TSyntax `testName -> CommandElabM String
 | `(testName| [ $s:str ]) => pure s.getString
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

@[command_elab testOptimize]
def testOptimizeImp : CommandElab := fun stx => do
 let name ← parseTestName ⟨stx[1]⟩
 let sOpts ← parseVerbose default ⟨stx[2]⟩
 let normNatFlag ← parseNormNatLitOption ⟨stx[3]⟩
 let (t1, t2) ← parseTermReducedTo ⟨stx[4]⟩
 withoutModifyingEnv $ runTermElabM fun _ => do
   -- create a local declaration name for the test case
   let m ← getMainModule
   withDeclName (m ++ name.toName) $ do
     let actual ← callOptimize sOpts t1
     let expected' := removeAnnotations (← parseTerm t2)
     -- keep the current name generator and restore it afterwards
     let ngen ← getNGen
     let expected ← if normNatFlag then normNatLitAndLambdaBeta expected' else pure expected'
     -- restore name generator
     setNGen ngen
     if actual == expected
     then logInfo f!"{name} ✅ Success!"
     else logError f!"{name} ❌ Failure! : expecting {reprStr expected} \nbut got {reprStr actual}"

end Tests
