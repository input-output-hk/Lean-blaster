import Lean
import Solver.Optimize.Basic
import Solver.Command.Syntax

open Lean Elab Command Term Meta Solver.Options Solver.Syntax

namespace Tests
/-- Parse a term syntax. -/
def parseTerm (stx : Syntax) : TermElabM Expr := elabTermAndSynthesize stx none

/-- Parse a term syntax and call optimize. -/
def callOptimize (sOpts : SolverOptions) (stx : Syntax) : TermElabM Expr := do
  let optRes ← (Solver.Optimize.optimize sOpts (← parseTerm stx))
  pure optRes.1

/-! ## Definition of #testOptimize command to write unit test for Solver.optimize
    The #testOptimize usage is as follows:
     #testOptimize [ "TestName" ] (verbose: num)? TermToOptimize ==> OptimizedTerm

    with optional argument `verbose` to activate debug info

    E.g.
     #testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ==> ∀ (a : Prop), a
-/
syntax testName := "[" str "]"
syntax termReducedTo := term  "===>" term
syntax normNatLitOption := ("(norm-nat-in-result:" num ")")?
syntax (name := testOptimize) "#testOptimize" testName solveVerbose normNatLitOption termReducedTo : command

def parseTestName : TSyntax `testName -> CommandElabM String
 | `(testName| [ $s:str ]) => pure s.getString
 | _ => throwUnsupportedSyntax

def parseTermReducedTo : TSyntax `termReducedTo -> CommandElabM (Syntax × Syntax)
|`(termReducedTo | $t1 ===> $t2) => pure (t1.raw, t2.raw)
| _ => throwUnsupportedSyntax

def parseNormNatLitOption : TSyntax `normNatLitOption -> CommandElabM Bool
 | `(normNatLitOption| (norm-nat-in-result: $n:num)) => do
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
                     k (Expr.updateLet! e t' v' b') ) ) )
   | Expr.mdata _ e => k e
   | Expr.proj _ _ p =>
       visit p (fun p' => k (Expr.updateProj! e p'))
   | _ => k e
  visit e id

/-- Only normalizing Nat literals in `e`. -/
partial def normNatLit (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.const ``Nat.zero _ => return (mkRawNatLit 0)
    | Expr.app .. =>
       Expr.withApp e fun f args => do
        let mut margs := args
        for i in [:args.size] do
          margs ← margs.modifyM i visit
        match f with
        | Expr.const n@`OfNat.ofNat l =>
          let cInfo@(ConstantInfo.defnInfo _) ← getConstInfo n
            | throwError "normNatLit: defnInfo expected for OfNat.ofNat"
          let fbody ← instantiateValueLevelParams cInfo l
          visit (Expr.beta fbody margs)
        | _ => return mkAppN f margs
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
     let expected ← if normNatFlag then normNatLit expected' else pure expected'
     if actual == expected
     then logInfo f!"{name} ✓ Success!"
     else logError f!"{name} ✗ Failure! : expecting {reprStr expected} \nbut got {reprStr actual}"

end Tests
