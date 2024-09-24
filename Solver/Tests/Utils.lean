import Lean
import Solver.Optimize.Basic
import Solver.Command.Syntax

open Lean Elab Command Term Meta

namespace Tests
/-- Parse a term syntax. -/
def parseTerm (stx : Syntax) : TermElabM Expr := elabTermAndSynthesize stx none

/-- Parse a term syntax and call optimize. -/
def callOptimize (sOpts : Solver.SolverOptions) (stx : Syntax) : TermElabM Expr := do
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
syntax (name := testOptimize) "#testOptimize" testName Solver.solveVerbose termReducedTo : command

def parseTestName : TSyntax `testName -> CommandElabM String
 | `(testName| [ $s:str ]) => pure s.getString
 | _ => throwUnsupportedSyntax

def parseTermReducedTo : TSyntax `termReducedTo -> CommandElabM (Syntax × Syntax)
|`(termReducedTo | $t1 ===> $t2) => pure (t1.raw, t2.raw)
| _ => throwUnsupportedSyntax

@[command_elab testOptimize]
def testOptimizeImp : CommandElab := fun stx => do
 let name ← parseTestName ⟨stx[1]⟩
 let sOpts ← Solver.parseVerbose default ⟨stx[2]⟩
 let (t1, t2) ← parseTermReducedTo ⟨stx[3]⟩
 withoutModifyingEnv $ runTermElabM fun _ => do
   -- create a local declaration name for the test case
   let m ← getMainModule
   withDeclName (m ++ name.toName) $ do
     let actual ← callOptimize sOpts t1
     let expected ← parseTerm t2
     if actual == expected
     then logInfo f!"{name} ✓ Success!"
     else logError f!"{name} ✗ Failure! : expecting {reprStr expected} \nbut got {reprStr actual}"

end Tests
