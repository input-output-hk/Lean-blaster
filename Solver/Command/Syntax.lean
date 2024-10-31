import Lean
import Solver.Command.Options
import Solver.Smt.Translate
import Solver.Logging

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Syntax

/-! ## Definition of #solve command that optimizes a lean theorem and calls
    the backend Smt solver on the remaining unsolved goals.
    The #solve usage is as follows:
     #solve (unfold-depth: num)? (timeout: num)? (verbose: num)? (only-smt-lib: bool)? [term]

    with:
      - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
      - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
      - `verbose:` activating debug info (default: 0)
      - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: false)

    E.g.
     #testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ==> ∀ (a : Prop), a
-/
syntax solveUnfoldDepth := ("(unfold-depth:" num ")")?
syntax solveTimeout := ("(timeout:" num ")")?
syntax solveVerbose := ("(verbose:" num ")")?
syntax solveSMTLib := ("(only-smt-lib:" char ")")?

-- NOTE: Limited to one term for the time being
syntax solveTerm := "[" term "]"
syntax (name := solve) "#solve" solveUnfoldDepth solveTimeout solveVerbose solveSMTLib solveTerm : command

def parseUnfoldDepth (sOpts : SolverOptions) : TSyntax `solveUnfoldDepth -> CommandElabM SolverOptions
 | `(solveUnfoldDepth| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
 | `(solveUnfoldDepth| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseTimeout (sOpts : SolverOptions) : TSyntax `solveTimeout -> CommandElabM SolverOptions
 | `(solveTimeout| (timeout: $n:num)) => return { sOpts with timeout := n.getNat }
 | `(solveTimeout| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseVerbose (sOpts : SolverOptions) : TSyntax `solveVerbose -> CommandElabM SolverOptions
 | `(solveVerbose| (verbose: $n:num)) => return { sOpts with verbose := n.getNat }
 | `(solveVerbose| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseSmtLib (sOpts : SolverOptions) : TSyntax `solveSMTLib -> CommandElabM SolverOptions
 | `(solveSMTLib| (only-smt-lib: $b:char)) => do
       match b.getChar with
        | 't' => return { sOpts with onlySmtLib := true }
        | 'f' => return { sOpts with onlySmtLib := false }
        | _ => throwUnsupportedSyntax
 | `(solveSMTLib| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseTerm : TSyntax `Solver.solveTerm -> CommandElabM Syntax
  |`(solveTerm| [ $th ]) => pure th.raw
  | _ => throwUnsupportedSyntax

@[command_elab solve]
def solveImp : CommandElab := fun stx => do
  let sOpts ← parseSmtLib (← parseVerbose (← parseTimeout (← parseUnfoldDepth default ⟨stx[1]⟩) ⟨stx[2]⟩) ⟨stx[3]⟩) ⟨stx[4]⟩
  let tr ← parseTerm ⟨stx[5]⟩
  withoutModifyingEnv $ runTermElabM fun _ =>
    Solver.Smt.translate sOpts tr

end Solver.Syntax

