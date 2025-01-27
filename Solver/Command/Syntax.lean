import Lean
import Solver.Command.Options
import Solver.Smt.Translate

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Syntax

/-! ## Definition of #solve command that optimizes a lean theorem and calls
    the backend Smt solver on the remaining unsolved goals.
    The #solve usage is as follows:
     #solve (unfold-depth: num)? (timeout: num)?
            (verbose: num)? (only-smt-lib: num)? (only-optimize: num)?
            (dump-smt-lib: num)? (gen-cex: num)? (solve-result: num)? [term]

    with:
      - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
      - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
      - `verbose:` activating debug info (default: 0)
      - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
      - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
      - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
      - `gen-cex`: generate counterexample for falsified theorems (default: 1)
      - `solve-result`: specify the expected result from the #solve command, i.e.,
                        0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)
    E.g.
     #solve [∀ x y : Nat, x + y > x]
-/
syntax solveUnfoldDepth := ("(unfold-depth:" num ")")?
syntax solveTimeout := ("(timeout:" num ")")?
syntax solveVerbose := ("(verbose:" num ")")?
syntax solveSMTLib := ("(only-smt-lib:" num ")")?
syntax solveOptimize := ("(only-optimize:" num ")")?
syntax solveDumpSmt := ("(dump-smt-lib:" num ")")?
syntax solveGenCex := ("(gen-cex:" num ")")?
syntax solveResult := ("(solve-result:" num ")")?

-- NOTE: Limited to one term for the time being
syntax solveTerm := "[" term "]"
syntax (name := solve) "#solve"
  solveUnfoldDepth solveTimeout
  solveVerbose solveSMTLib solveOptimize solveDumpSmt solveGenCex
  solveResult solveTerm : command

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
 | `(solveSMTLib| (only-smt-lib: $n:num)) => do
       match n.getNat with
        | 0 => return { sOpts with onlySmtLib := false }
        | 1 => return { sOpts with onlySmtLib := true }
        | _ => throwUnsupportedSyntax
 | `(solveSMTLib| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseOptimize (sOpts : SolverOptions) : TSyntax `solveOptimize -> CommandElabM SolverOptions
 | `(solveOptimize| (only-optimize: $n:num)) => do
       match n.getNat with
        | 0 => return { sOpts with onlyOptimize := false }
        | 1 => return { sOpts with onlyOptimize := true }
        | _ => throwUnsupportedSyntax
 | `(solveOptimize| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseDumpSmt (sOpts : SolverOptions) : TSyntax `solveDumpSmt -> CommandElabM SolverOptions
 | `(solveDumpSmt| (dump-smt-lib: $n:num)) => do
       match n.getNat with
        | 0 => return { sOpts with dumpSmtLib := false }
        | 1 => return { sOpts with dumpSmtLib := true }
        | _ => throwUnsupportedSyntax
 | `(solveDumpSmt| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseGenCex (sOpts : SolverOptions) : TSyntax `solveGenCex -> CommandElabM SolverOptions
 | `(solveGenCex| (gen-cex: $n:num)) => do
       match n.getNat with
        | 0 => return { sOpts with generateCex := false }
        | 1 => return { sOpts with generateCex := true }
        | _ => throwUnsupportedSyntax
 | `(solveGenCex| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseSolveResult (sOpts : SolverOptions) : TSyntax `solveResult -> CommandElabM SolverOptions
 | `(solveResult| (solve-result: $n:num)) => do
       match n.getNat with
        | 0 => return { sOpts with solveResult := .ExpectedValid }
        | 1 => return { sOpts with solveResult := .ExpectedFalsified }
        | 2 => return { sOpts with solveResult := .ExpectedUndetermined }
        | _ => throwUnsupportedSyntax
 | `(solveResult| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseTerm : TSyntax `Solver.solveTerm -> CommandElabM Syntax
  |`(solveTerm| [ $th ]) => pure th.raw
  | _ => throwUnsupportedSyntax

@[command_elab solve]
def solveImp : CommandElab := fun stx => do
  let sOpts ← parseVerbose (← parseTimeout (← parseUnfoldDepth default ⟨stx[1]⟩) ⟨stx[2]⟩) ⟨stx[3]⟩
  let sOpts ← parseDumpSmt (← parseOptimize (← parseSmtLib sOpts ⟨stx[4]⟩) ⟨stx[5]⟩) ⟨stx[6]⟩
  let sOpts ← parseSolveResult (← parseGenCex sOpts ⟨stx[7]⟩) ⟨stx[8]⟩
  let tr ← parseTerm ⟨stx[9]⟩
  withoutModifyingEnv $ runTermElabM fun _ =>
    Solver.Smt.translate sOpts tr

end Solver.Syntax

