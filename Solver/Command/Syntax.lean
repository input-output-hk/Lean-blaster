import Lean
import Solver.Command.Options
import Solver.Translate.Basic
import Solver.Logging

open Lean Elab Command Term Meta

namespace Solver

syntax solveUnfoldDepth := ("(unfold-depth:" num ")")?
syntax solveTimeout := ("(timeout:" num ")")?
syntax solveVerbose := ("(verbose:" num ")")?

-- NOTE: Limited to one term for the time being
syntax solveTerm := "[" term "]"
syntax (name := solve) "#solve" solveUnfoldDepth solveTimeout solveVerbose solveTerm : command

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

def parseTerm : TSyntax `solveTerm -> CommandElabM Syntax
  |`(solveTerm| [ $th ]) => pure th.raw
  | _ => throwUnsupportedSyntax

@[command_elab solve]
def solveImp : CommandElab := fun stx => do
  let sOpts ← parseVerbose (← parseTimeout (← parseUnfoldDepth default ⟨stx[1]⟩) ⟨stx[2]⟩) ⟨stx[3]⟩
  let t ← parseTerm ⟨stx[4]⟩
  withoutModifyingEnv $ runTermElabM fun _ => do
    let se ← translate sOpts t
    -- TEMPORARY STUBBING
    logReprExpr sOpts "Normalized expr" se
    match (toResult se) with
    | r@Result.Valid => logInfo f!"{reprStr r}"
    | r@Result.Falsified => logError f!"{reprStr r}"
    | r@Result.Undetermined => logWarning f!"{reprStr r}"

end Solver

