import Lean
import Solver.Command.Options
import Solver.Smt.Translate

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Syntax

/--
`#solve` is a Lean4 command that optimizes a lean theorem and calls the
backend Smt solver on the remaining unsolved goals.

Options:
  - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
  - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
  - `verbose:` activating debug info (default: 0)
  - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
  - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
  - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
  - `random-seed`: seed for the random number generator (default: none)
  - `gen-cex`: generate counterexample for falsified theorems (default: 1)
  - `solve-result`: specify the expected result from the #solve command, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)

Examples:
   - #solve [∀ x y : Nat, x + y ≥ x]
   - #solve (only-optimize: 1) (verbose: 1) [∀ x y : Nat, x + y ≥ x]
   - #solve [add_nat_ge_left]
-/

declare_syntax_cat solveOption
syntax "(unfold-depth:" num ")" : solveOption
syntax "(timeout:" num ")" : solveOption
syntax "(verbose:" num ")" : solveOption
syntax "(only-smt-lib:" num ")" : solveOption
syntax "(only-optimize:" num ")" : solveOption
syntax "(dump-smt-lib:" num ")" : solveOption
syntax "(gen-cex:" num ")" : solveOption
syntax "(solve-result:" num ")" : solveOption
syntax "(max-depth:" num ")" : solveOption
syntax "(random-seed:" num ")" : solveOption

-- NOTE: Limited to one term for the time being
syntax solveTerm := "[" term "]"
syntax (name := solve) "#solve" (solveOption)* solveTerm : command

variable [MonadExceptOf Exception m] [Monad m]

/-! ### Individual Parsing Functions -/
def parseUnfoldDepth (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
  | _ => return sOpts

def parseMaxDepth (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
 | `(solveOption| (max-depth: $n:num)) => return { sOpts with maxDepth := n.getNat }
 | _ => return sOpts


def parseTimeout (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (timeout: $n:num)) => return { sOpts with timeout := some n.getNat }
  | _ => return sOpts

def parseVerbose (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (verbose: $n:num)) => return { sOpts with verbose := n.getNat }
  | _ => return sOpts

def parseSmtLib (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (only-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlySmtLib := false }
      | 1 => return { sOpts with onlySmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseOptimize (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (only-optimize: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlyOptimize := false }
      | 1 => return { sOpts with onlyOptimize := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseDumpSmt (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (dump-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with dumpSmtLib := false }
      | 1 => return { sOpts with dumpSmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseGenCex (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (gen-cex: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with generateCex := false }
      | 1 => return { sOpts with generateCex := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseRandomSeed (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (random-seed: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with randomSeed := none }
      | n => return { sOpts with randomSeed := some n }
  | _ => return sOpts

def parseSolveResult (sOpts : SolverOptions) : TSyntax `solveOption → m SolverOptions
  | `(solveOption| (solve-result: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with solveResult := .ExpectedValid }
      | 1 => return { sOpts with solveResult := .ExpectedFalsified }
      | 2 => return { sOpts with solveResult := .ExpectedUndetermined }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

/-! ### Generic Parser for All Options -/
def parseSolveOption (sOpts : SolverOptions) (opt : TSyntax `solveOption) : m SolverOptions := do
  let sOpts ← parseUnfoldDepth sOpts opt
  let sOpts ← parseTimeout sOpts opt
  let sOpts ← parseVerbose sOpts opt
  let sOpts ← parseSmtLib sOpts opt
  let sOpts ← parseOptimize sOpts opt
  let sOpts ← parseDumpSmt sOpts opt
  let sOpts ← parseGenCex sOpts opt
  let sOpts ← parseSolveResult sOpts opt
  let sOpts ← parseMaxDepth sOpts opt
  let sOpts ← parseRandomSeed sOpts opt
  return sOpts

/-! ### Process Multiple Options -/
def parseSolveOptions (opts : Array Syntax) (sOpts : SolverOptions) : m SolverOptions :=
  opts.foldlM (init := sOpts) fun acc opt => do
    let opt' : TSyntax `solveOption := ⟨opt⟩
    parseSolveOption acc opt'

def parseTerm : TSyntax `Solver.solveTerm -> m Syntax
  |`(solveTerm| [ $th ]) => pure th.raw
  | _ => throwUnsupportedSyntax

def commandInvoker (f : SolverOptions → Syntax → TermElabM Unit) : CommandElab := fun stx => do
  let opts := stx[1].getArgs
  let sOpts ← parseSolveOptions opts default  -- Process all options dynamically
  let tr ← parseTerm ⟨stx[2]⟩
  withoutModifyingEnv $ runTermElabM fun _ => f sOpts tr

/-! ### Implementation of solve command -/
@[command_elab solve]
def solveImp : CommandElab := commandInvoker Solver.Smt.command

end Solver.Syntax
