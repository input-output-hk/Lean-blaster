import Lean
import Blaster.Command.Options
import Blaster.Smt.Translate
open Lean Elab Command Term Meta Blaster.Options

namespace Blaster.Syntax

/--
`#blaster` is a Lean4 command that optimizes a lean theorem and calls the
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
  - `solve-result`: specify the expected result from the #blaster command, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)

Examples:
   - #blaster [∀ x y : Nat, x + y ≥ x]
   - #blaster (only-optimize: 1) (verbose: 1) [∀ x y : Nat, x + y ≥ x]
   - #blaster [add_nat_ge_left]
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
syntax (name := solve) "#blaster" (solveOption)* solveTerm : command

variable [MonadExceptOf Exception m] [Monad m]

/-! ### Individual Parsing Functions -/
def parseUnfoldDepth (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
  | _ => return sOpts

def parseMaxDepth (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
 | `(solveOption| (max-depth: $n:num)) => return { sOpts with maxDepth := n.getNat }
 | _ => return sOpts


def parseTimeout (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (timeout: $n:num)) => return { sOpts with timeout := some n.getNat }
  | _ => return sOpts

def parseVerbose (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (verbose: $n:num)) => return { sOpts with verbose := n.getNat }
  | _ => return sOpts

def parseSmtLib (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (only-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlySmtLib := false }
      | 1 => return { sOpts with onlySmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseOptimize (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (only-optimize: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlyOptimize := false }
      | 1 => return { sOpts with onlyOptimize := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseDumpSmt (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (dump-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with dumpSmtLib := false }
      | 1 => return { sOpts with dumpSmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseGenCex (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (gen-cex: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with generateCex := false }
      | 1 => return { sOpts with generateCex := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseRandomSeed (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (random-seed: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with randomSeed := none }
      | n => return { sOpts with randomSeed := some n }
  | _ => return sOpts

def parseSolveResult (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (solve-result: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with solveResult := .ExpectedValid }
      | 1 => return { sOpts with solveResult := .ExpectedFalsified }
      | 2 => return { sOpts with solveResult := .ExpectedUndetermined }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

/-! ### Generic Parser for All Options -/
def parseSolveOption (sOpts : BlasterOptions) (opt : TSyntax `solveOption) : m BlasterOptions := do
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
def parseSolveOptions (opts : Array Syntax) (sOpts : BlasterOptions) : m BlasterOptions :=
  opts.foldlM (init := sOpts) fun acc opt => do
    let opt' : TSyntax `solveOption := ⟨opt⟩
    parseSolveOption acc opt'

def parseTerm : TSyntax `Blaster.solveTerm -> m Syntax
  |`(solveTerm| [ $th ]) => pure th.raw
  | _ => throwUnsupportedSyntax


def commandInvoker (f : BlasterOptions → Syntax → TermElabM Unit) : CommandElab := fun stx => do
  let some cancelTk := (← read).cancelTk? | unreachable!
  let opts := stx[1].getArgs
  let sOpts ← parseSolveOptions opts default  -- Process all options dynamically
  let tr ← parseTerm ⟨stx[2]⟩
  let act ← wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ =>
    withoutModifyingEnv $ runTermElabM fun _ =>
    -- NOTE: We need to set maxRecDepth to 0 as the term elaborator function is triggering
    -- "maximum recursion depth has been reached".
    -- This only happens when the #solve command is invoked on some complex term.
    -- NOTE: maxHeartbeats is set to 0 to avoid all Lean4 codebase functions that depends on whnf
    -- to trigger the maxHeartbeats reached error. Indeed, Lean4 badly handles the number of heat beats.
    -- Heart beats are only incremented but never decremented. It should be decremented when
    -- memory allocation is freed.
    -- The direct use of whnf will soon be removed at the preprocessing phase.
    -- However, since we rely on functions like isProp, inferType and withLocalDecl, setting maxHearbeats
    -- to zero will still be required. Unless, we have a new implementation for these functions.
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0, maxRecDepth := 0 }) $ do
        f sOpts tr
  let task ← BaseIO.asTask (prio := Task.Priority.dedicated) (act ())
  logSnapshotTask { stx? := some stx, task, cancelTk? := cancelTk }


/-! ### Implementation of solve command -/
@[command_elab solve]
def solveImp : CommandElab := commandInvoker Blaster.Smt.command

end Blaster.Syntax
