import Lean
import Solver.Command.Options
import Solver.Smt.Translate
import Solver.Optimize
import Solver.Logging.Basic

open Lean Elab Tactic Meta
open Solver.Optimize Solver.Smt Solver.Options
namespace Solver.Tactic

declare_syntax_cat solveOptionT
syntax "(unfold-depth:" num ")" : solveOptionT
syntax "(max-depth:" num ")" : solveOptionT
syntax "(timeout:" num ")" : solveOptionT
syntax "(verbose:" num ")" : solveOptionT
syntax "(only-smt-lib:" num ")" : solveOptionT
syntax "(only-optimize:" num ")" : solveOptionT
syntax "(dump-smt-lib:" num ")" : solveOptionT
syntax "(gen-cex:" num ")" : solveOptionT
syntax "(random-seed:" num ")" : solveOptionT
syntax "(solve-result:" num ")" : solveOptionT


/--
`blast` is an SMT-based tactic that automatically proves goals using Z3.

Options:
      - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
      - `verbose:` activating debug info (default: 0)
      - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
      - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
      - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
      - `gen-cex`: generate counterexample for falsified theorems (default: 1)
      - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
      - `random-seed`: seed for the random number generator (default: none)
      - `solve-result`: specify the expected result from the #solve command, i.e.,
                        0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)
Example: `blast (timeout: 10) (verbose: 1)`
-/
syntax (name := blastTactic) "blast_smt" (solveOptionT)* : tactic

/-! ### Helper Functions -/
def formatSmtQuery (cmds : Array SmtCommand) : String :=
  String.intercalate "\n" (cmds.map toString).toList

/-! ### Individual Parsing Functions -/
def parseUnfoldDepth (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
  | _ => return sOpts

def parseTimeout (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (timeout: $n:num)) => return { sOpts with timeout := some n.getNat }
  | _ => return sOpts

def parseVerbose (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (verbose: $n:num)) => return { sOpts with verbose := n.getNat }
  | _ => return sOpts

def parseSmtLib (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (only-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlySmtLib := false }
      | 1 => return { sOpts with onlySmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseOptimize (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (only-optimize: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlyOptimize := false }
      | 1 => return { sOpts with onlyOptimize := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseDumpSmt (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (dump-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with dumpSmtLib := false }
      | 1 => return { sOpts with dumpSmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseGenCex (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (gen-cex: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with generateCex := false }
      | 1 => return { sOpts with generateCex := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseRandomSeed (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (random-seed: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with randomSeed := none }
      | n => return { sOpts with randomSeed := some n }
  | _ => return sOpts

def parseSolveResult (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (solve-result: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with solveResult := .ExpectedValid }
      | 1 => return { sOpts with solveResult := .ExpectedFalsified }
      | 2 => return { sOpts with solveResult := .ExpectedUndetermined }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

/-! ### Generic Parser for All Options -/
def parseSolveOption (sOpts : SolverOptions) (opt : TSyntax `solveOptionT) : TacticM SolverOptions := do
  let sOpts ← parseUnfoldDepth sOpts opt
  let sOpts ← parseTimeout sOpts opt
  let sOpts ← parseVerbose sOpts opt
  let sOpts ← parseSmtLib sOpts opt
  let sOpts ← parseOptimize sOpts opt
  let sOpts ← parseDumpSmt sOpts opt
  let sOpts ← parseGenCex sOpts opt
  let sOpts ← parseSolveResult sOpts opt
  let sOpts ← parseRandomSeed sOpts opt
  return sOpts

/-! ### Process Multiple Options -/
def parseSolveOptions (opts : Array Syntax) (sOpts : SolverOptions) : TacticM SolverOptions :=
  opts.foldlM (init := sOpts) fun acc opt => do
    let opt' : TSyntax `solveOptionT := ⟨opt⟩
    parseSolveOption acc opt'

/-! ### Main Translation Function with Result Handling -/
def translateMainWithResult (e : Expr) : TranslateEnvT (Result × Expr)  := do
    let optExpr ← Optimize.main (← toPropExpr e)
    match (toResult optExpr) with
    | res@(.Undetermined) =>
        if (← get).optEnv.options.solverOptions.onlyOptimize
        then return (res, optExpr)
        else
          setSolverProcess
          let st ← translateExpr optExpr
          assertTerm (notSmt st)
          let res ← checkSat
          discard $ exitSmt
          return (res, optExpr)
    | res => return (res, optExpr)
  where
    isTheoremExpr (e : Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const n _ := e.getAppFn' | return none
      let ConstantInfo.thmInfo info ← getConstInfo n | return none
      return info.type

    toPropExpr (e : Expr) : TranslateEnvT Expr := do
      if let some r ← isTheoremExpr e then return r
      if !(← isTypeCorrect e) || (Expr.hasSorry e) then
         throwEnvError "translate: {← ppExpr e} is not well-formed"
      if (← isPropEnv e) then return e
         throwEnvError "translate: {← ppExpr e} is not a proposition!"

@[tactic blastTactic]
def blastTacticImp : Tactic := fun stx => withMainContext do
  -- Parse options in any order
  let opts := stx[1].getArgs
  let sOpts ← parseSolveOptions opts default

  -- Get the current goal
  let goal ← getMainGoal

  -- Build the full goal including hypotheses as implications
  let fullGoal ← goal.withContext do
    let goalType ← goal.getType
    -- Get all hypotheses from the local context
    let lctx ← getLCtx
    let mut hyps := #[]

    for decl in lctx do
      if decl.isImplementationDetail then continue
      let declType ← instantiateMVars decl.type
      if ← isProp declType then
        hyps := hyps.push decl.toExpr

    -- Build: h1 → h2 → ... → hn → goal
    mkForallFVars hyps goalType

  let env : TranslateEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let ((result, optExpr), finalEnv) ← translateMainWithResult fullGoal |>.run env

  if sOpts.dumpSmtLib then
    let smtLibQuery := finalEnv.smtEnv.smtCommands
    let smtLibStr := formatSmtQuery smtLibQuery
    logInfo m!"SMT-Lib Query:\n{smtLibStr}"

  discard $ (logResult result).run finalEnv

  match result with
  | .Valid =>
      -- TODO: replace with proper proof reconstruction
      -- Label sorry for goal splitting?
      let goalType ← goal.getType
      let sorryProof ← Lean.Meta.mkLabeledSorry goalType (synthetic := false) (unique := true)
      goal.assign sorryProof
      replaceMainGoal []
  | .Falsified cex =>
    throwTacticEx `blast goal "Goal was falsified (see counterexample above)"
  | .Undetermined =>
      -- Replace the goal with the optimized expression
      let goalType ← goal.getType
      let newGoal ← goal.replaceTargetEq optExpr (← mkEqRefl goalType)
      replaceMainGoal [newGoal]

end Solver.Tactic
