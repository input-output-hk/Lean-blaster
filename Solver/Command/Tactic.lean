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

syntax (name := blastTactic) "blast_smt" (solveOptionT)* : tactic

/-! ### Helper Functions -/
def formatSmtQuery (cmds : Array SmtCommand) : String :=
  String.intercalate "\n" (cmds.map toString).toList

/-! ### Individual Parsing Functions -/
def parseUnfoldDepth (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
  | _ => return sOpts

def parseMaxDepth (sOpts : SolverOptions) : TSyntax `solveOptionT → TacticM SolverOptions
  | `(solveOptionT| (max-depth: $n:num)) => return { sOpts with maxDepth := n.getNat }
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
  let sOpts ← parseMaxDepth sOpts opt
  let sOpts ← parseRandomSeed sOpts opt
  return sOpts

/-! ### Process Multiple Options -/
def parseSolveOptions (opts : Array Syntax) (sOpts : SolverOptions) : TacticM SolverOptions :=
  opts.foldlM (init := sOpts) fun acc opt => do
    let opt' : TSyntax `solveOptionT := ⟨opt⟩  -- Explicit cast
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
  let goalType ← goal.getType

  let env : TranslateEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let ((result, optExpr), finalEnv) ← translateMainWithResult goalType |>.run env

  if sOpts.dumpSmtLib then
    let smtLibQuery := finalEnv.smtEnv.smtCommands
    let smtLibStr := formatSmtQuery smtLibQuery
    logInfo m!"SMT-Lib Query:\n{smtLibStr}"

  discard $ (logResult result).run finalEnv

  match result with
  | .Valid =>
      -- TODO: replace with proper proof reconstruction
      -- Label sorry for goal splitting?
      let sorryProof ← Lean.Meta.mkLabeledSorry goalType (synthetic := false) (unique := true)
      goal.assign sorryProof
      replaceMainGoal []
  | .Falsified cex =>
    throwTacticEx `blast goal "Goal was falsified (see counterexample above)"
  | .Undetermined =>
      -- Replace the goal with the optimized expression
      let newGoal ← goal.replaceTargetEq optExpr (← mkEqRefl goalType)
      replaceMainGoal [newGoal]


end Solver.Tactic
