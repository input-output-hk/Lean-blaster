import Lean
import Solver.Command.Options
import Solver.Smt.Translate
import Solver.Optimize

open Lean Elab Tactic Meta Solver.Options
open Solver.Optimize
open Solver.Smt
namespace Solver.Tactic

declare_syntax_cat solveOptionT
syntax solveUnfoldDepth := ("(unfold-depth:" num ")")?
syntax solveMaxDepth := ("(max-depth:" num ")")?
syntax solveTimeout := ("(timeout:" num ")")?
syntax solveVerbose := ("(verbose:" num ")")?
syntax solveSMTLib := ("(only-smt-lib:" num ")")?
syntax solveOptimize := ("(only-optimize:" num ")")?
syntax solveDumpSmt := ("(dump-smt-lib:" num ")")?
syntax solveGenCex := ("(gen-cex:" num ")")?
syntax solveRandomSeed := ("(random-seed:" num ")")?
syntax solveResult := ("(solve-result:" num ")")?

syntax (name := lean_blasterTactic) "lean_blaster"
  solveUnfoldDepth solveMaxDepth solveTimeout solveRandomSeed
  solveVerbose solveSMTLib solveOptimize solveDumpSmt solveGenCex
  solveResult : tactic


/-! ### Individual Parsing Functions -/
def parseUnfoldDepth (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
 | `(solveUnfoldDepth| (unfold-depth: $n:num)) => return { sOpts with unfoldDepth := n.getNat }
 | `(solveUnfoldDepth| ) => return sOpts
 | _ => throwUnsupportedSyntax

def parseMaxDepth (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveMaxDepth| (max-depth: $n:num)) => return { sOpts with maxDepth := n.getNat }
  | _ => return sOpts


def parseTimeout (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveTimeout| (timeout: $n:num)) => return { sOpts with timeout := some n.getNat }
  | _ => return sOpts

def parseVerbose (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveVerbose| (verbose: $n:num)) => return { sOpts with verbose := n.getNat }
  | _ => return sOpts

def parseSmtLib (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveSMTLib| (only-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlySmtLib := false }
      | 1 => return { sOpts with onlySmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseOptimize (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveOptimize| (only-optimize: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with onlyOptimize := false }
      | 1 => return { sOpts with onlyOptimize := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseDumpSmt (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveDumpSmt| (dump-smt-lib: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with dumpSmtLib := false }
      | 1 => return { sOpts with dumpSmtLib := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseGenCex (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveGenCex| (gen-cex: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with generateCex := false }
      | 1 => return { sOpts with generateCex := true }
      | _ => throwUnsupportedSyntax
  | _ => return sOpts

def parseRandomSeed (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveRandomSeed| (random-seed: $n:num)) =>
      match n.getNat with
      | 0 => return { sOpts with randomSeed := none }
      | n => return { sOpts with randomSeed := some n }
  | _ => return sOpts

def parseSolveResult (sOpts : SolverOptions) : TSyntax `solveOptionT -> TacticM SolverOptions
  | `(solveResult| (solve-result: $n:num)) =>
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

/-! ### Main Translation Function with Result Handling -/
def translateMainWithResult (e : Expr) : TranslateEnvT Result := do
    let optExpr ← Optimize.main (← toPropExpr e)
    match (toResult optExpr) with
    | res@(.Undetermined) =>
        if (← get).optEnv.options.solverOptions.onlyOptimize
        then return res
        else
          setSolverProcess
          let st ← translateExpr optExpr
          assertTerm (notSmt st)
          let res ← checkSat
          discard $ exitSmt
          return res
    | res => return res
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

@[tactic lean_blasterTactic]
def lean_blasterTacticImp : Tactic := fun stx => withMainContext do
  -- Parse options
  let sOpts ← parseVerbose (← parseTimeout (← parseUnfoldDepth default ⟨stx[1]⟩) ⟨stx[2]⟩) ⟨stx[3]⟩
  let sOpts ← parseDumpSmt (← parseOptimize (← parseSmtLib sOpts ⟨stx[4]⟩) ⟨stx[5]⟩) ⟨stx[6]⟩
  let sOpts ← parseSolveResult (← parseGenCex sOpts ⟨stx[7]⟩) ⟨stx[8]⟩

  -- Get the current goal
  let goal ← getMainGoal
  let goalType ← goal.getType

  let env : TranslateEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let (result, _) ← translateMainWithResult goalType |>.run env

  match result with
  | .Valid =>
      -- TODO: replace with proper proof reconstruction
      let sorryProof ← mkSorry goalType (synthetic := false)
      goal.assign sorryProof
      replaceMainGoal []
  | .Falsified cex =>
      let cexMsg := if cex.isEmpty then
        "SMT solver found counterexample (no details available)"
      else
        let cexLines := String.intercalate "\n" (cex.map (fun s => s!"  • {s}"))
        s!"SMT solver found counterexample:\n{cexLines}"
      throwTacticEx `lean_blaster goal cexMsg
  | .Undetermined =>
      throwTacticEx `lean_blaster goal "SMT solver could not determine validity"

end Solver.Tactic
