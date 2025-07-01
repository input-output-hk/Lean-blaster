import Lean
import Solver.Command.Options
import Solver.Optimize.Basic
import Solver.Smt.Env
import Solver.Smt.Term
import Solver.Smt.Translate.Application

open Lean Elab Command Term Meta Solver.Optimize Solver.Options

namespace Solver.Smt

/-- Translate an optimized Lean4 `Expr` to an SMT term, and invoke the solver. --/
partial def translateExpr (e : Expr) : TranslateEnvT SmtTerm := do
  let rec visit (e : Expr) (topLevel := false) : TranslateEnvT SmtTerm := do
    withTranslateEnvCache e fun _ => do
    trace[Translate.expr] "translating {reprStr e}"
    logReprExpr "Translate:" e
    if let some n := isIntValue? e then return intLitSmt n
    if let some n := isNatValue? e then return natLitSmt n
    if let some s := isStrValue? e then return strLitSmt s
    -- TODO: consider other sort once supported (e.g., BitVec, Char, etc)
    match e with
     | Expr.fvar .. => translateFreeVar e optimizeExpr visit
     | Expr.const .. => translateConst e optimizeExpr visit
     | Expr.forallE .. =>
         let qtyEnv := initialQuantifierEnv topLevel
         let (t, _) ← translateForAll e optimizeExpr visit |>.run qtyEnv
         trace[Translate.forAll] "translate forall {reprStr e} ==> {t}"
         return t
     | Expr.app .. => translateApp e optimizeExpr visit
     | Expr.lam .. => translateLambda e optimizeExpr visit
     | Expr.mdata _d me =>
        match toTaggedCtorSelector? e with
        | none => visit me
        | some (Expr.app (Expr.const s _) _) =>
            return mkSimpleSmtAppN (nameToSmtSymbol s) #[smtSimpleVarId (mkReservedSymbol "@x")]
        | some s => throwEnvError f!"translateExpr: unexpected ctor selector expression {reprStr s}"
     | Expr.proj n idx p => translateProj n idx p visit
     | Expr.lit .. => throwEnvError f!"translateExpr: unexpected literal expression {reprStr e}"
     | Expr.mvar .. => throwEnvError f!"translateExpr: unexpected meta variable {reprStr e}"
     | Expr.bvar .. => throwEnvError f!"translateExpr: unexpected bounded variable {reprStr e}"
     | Expr.letE .. => throwEnvError f!"translateExpr: unexpected let expression {reprStr e}"
     | Expr.sort _ => throwEnvError f!"translateExpr: unexpected sort type {reprStr e}" -- sort type are handled elsewhere
  visit e (topLevel := true)

def Translate.main (e : Expr) : TranslateEnvT Unit := do
    let optExpr ← profileTask "Optimization" $ Optimize.main (← toPropExpr e)
    trace[Translate.optExpr] "optimized expression: {← ppExpr optExpr}"
    match (toResult optExpr) with
    | res@(.Undetermined) =>
        if (← get).optEnv.options.solverOptions.onlyOptimize
        then logResult res
        else
          -- set backend solver
          setSolverProcess
          let st ← profileTask "Translation" $ translateExpr optExpr
          -- assert negation for check sat
          profileTask "Submitting Smt Query" $ assertTerm (notSmt st)
          -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
          logSmtQuery
          let res ← profileTask "Solve" checkSat
          logResult res
          discard $ exitSmt
          -- TODO: spawn lean proof mode when result is undetermined

    | res => logResult res

  where
    isTheoremExpr (e : Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const n _ := e.getAppFn' | return none
      let ConstantInfo.thmInfo info ← getConstInfo n | return none
      return info.type

    toPropExpr (e : Expr) : TranslateEnvT Expr := do
      if let some r ← isTheoremExpr e then return r
      if !(← isTypeCorrect e) || (Expr.hasSorry e) then
         throwEnvError f!"translate: {← ppExpr e} is not well-formed"
      if (← isProp e) then return e
         throwEnvError f!"translate: {← ppExpr e} is not a proposition !!!"

def command (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  elabTermAndSynthesize stx none >>= fun e => do
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    discard $ Translate.main e|>.run env

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

namespace Solver.Smt
