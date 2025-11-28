import Lean
import Solver.Command.Options
import Solver.Optimize.Basic
import Solver.Smt.Env
import Solver.Smt.Term
import Solver.Smt.Translate.Application

open Lean Elab Command Term Meta Solver.Optimize Solver.Options

namespace Solver.Smt

/-- Translate an optimized Lean4 `Expr` to an SMT term, and invoke the solver. --/
partial def translateExpr (e : Expr) (topLevel := true) : TranslateEnvT SmtTerm := do
  let rec visit (e : Expr) (topLevel := false) : TranslateEnvT SmtTerm := do
    withTranslateEnvCache e fun _ => do
    trace[Translate.expr] "translating {reprStr e}"
    logReprExpr "Translate:" e
    if let some n := isIntValue? e then return intLitSmt n
    if let some n := isNatValue? e then return natLitSmt n
    if let some s := isStrValue? e then return strLitSmt s
    -- TODO: consider other sort once supported (e.g., BitVec, Char, etc)
    match e with
     | Expr.fvar .. => translateFreeVar e visit
     | Expr.const .. => translateConst e visit
     | Expr.forallE .. =>
         let qtyEnv := initialQuantifierEnv topLevel
         let (t, _) ← translateForAll e visit |>.run qtyEnv
         trace[Translate.forAll] "translate forall {reprStr e} ==> {t}"
         return t
     | Expr.app .. => translateApp e visit
     | Expr.lam .. => translateLambda e visit
     | Expr.mdata _d me =>
        match toTaggedCtorSelector? e with
        | none => visit me
        | some (Expr.app (Expr.const s _) _) =>
            return mkSimpleSmtAppN (nameToSmtSymbol s) #[smtSimpleVarId (mkReservedSymbol "@x")]
        | some s => throwEnvError "translateExpr: unexpected ctor selector expression {reprStr s}"
     | Expr.proj n idx p => translateProj n idx p visit
     | Expr.lit .. => throwEnvError "translateExpr: unexpected literal expression {reprStr e}"
     | Expr.mvar .. => throwEnvError "translateExpr: unexpected meta variable {reprStr e}"
     | Expr.bvar .. => throwEnvError "translateExpr: unexpected bound variable {reprStr e}"
     | Expr.letE .. => throwEnvError "translateExpr: unexpected let expression {reprStr e}"
     | Expr.sort _ => throwEnvError "translateExpr: unexpected sort type {reprStr e}" -- sort type are handled elsewhere
  visit e topLevel

def Translate.main (e : Expr) (logUndetermined := true) : TranslateEnvT (Result × Expr) := do
    let e' ← addAxioms (← toPropExpr e) (← findLocalAxioms)
    let optExpr ← profileTask "Optimization" $ Optimize.main e'
    trace[Translate.optExpr] "optimized expression: {← ppExpr optExpr}"
    match (toResult optExpr) with
    | res@(.Undetermined) =>
        if (← get).optEnv.options.solverOptions.onlyOptimize then
          if logUndetermined then logResult res
          return (res, optExpr)
        else
          -- set backend solver and ensure it's killed on error/interruption
          try
            setSolverProcess
            let st ← profileTask "Translation" $ translateExpr optExpr
            -- assert negation for check sat
            profileTask "Submitting Smt Query" $ assertTerm (notSmt st)
            -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
            logSmtQuery
            let res ← profileTask "Solve" checkSat
            if !isUndeterminedResult res || logUndetermined then logResult res
            discard $ exitSmt
            return (res, optExpr)
          catch e =>
            -- Kill the solver process on any error or interruption
            killSolverProcess
            throw e
    | res =>
       logResult res
       return (res, optExpr)

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
         throwEnvError "translate: {← ppExpr e} is not a proposition !!!"

    addAxioms (e : Expr) (axioms : List Expr) : TranslateEnvT Expr := do
      match axioms with
      | [] => return e
      | a :: tl =>
         addAxioms (mkForall (← Term.mkFreshBinderName) BinderInfo.default a e) tl

def command (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0, maxRecDepth := 0 }) $ do
   withRef stx do
     instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none) >>= fun e => do
       let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
       try
         discard $ Translate.main e|>.run env
       catch e =>
         -- Ensure cleanup happens even if the command is interrupted
         discard $ killSolverProcess.run env
         throw e

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

end Solver.Smt
