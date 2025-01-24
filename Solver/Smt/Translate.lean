import Lean
import Solver.Command.Options
import Solver.Optimize.Basic
import Solver.Smt.Env
import Solver.Smt.Term
import Solver.Smt.Translate.Application

open Lean Elab Command Term Meta Solver.Optimize Solver.Options

namespace Solver.Smt

partial def translateExpr (e : Expr) : TranslateEnvT Unit := do
  let rec visit (e : Expr) (topLevel := false) : TranslateEnvT SmtTerm := do
    withTranslateEnvCache e fun _ => do
    trace[Translate.expr] f!"translating {reprStr e}"
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
         trace[Translate.forAll] f!"translate forall {reprStr e} ==> {t}"
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
  let st ← visit e (topLevel := true)
  -- assert negation for check sat
  assertTerm (notSmt st)
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  logResult (← checkSat) (← get).optEnv.options.solverOptions
  -- TODO: spawn lean proof mode when result is undetermined
  discard $ exitSmt


def translate (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  elabTermAndSynthesize stx none >>= fun e => do
    let (optExpr, env) ← optimize sOpts (← toPropExpr e)
    match (toResult optExpr) with
    | .Undetermined =>
        trace[Translate.optExpr] f!"optimized expression: {reprStr optExpr}"
        discard $ translateExpr optExpr|>.run (← setSolverProcess sOpts env)
    | res =>
       if sOpts.falsifiedResult && !isFalsifiedResult res
       then throwError (falsifiedError res)
       else logResult res sOpts
  where
    toPropExpr (e : Expr) : TermElabM Expr := do
    let e_type ← inferType e
    let forall_type ← inferType e_type
    if Expr.isProp e_type then return e
    if Expr.isProp forall_type then return e_type -- case when parsed term is a theorem name
    throwError f!"translate: Term of type Prop expected !!!"

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

namespace Solver.Smt
