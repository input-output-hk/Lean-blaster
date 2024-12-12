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
    logReprExpr "Translate:" e
    if let some n := isIntValue? e then return intLitSmt n
    if let some n := isNatValue? e then return natLitSmt n
    if let some s := isStrValue? e then return strLitSmt s
    -- TODO: consider other sort once supported (e.g., BitVec, Char, etc)
    match e with
     | Expr.fvar .. => translateFreeVar e optimizeExpr visit
     | Expr.const .. => throwEnvError f!"unexpected const expression {e}"
     | Expr.forallE .. =>
         let qtyEnv := initialQuantifierEnv topLevel
         let (t, _) ← translateForAll e optimizeExpr visit |>.run qtyEnv
         return t
     | Expr.app .. => translateApp e optimizeExpr visit
     | Expr.lam .. => translateLambda e optimizeExpr visit
     | Expr.mdata _d me =>
        match toTaggedCtorSelector? e with
        | none => visit me
        | some (Expr.app (Expr.const s _) (Expr.const a _)) =>
            return mkSimpleSmtAppN (nameToSmtSymbol s) #[smtSimpleVarId (nameToSmtSymbol a)]
        | some s => throwEnvError f!"unexpected ctor selector expression {reprStr s}"
     | Expr.proj n idx p => translateProj n idx p visit
     | Expr.lit .. => throwEnvError f!"unexpected literal expression {e}"
     | Expr.mvar .. => throwEnvError f!"unexpected meta variable {e}"
     | Expr.bvar .. => throwEnvError f!"unexpected bounded variable {e}"
     | Expr.letE .. => throwEnvError f!"unexpected let expression"
     | Expr.sort _ => throwEnvError f!"unexpected sort type {reprStr e}" -- sort type are handled elsewhere
  let st ← visit e (topLevel := true)
  -- assert negation for check sat
  assertTerm (notSmt st)
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  logResult (← checkSat)
  -- TODO: spawn lean proof mode when result is undetermined
  discard $ exitSmt


def translate (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  elabTermAndSynthesize stx none >>= fun e => do
    let (optExpr, env) ← optimize sOpts (← toPropExpr e)
    match (toResult optExpr) with
    | .Undetermined =>
        discard $ translateExpr optExpr|>.run (← setSolverProcess sOpts env)
    | res => logResult res
  where
    toPropExpr (e : Expr) : TermElabM Expr := do
    let e_type ← inferType e
    let forall_type ← inferType e_type
    if Expr.isProp e_type then return e
    if Expr.isProp forall_type then return e_type -- case when parsed term is a theorem name
    throwError f!"translate: Term of type Prop expected !!!"

namespace Solver.Smt
