import Lean
import Blaster.Command.Options
import Blaster.Optimize.Basic
import Blaster.Smt.Env
import Blaster.Smt.Term
import Blaster.Smt.Translate.Application

open Lean Elab Command Term Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

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
          -- set backend solver
          setBlasterProcess
          let st ← profileTask "Translation" $ translateExpr optExpr
          -- assert negation for check sat
          profileTask "Submitting Smt Query" $ assertTerm (notSmt st)
          -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
          logSmtQuery
          let res ← profileTask "Solve" checkSat
          if !isUndeterminedResult res || logUndetermined then logResult res
          discard $ exitSmt
          return (res, optExpr)
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

/-- Replace the first occurrence of `pat` in `s` with `repl`. -/
private def replaceFirst (s pat repl : String) : Option String :=
  match s.splitOn pat with
  | [] | [_] => none
  | p0 :: rest => some (p0 ++ repl ++ String.intercalate pat rest)

/-- After a decisive `(solver: any)` race, offer a code-action suggestion
    replacing `any` with the winning solver, so the same result can be
    reproduced deterministically with the fastest backend. -/
def suggestPinnedSolver (invocationStx : Syntax) (winner : SmtSolver) : TermElabM Unit := do
  -- drop trailing trivia (whitespace/comments following the invocation)
  let some src := invocationStx.unsetTrailing.reprint | return ()
  let some newText := (
    match src.trim.splitOn "solver:" with
    | p0 :: rest@(_ :: _) =>
        let after := String.intercalate "solver:" rest
        (replaceFirst after "any" winner.identName).map (p0 ++ "solver:" ++ ·)
    | _ => none) | return ()
  Lean.Meta.Tactic.TryThis.addSuggestion invocationStx { suggestion := newText }

def command (sOpts: BlasterOptions) (cmdStx : Syntax) (stx : Syntax) : TermElabM Unit := do
   withRef stx do
     instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none) >>= fun e => do
       let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
       let t0 ← IO.monoMsNow
       let (_, fenv) ← Translate.main e|>.run env
       let totalMs := (← IO.monoMsNow) - t0
       -- performance report: total wall-clock of the whole call
       -- (optimization + translation + solving)
       if sOpts.verbose ≥ 1 then
         logInfoAt stx s!"⏱ blaster total: {totalMs}ms"
       -- pin-the-winner suggestion after a decisive `any` race
       if sOpts.solver == .any then
         if let some w := fenv.smtEnv.anyWinner then
           suggestPinnedSolver cmdStx w

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

end Blaster.Smt
