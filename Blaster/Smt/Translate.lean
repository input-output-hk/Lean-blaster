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
    if let some s := isStrValue? e then
      match strLitSmt s with
      | .ok t => return t
      | .error c =>
          throwEnvError "translateExpr: string literal holds the character with code point \
                         {c.toNat}, above the Smt string alphabet bound {maxSmtCodePoint}"
    -- TODO: consider other sort once supported (e.g., BitVec, Char, etc)
    match e with
     | Expr.fvar .. => translateFreeVar e visit
     | Expr.const .. => translateConst e visit
     | Expr.forallE .. =>
         let qtyEnv := initialQuantifierEnv topLevel
         let t ← translateForAll e visit |>.run' qtyEnv
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

register_option blaster.useSmtlib : Bool := {
  defValue := false
  descr := "use the external SMT-LIB solver for this Blaster invocation"
}

register_option blaster.smtlibFallbackAfter : Nat := {
  defValue := 0
  descr := "cap the native solver check in seconds, then retry undetermined queries through SMT-LIB"
}

def Translate.main (e : Expr) (logUndetermined := true) : TranslateEnvT (Result × Expr) := do
  if blaster.useSmtlib.get (← getOptions) then
    modify fun env => { env with optEnv.options.solverOptions.backend := .smtlib }
  -- set start local context
  updateLocalContext (← mkLocalContext)
  let source ← toPropExpr e
  let e ← addAxioms source (← findLocalAxioms)
  let optExpr ← profileTask "Optimization" $ Optimize.mainAux e (applyHashCons := false)
  trace[Translate.optExpr] "optimized expression: {← ppExpr optExpr}"
  match (toResult optExpr) with
  | res@(.Undetermined) =>
      if (← get).optEnv.options.solverOptions.onlyOptimize then
        if logUndetermined then logResult res
        return (res, optExpr)
      else
        let initial ← get
        let options := initial.optEnv.options.solverOptions
        let nativeSeconds := blaster.smtlibFallbackAfter.get (← getOptions)
        let fallback := nativeSeconds > 0 && options.backend == .ffi && !options.onlySmtLib
        if fallback then
          let limit := min nativeSeconds (options.timeout.getD nativeSeconds)
          modify fun env => { env with optEnv.options.solverOptions.timeout := some limit }
        let res ← solve source optExpr (logUndetermined && !fallback)
        if fallback && isUndeterminedResult res then
          logInfoAt (← getRef) "Native Z3 returned undetermined; retrying via SMT-LIB"
          set { initial with optEnv.options.solverOptions.backend := .smtlib }
          return ((← solve source optExpr logUndetermined), optExpr)
        return (res, optExpr)
  | res =>
     logResult res
     return (res, optExpr)

  where
    solve (source optExpr : Expr) (logUndetermined : Bool) : TranslateEnvT Result := do
      setBlasterProcess
      let st ← profileTask "Translation" $ translateExpr optExpr
      profileTask "Submitting Smt Query" $ assertTerm (notSmt st)
      logSmtQuery
      let res ← profileTask "Solve" checkSat
      if !isUndeterminedResult res || logUndetermined then logResult res
      if (← get).optEnv.options.solverOptions.replay && isFalsifiedResult res then
        logInfoAt (← getRef) (← replayNativeCounterexample source)
      discard $ exitSmt
      return res

    isTheoremExpr (e : Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const n _ := e.getAppFn' | return none
      let ConstantInfo.thmInfo info ← getConstEnvInfo n | return none
      hashcons info.type

    toPropExpr (e : Expr) : TranslateEnvT Expr := do
      if let some r ← isTheoremExpr e then return r
      if !(← isTypeCorrect e) || (Expr.hasSorry e) then
         throwEnvError "translate: {← ppExpr e} is not well-formed"
      let e' ← hashcons e
      if (← isPropEnv e') then return e'
         throwEnvError "translate: {← ppExpr e} is not a proposition !!!"

    addAxioms (e : Expr) (axioms : List Expr) : TranslateEnvT Expr := do
      match axioms with
      | [] => return e
      | a :: tl =>
         addAxioms (← mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default (← hashcons a) e) tl

def command (sOpts: BlasterOptions) (stx : Syntax) : TermElabM Unit := do
   withRef stx do
     instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none) >>= fun e => do
       let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
       discard $ Translate.main e|>.run env

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

end Blaster.Smt
