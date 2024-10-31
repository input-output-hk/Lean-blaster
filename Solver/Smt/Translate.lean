import Lean
import Solver.Command.Options
import Solver.Optimize.Basic
import Solver.Smt.Env

open Lean Elab Command Term Meta Solver.Optimize Solver.Options

namespace Solver.Smt

partial def translateExpr (sOpts : SolverOptions) (e : Expr) : TranslateEnvT Unit := do
  let rec visit (e : Expr) (topLevel := false) : TranslateEnvT SmtTerm := do
    withTranslateEnvCache e fun _ => do
    logReprExpr sOpts "Translate:" e
    if let some n := isIntValue? e then return intLitSmt n
    if let some n := isNatValue? e then return natLitSmt n
    if let some s := isStrValue? e then return strLitSmt s
    match e with
     | Expr.fvar fv => return (smtVarId s!"{← fv.getUserName}")
     | Expr.const n _l =>
        match (← getConstInfo n) with
        | .inductInfo _ => logInfo f!"inductive info for {n}"
        | .defnInfo _ => logInfo f!"def info for {n}"
        | .axiomInfo _ => logInfo f!"axiom info for {n}"
        | .recInfo _ => logInfo f!"rec info for {n}"
        | .thmInfo  _ => logInfo f!"thm info for {n}"
        | .opaqueInfo _ => logInfo f!"opaque info for {n}"
        | .quotInfo _ => logInfo f!"quotInfo info for {n}"
        | .ctorInfo _ => logInfo f!"ctorInfo info for {n}"
        return smtVarId s!"{n}"
     | Expr.forallE .. =>
         forallTelescope e fun xs b => do
           logInfo f!"quantifiers: {reprStr xs}"
           -- let mut qty := #[]
           for i in [:xs.size] do
             let t ← inferType xs[i]!
             logInfo f!"inferType: {reprStr t} {← isProp t}"
           logInfo f!"forall body: {reprStr b}"
           return smtVarId ""
     | Expr.app .. =>
         Expr.withApp e fun rf ras => do
          let fInfo ← getFunInfoNArgs rf ras.size
          let mut mas := #[]
          for i in [:ras.size] do
            if i < fInfo.paramInfo.size then
              let aInfo := fInfo.paramInfo[i]!
              if aInfo.isExplicit then
                mas := mas.push (← visit ras[i]!)
            else
              mas := mas.push (← visit ras[i]!)
          logInfo f!"APPEXPR: {reprStr rf}"
          let n := rf.getAppFn.constName!
          match (← getConstInfo n) with
          | .inductInfo _ => logInfo f!"inductive info for {n}"
          | .defnInfo _ => logInfo f!"def info for {n}"
          | .axiomInfo _ => logInfo f!"axiom info for {n}"
          | .recInfo _ => logInfo f!"rec info for {n}"
          | .thmInfo  _ => logInfo f!"thm info for {n}"
          | .opaqueInfo _ => logInfo f!"opaque info for {n}"
          | .quotInfo _ => logInfo f!"quotInfo info for {n}"
          | .ctorInfo _ => logInfo f!"ctorInfo info for {n}"
          -- check for partially applied function and create lambda expression
          -- handle match expression and generate ite
          -- handle opaque functions
          -- handle recursive function and use instance name remove implicit args
          return mkSmtAppN s!"rf.constName!" mas
     | Expr.lam .. => throwError f!"unexpected lambda expression"
     | Expr.letE .. => throwError f!"unexpected let expression"
     | Expr.mdata _d me => visit me
     | Expr.sort _ => return smtVarId "sort"
         -- this case must be handled elsewhere in forall, exists or when encountering top level decl
         -- need to declare new sort if prop return boolSort  -- sort is used for Type u, Prop, etc
     | Expr.proj .. =>
         -- need to properly represent structure at smt level and use corresponding selector
         throwError f!"proj: not supported for now"
     | Expr.lit .. => throwError f!"unexpected literal expression {e}"
     | Expr.mvar .. => throwError f!"unexpected meta variable {e}"
     | Expr.bvar .. => throwError f!"unexpected bounded variable {e}"
  let st ← visit e (topLevel := true)
  -- assert negation for check sat
  assertTerm (notSmt st)
  let res ← checkSat
  match res with
  | .Valid => logInfo s!"Valid"
  | .Falsified => getModel
  | .Undetermined => logInfo s!"Undetermined" -- TODO: spawn lean proof mode


def translate (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  elabTermAndSynthesize stx none >>= fun e => do
    let (optExpr, env) ← optimize sOpts (← toPropExpr e)
    match (toResult optExpr) with
    | .Valid => logInfo s!"Valid"
    | .Falsified => logWarning s!"Falsified"
    | .Undetermined =>
      discard $ translateExpr sOpts optExpr|>.run (← setSolverProcess sOpts env)
  where
    toPropExpr (e : Expr) : TermElabM Expr := do
    let e_type ← inferType e
    let forall_type ← inferType e_type
    if Expr.isProp e_type then return e
    if Expr.isProp forall_type then return e_type -- case when parsed term is a theorem name
    throwError f!"translate: Term of type Prop expected !!!"

namespace Solver.Smt
