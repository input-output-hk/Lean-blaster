import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Translate.Env
import Solver.Optimize.Basic
open Lean Elab Command Term Meta

namespace Solver

/-- Result of an SMT query. -/
inductive Result where
  | Valid        : Result
  | Falsified    : Result
  | Undetermined : Result
deriving Repr, DecidableEq


def toResult (e : Expr) : Result :=
 match e with
 | Expr.const ``True _  => Result.Valid
 | Expr.const ``False _  => Result.Falsified
 | _ => Result.Undetermined

def translate (sOpts: SolverOptions) (stx : Syntax) : TermElabM Expr := do
  elabTermAndSynthesize stx none >>= fun e => do
    return (← (Solver.Optimize.optimize sOpts (← toPropExpr e))).1

  where
    toPropExpr (e : Expr) : TermElabM Expr := do
    let e_type ← inferType e
    let forall_type ← inferType e_type
    if Expr.isProp e_type
    then return e
    else if Expr.isProp forall_type
         then return e_type -- case when parsed term is a theorem name
         else throwError f!"translate: Term of type Prop expected !!!"


end Solver
