import Lean

import Blaster.Reconstruct.Trace

open Lean Elab Tactic Meta

namespace Blaster.Reconstruct

def traceToSimpLemmas (trace : RewriteTrace) : List Name :=
  trace.filterMap λ step =>
    match step with
    | .Rewrite lemmaName => some lemmaName
    | .Unfold fname => some fname
    | .RewriteWithHyp _ => none

def namesToSimpArgs (names : List Name) : MetaM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  names.toArray.mapM fun name => do
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)

def buildSimpTactic (args : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : MetaM Syntax :=
  `(tactic| simp only [$args,*])

def reconstructFromTrace (trace : RewriteTrace) : TacticM Unit := do
  let names := traceToSimpLemmas trace
  let args <- namesToSimpArgs names
  let tac <- buildSimpTactic args
  evalTactic tac

elab "reconstruct" trace:term : tactic => do
  let traceExpr <-
    Lean.Elab.Tactic.elabTerm trace (some (mkConst `Blaster.Reconstruct.RewriteTrace))
  let traceVal <-
    unsafe Lean.Meta.evalExpr RewriteTrace (mkConst `Blaster.Reconstruct.RewriteTrace) traceExpr
  reconstructFromTrace traceVal

end Blaster.Reconstruct
