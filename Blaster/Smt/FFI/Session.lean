import Blaster.Smt.FFI.Build
import Blaster.Smt.FFI.Solver
import Blaster.Smt.Result
import Blaster.Smt.Term

namespace Blaster.Smt.FFI
open Blaster.Smt

structure Z3Session where
  ctx    : Context
  solver : Solver
  state  : IO.Ref BuildState

def Z3Session.create : IO Z3Session := do
  let ctx ← mkContext
  let solver ← ctx.mkSolver
  let st ← BuildState.mk ctx
  let ref ← IO.mkRef st
  return { ctx, solver, state := ref }

/-- Run a BuildM action against the session's persistent state. -/
def Z3Session.run (sess : Z3Session) (m : BuildM α) : IO α := do
  let st ← sess.state.get
  let (a, st') ← StateRefT'.run m st
  sess.state.set st'
  return a

def Z3Session.runCommand (sess : Z3Session) (c : SmtCommand) : IO Unit :=
  sess.run (_root_.Blaster.Smt.FFI.runCommand c)

def Z3Session.assert (sess : Z3Session) (t : SmtTerm) : IO Unit := do
  let a ← sess.run (buildTerm t)
  sess.solver.assert a

/-- Extract counterexample strings for the top-level vars, matching the legacy
    ordering (outer array forward, each inner list reversed). -/
def Z3Session.getModel (sess : Z3Session)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO (List String) := do
  if !genCex then return []
  let mut cex := #[]
  for vars in topVars do
    for (sym, name) in vars.reverse do
      let a ← sess.run (buildTerm (smtSimpleVarId sym))
      let v ← sess.solver.evalStr a
      cex := cex.push s!"{name}: {v}"
  return cex.toList

/-- Check satisfiability of the asserted formula, mapping Z3's lbool to Result.
    On `sat`, evaluates top-level vars for the counterexample. -/
def Z3Session.checkSat (sess : Z3Session)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  match ← sess.solver.check with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

/-- Check satisfiability of the asserted formula under the given assumption
    literals, mapping Z3's lbool to Result. Each assumption term is built against
    the persistent build state (mirroring `assert`/`checkSat`), so consts declared
    earlier via `runCommand` resolve through `buildIdent`. On `sat`, evaluates
    top-level vars for the counterexample. -/
def Z3Session.checkAssuming (sess : Z3Session) (assumps : Array SmtTerm)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  let asts ← assumps.mapM (fun t => sess.run (buildTerm t))
  match ← sess.solver.checkAssuming asts with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

/-- Route a declarative SmtCommand to the FFI session. Declarations go to the
    build env; assert goes to the solver; options/check/model/exit are handled
    elsewhere (no-op here). -/
def Z3Session.submit (sess : Z3Session) (c : SmtCommand) : IO Unit := do
  match c with
  | .assertTerm t => sess.assert t
  | .checkSat | .checkSatAssuming _ | .getModel | .getProof | .evalTerm _ | .exitSmt => pure ()
  | .setLogic _ | .setOption _ _ => pure ()   -- options: a later task
  | other => sess.runCommand other

end Blaster.Smt.FFI
