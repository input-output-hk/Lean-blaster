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

/-- Run a check action (returns Z3 lbool code 2/0/1). If a cancel token is provided,
    run on a task and poll: on cancellation, interrupt the solver and return the
    interrupted result. With no token, call directly (no task overhead — preserves the
    fast synchronous path). -/
partial def Z3Session.runCheckCancellable (sess : Z3Session) (check : IO UInt32)
    (cancelTk? : Option IO.CancelToken) : IO UInt32 := do
  match cancelTk? with
  | none => check
  | some tk =>
    let task ← IO.asTask check
    loop sess tk task
where
  loop (sess : Z3Session) (tk : IO.CancelToken)
      (task : Task (Except IO.Error UInt32)) : IO UInt32 := do
    if ← IO.hasFinished task then
      IO.ofExcept task.get
    else if ← tk.isSet then
      sess.solver.interrupt
      IO.ofExcept task.get      -- let the interrupted check finish; it returns undef(1)
    else
      -- Poll interval. At Lean elaboration time `cancelTk?` is ALWAYS `some`, so every FFI
      -- check routes through this task+poll loop; a small (1ms) interval bounds worst-case
      -- poll latency for a fast check that loses the first `hasFinished` race. (On the
      -- FFIEndToEnd workload 1ms vs 10ms was within measurement noise; 1ms is the safer
      -- default for larger check-heavy workloads.)
      IO.sleep 1
      loop sess tk task

/-- Cancellable variant of `checkSat`: routes the blocking check through
    `runCheckCancellable` with the given token. Same `Result` mapping as `checkSat`. -/
def Z3Session.checkSatCancel (sess : Z3Session) (cancelTk? : Option IO.CancelToken)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  match ← sess.runCheckCancellable sess.solver.check cancelTk? with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

/-- Cancellable variant of `checkAssuming`: builds the assumption Asts against the
    persistent build state (as `checkAssuming` does), then routes the blocking
    check-assumptions through `runCheckCancellable`. Same `Result` mapping. -/
def Z3Session.checkAssumingCancel (sess : Z3Session) (assumps : Array SmtTerm)
    (cancelTk? : Option IO.CancelToken)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  let asts ← assumps.mapM (fun t => sess.run (buildTerm t))
  match ← sess.runCheckCancellable (sess.solver.checkAssuming asts) cancelTk? with
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
