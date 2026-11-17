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

/-- Create an in-process Z3 session (context + solver + build state).

    The engine parameters that legacy `setDefaultSmtOptions` emits as SMT-LIB
    `(set-option …)` commands (`auto_config`, `smt.mbqi`, `smt.macro_finder`,
    `smt.pull_nested_quantifiers`) are installed here as PROCESS-GLOBAL Z3 params
    (`Z3_global_param_set`) BEFORE `mkContext`/`mkSolver`, because:
    * `Z3_update_param_value` rejects the `smt.*` module params (error INVALID_ARG),
    * a default `auto_config = true` overrides solver-level `smt.*` params, so the
      canonical fix is to disable it before the solver is built, and
    * global params live in a separate store from `Z3_solver_set_params`, so they are
      immune to the later `setTimeout`/`setRandomSeed` `Z3_solver_set_params` calls.

    These are the FIXED defaults from `setDefaultSmtOptions` (they never vary between
    goals), so the individual `Blaster.Smt.Env` engine-param setters (`setMbqi` etc.)
    remain no-ops on the FFI backend — the values applied here always match what they
    would request. `random_seed`/`timeout` stay solver-level (installed on demand). -/
def Z3Session.create : IO Z3Session := do
  -- Mirror legacy `setDefaultSmtOptions` engine params (must precede solver creation).
  globalParamSet "auto_config" "false"
  globalParamSet "smt.mbqi" "true"
  globalParamSet "smt.macro_finder" "true"
  globalParamSet "smt.pull_nested_quantifiers" "true"
  globalParamSet "smt.case_split_relevant_first" "true"
  globalParamSet "smt.qi.persist_instances" "true"
  globalParamSet "smt.arith.nl.grobner_expand_terms" "false"
  globalParamSet "smt.arith.nl.reduce_pseudo_linear" "false"
  globalParamSet "smt.arith.nl.grobner_exp_delay" "false"
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
    (topVars : Array (List TopLevelVar)) (genCex : Bool) : IO (List String) := do
  if !genCex then return []
  if topVars.isEmpty then return [← sess.solver.modelStr]
  let mut cex := #[]
  for vars in topVars do
    for v in vars.reverse do
      let a ← sess.run (buildTerm (smtSimpleVarId v.symbol))
      let raw ← sess.solver.evalStr a
      cex := cex.push s!"{v.userName}: {raw}"
  return cex.toList

/-- Check satisfiability of the asserted formula, mapping Z3's lbool to Result.
    On `sat`, evaluates top-level vars for the counterexample. -/
def Z3Session.checkSat (sess : Z3Session)
    (topVars : Array (List TopLevelVar)) (genCex : Bool) : IO Result := do
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
    (topVars : Array (List TopLevelVar)) (genCex : Bool) : IO Result := do
  let asts ← assumps.mapM (fun t => sess.run (buildTerm t))
  match ← sess.solver.checkAssuming asts with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

/-- Run a check action (returns Z3 lbool code 2/0/1). Keep every ordinary Z3
    operation on the caller's thread: Z3 contexts cannot be accessed from two
    threads, except that `Z3_solver_interrupt` may be called from another thread.
    When cancellation is enabled, a helper task polls only the token and invokes
    that permitted interrupt. -/
partial def Z3Session.runCheckCancellable (sess : Z3Session) (check : IO UInt32)
    (cancelTk? : Option IO.CancelToken) : IO UInt32 := do
  let some tk := cancelTk? | check
  if ← tk.isSet then return 1
  let finished ← IO.CancelToken.new
  let poll ← IO.asTask (pollCancel sess tk finished)
  let result ← try check finally finished.set
  discard <| IO.ofExcept poll.get
  return result
where
  pollCancel (sess : Z3Session) (tk finished : IO.CancelToken) : IO Unit := do
    if ← finished.isSet then return
    if ← tk.isSet then
      sess.solver.interrupt
    else
      IO.sleep 1
      pollCancel sess tk finished

/-- Cancellable variant of `checkSat`: routes the blocking check through
    `runCheckCancellable` with the given token. Same `Result` mapping as `checkSat`. -/
def Z3Session.checkSatCancel (sess : Z3Session) (cancelTk? : Option IO.CancelToken)
    (topVars : Array (List TopLevelVar)) (genCex : Bool) : IO Result := do
  match ← sess.runCheckCancellable sess.solver.check cancelTk? with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

/-- Cancellable variant of `checkAssuming`: builds the assumption Asts against the
    persistent build state (as `checkAssuming` does), then routes the blocking
    check-assumptions through `runCheckCancellable`. Same `Result` mapping. -/
def Z3Session.checkAssumingCancel (sess : Z3Session) (assumps : Array SmtTerm)
    (cancelTk? : Option IO.CancelToken)
    (topVars : Array (List TopLevelVar)) (genCex : Bool) : IO Result := do
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
  | .setLogic "ALL" | .setSimplifier "recfun-finder" => pure ()
  | .setOption opt value =>
      let fixed := #[
        (":print-success", "true"), (":produce-models", "true"),
        (":smt.pull-nested-quantifiers", "true"), (":smt.mbqi", "true"),
        (":auto_config", "false"), (":smt.macro_finder", "true"),
        (":smt.case_split_relevant_first", "true"),
        (":smt.qi.persist_instances", "true"),
        (":smt.arith.nl.grobner_expand_terms", "false"),
        (":smt.arith.nl.reduce_pseudo_linear", "false"),
        (":smt.arith.nl.grobner_exp_delay", "false")]
      if fixed.contains (opt, value) then return
      if opt == ":smt.random-seed" then
        let some seed := value.toNat?
          | throw (IO.userError s!"FFI backend: invalid random seed {value}")
        sess.solver.setRandomSeed (UInt32.ofNat seed)
        return
      if opt == ":timeout" then
        let some timeout := value.toNat?
          | throw (IO.userError s!"FFI backend: invalid timeout {value}")
        sess.solver.setTimeout (UInt32.ofNat (min timeout 4294967295))
        return
      throw (IO.userError s!"FFI backend: unsupported solver option {opt} = {value}")
  | .setLogic logic => throw (IO.userError s!"FFI backend: unsupported logic {logic}")
  | .setSimplifier simplifier =>
      throw (IO.userError s!"FFI backend: unsupported simplifier {simplifier}")
  | other => sess.runCommand other

end Blaster.Smt.FFI
