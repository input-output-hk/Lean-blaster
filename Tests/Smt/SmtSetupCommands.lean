import Blaster

namespace Test.SmtSetupCommands

open Blaster.Options Blaster.Optimize Blaster.Smt

/-! ## Test objectives to validate the emitted default solver setup commands

    `setBlasterProcess` resolves the backend and records the same pure
    `solverSetupCommands` transcript used to initialize live sessions. These
    tests run it in `only-smt-lib` mode (no solver process is spawned) and pin
    the exact per-solver sequence, guarding:
     - the default options every query relies on (`print-success` handshake,
       model/proof production, quantifier instantiation, macro elimination);
     - solver-specific option spellings and the seconds → milliseconds
       timeout mapping (z3 `:timeout` vs cvc5 `:tlimit-per`);
     - Blaster's pinned command ordering: cvc5's `(set-logic ALL)` comes
       after all options, while z3 gets no `set-logic` at all.

    `solver:` and `timeout:` are set explicitly so the runs are independent
    of the `BLASTER_SOLVER` / `BLASTER_TIMEOUT` environment variables.
-/

/-- Run the solver setup (`setBlasterProcess`) in `only-smt-lib` mode on a
    fresh translation environment and return the recorded setup commands,
    rendered exactly as they would be sent to the solver. -/
def setupCommands (solver : SmtSolver) : Lean.MetaM (Array String) := do
  let sOpts : BlasterOptions :=
    { onlySmtLib := true, dumpSmtLib := true, solver := some solver, timeout := some 7 }
  let env : TranslateEnv := default
  let env := { env with optEnv.options.solverOptions := sOpts }
  let (_, env) ← setBlasterProcess.run env
  let some record := env.smtEnv.solverRecords.find? (·.solver == solver)
    | throwError "missing solver setup record"
  return record.setupCommands.map toString

/-- Print the setup commands one per line (pinned with `#guard_msgs`). -/
def printSetupCommands (solver : SmtSolver) : Lean.MetaM Unit := do
  for c in (← setupCommands solver) do
    IO.println c

/-! # z3: default setup sequence (no `set-logic`: z3 solves in `ALL` mode
     when no logic is set) -/

/--
info: (set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :smt.pull-nested-quantifiers true)
(set-option :smt.mbqi true)
(set-option :auto_config false)
(set-option :smt.macro_finder true)
(set-option :timeout 7000)
-/
#guard_msgs in
#eval printSetupCommands .z3

/-! # cvc5: default setup sequence, `(set-logic ALL)` last -/

/--
info: (set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :mbqi true)
(set-option :macros-quant true)
(set-option :tlimit-per 7000)
(set-logic ALL)
-/
#guard_msgs in
#eval printSetupCommands .cvc5

/-! # Blaster-pinned cvc5 ordering invariant, independent of option spellings:
     the setup ends with exactly one `set-logic`, and everything before it
     is a `set-option`. -/

/-- info: true -/
#guard_msgs in
#eval show Lean.MetaM Bool from do
  let cmds ← setupCommands .cvc5
  return cmds.back? == some "(set-logic ALL)"
      && cmds.pop.all (·.startsWith "(set-option ")

end Test.SmtSetupCommands
