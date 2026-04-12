/-
  Blaster.Wasm.SmtCapture — Utility to capture SMT-LIB 2 output from Blaster

  This module provides `captureSmtLib2`, which runs Blaster's translation
  pipeline on a proposition Expr and returns the resulting SMT-LIB 2 query
  as a String — without invoking the backend solver.

  Designed for pre-computing SMT queries at elaboration time so they can
  be embedded in WASM builds where MetaM is not available at runtime.
-/
import Blaster.Smt.Translate
import Blaster.Logging

open Lean Meta Blaster.Optimize Blaster.Options Blaster.Smt

namespace Blaster.Wasm

/-- Run Blaster's optimization + SMT translation pipeline on a proposition
    `Expr` and return the accumulated SMT-LIB 2 commands as a single String.

    The returned String is a complete SMT-LIB 2 script including a final
    `(check-sat)` command, ready to be fed to Z3.

    **Important**: This function runs in `MetaM` and requires a fully
    populated Lean `Environment`. It is intended to be called at elaboration
    time (during `lake build`) where MetaM is available.

    Options:
    - `unfoldDepth`: recursion unfolding depth (default 100)
    - `timeout`: solver timeout (not used since solver is not invoked)
-/
def captureSmtLib2 (goalType : Expr) (unfoldDepth : Nat := 100) : MetaM String := do
  let sOpts : BlasterOptions := {
    dumpSmtLib := true,      -- accumulate commands in smtCommands array
    onlySmtLib := true,      -- do NOT create a solver process
    unfoldDepth := unfoldDepth,
    generateCex := false,
    verbose := 0
  }
  let env : TranslateEnv := {(default : TranslateEnv) with
    optEnv.options.solverOptions := sOpts}
  let ((_, _), finalEnv) ←
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
      IO.setNumHeartbeats 0
      Translate.main goalType (logUndetermined := false) |>.run env
  -- Serialize all accumulated SMT commands
  let smt := finalEnv.smtEnv.smtCommands.foldl
    (fun acc c => acc ++ toString c ++ "\n") ""
  -- Append check-sat (not emitted by Translate.main when onlySmtLib=true)
  return smt ++ "(check-sat)\n"

/-- Like `captureSmtLib2` but also returns the Blaster `Result` from the
    optimization phase. If the result is already `Valid` or `Falsified`
    after optimization (before SMT translation), the SMT string will be empty. -/
def captureSmtLib2WithResult (goalType : Expr) (unfoldDepth : Nat := 100)
    : MetaM (Result × String) := do
  let sOpts : BlasterOptions := {
    dumpSmtLib := true,
    onlySmtLib := true,
    unfoldDepth := unfoldDepth,
    generateCex := false,
    verbose := 0
  }
  let env : TranslateEnv := {(default : TranslateEnv) with
    optEnv.options.solverOptions := sOpts}
  let ((result, _), finalEnv) ←
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
      IO.setNumHeartbeats 0
      Translate.main goalType (logUndetermined := false) |>.run env
  let smt := finalEnv.smtEnv.smtCommands.foldl
    (fun acc c => acc ++ toString c ++ "\n") ""
  let smt := if smt.isEmpty then "" else smt ++ "(check-sat)\n"
  return (result, smt)

/-- Capture SMT-LIB 2 for a named theorem in the current environment.
    Looks up the theorem by `Name`, extracts its type, and runs Blaster. -/
def captureSmtLib2ForTheorem (thmName : Name) (unfoldDepth : Nat := 100)
    : MetaM String := do
  let env ← getEnv
  let some info := env.find? thmName
    | throwError "captureSmtLib2ForTheorem: theorem '{thmName}' not found in environment"
  captureSmtLib2 info.type unfoldDepth

end Blaster.Wasm
