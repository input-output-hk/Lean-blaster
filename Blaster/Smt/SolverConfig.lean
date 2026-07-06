import Blaster.Command.Options

open Blaster.Options

namespace Blaster.Smt

/-- Per-solver configuration: every point where the supported backend
    solvers diverge lives here. Adding a new backend means adding a new
    `SolverConfig` value and a `SmtSolver` constructor — nothing else. -/
structure SolverConfig where
  /-- Human-readable solver name, used in error messages. -/
  displayName : String
  /-- Commands probed in order to locate the solver binary
      (native PATH first, then WSL fallback). -/
  candidates : Array String
  /-- Arguments passed when spawning the solver process. -/
  spawnArgs : Array String
  /-- Flag used to probe the binary (`<candidate> <versionFlag>`). -/
  versionFlag : String
  /-- Minimal supported version. Informational: used in error messages,
      not parsed from the binary (same behavior as historically for Z3). -/
  minVersion : String
  /-- `set-option` pairs submitted at startup, in order. -/
  defaultOptions : Array (String × String)
  /-- Option name for the per-query timeout, in milliseconds. -/
  timeoutOption : String
  /-- Option name for the random seed. -/
  seedOption : String
  /-- When `true`, model values are queried with the standard
      `(get-value (t))` instead of Z3's non-standard `(eval t)`. -/
  usesGetValue : Bool

/-- Z3 backend configuration.
    NOTE: `defaultOptions` must reproduce the historical
    `setDefaultSmtOptions` sequence exactly so that the command stream
    sent to Z3 remains byte-identical. -/
def z3Config : SolverConfig := {
  displayName := "Z3"
  candidates := #["z3", "wsl z3"]
  spawnArgs := #["-in", "-smt2"]
  versionFlag := "-version"
  minVersion := "4.15.2"
  defaultOptions := #[
    (":print-success", "true"),
    (":produce-models", "true"),
    (":produce-proofs", "true"),
    (":smt.pull-nested-quantifiers", "true"),
    (":smt.mbqi", "true"),
    (":auto_config", "false"),
    (":smt.macro_finder", "true")
  ]
  timeoutOption := ":timeout"
  seedOption := ":smt.random-seed"
  usesGetValue := false
}

/-- cvc5 backend configuration.
    NOTE: no `:produce-proofs` (proof retrieval is unused and expensive in
    cvc5). `:full-saturate-quant` is cvc5's main quantifier-instantiation
    strengthening, playing the role Z3's `:smt.mbqi`/`:smt.macro_finder`
    play in the Z3 configuration. -/
def cvc5Config : SolverConfig := {
  displayName := "cvc5"
  candidates := #["cvc5", "wsl cvc5"]
  spawnArgs := #["--incremental"]
  versionFlag := "--version"
  minVersion := "1.2.1"
  defaultOptions := #[
    (":print-success", "true"),
    (":produce-models", "true"),
    (":full-saturate-quant", "true")
  ]
  timeoutOption := ":tlimit-per"
  seedOption := ":seed"
  usesGetValue := true
}

/-- The configuration of the selected backend solver. -/
def _root_.Blaster.Options.SmtSolver.config : SmtSolver → SolverConfig
  | .z3 => z3Config
  | .cvc5 => cvc5Config

end Blaster.Smt
