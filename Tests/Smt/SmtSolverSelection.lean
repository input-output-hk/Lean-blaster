import Lean
import Blaster

/-! Tests for backend solver selection (`(solver: ...)` option) and the
    cvc5 backend. See docs/superpowers/specs/2026-07-06-cvc5-backend-design.md. -/

namespace Tests.SmtSolverSelection

-- Explicitly selecting z3 behaves exactly like the default.
#blaster (solver: z3) [∀ (x : Nat), x + 0 = x]

-- The cvc5 identifier parses (end-to-end cvc5 solving is exercised from Task 5 on).
#blaster (solver: cvc5) (only-smt-lib: 1) [∀ (x : Nat), x + 0 = x]

/-! SolverConfig sanity checks. -/
section SolverConfigChecks
open Blaster.Smt Blaster.Options

#guard (SmtSolver.z3).config.spawnArgs == #["-in", "-smt2"]
#guard (SmtSolver.z3).config.versionFlag == "-version"
#guard (SmtSolver.z3).config.usesGetValue == false
#guard (SmtSolver.z3).config.timeoutOption == ":timeout"
#guard (SmtSolver.z3).config.seedOption == ":smt.random-seed"
-- Z3 startup options must match the historical sequence exactly (order matters
-- for the byte-identical command stream guarantee).
#guard (SmtSolver.z3).config.defaultOptions ==
  #[(":print-success", "true"),
    (":produce-models", "true"),
    (":produce-proofs", "true"),
    (":smt.pull-nested-quantifiers", "true"),
    (":smt.mbqi", "true"),
    (":auto_config", "false"),
    (":smt.macro_finder", "true")]

#guard (SmtSolver.cvc5).config.spawnArgs == #["--incremental"]
#guard (SmtSolver.cvc5).config.versionFlag == "--version"
#guard (SmtSolver.cvc5).config.usesGetValue == true
#guard (SmtSolver.cvc5).config.timeoutOption == ":tlimit-per"
#guard (SmtSolver.cvc5).config.seedOption == ":seed"
-- cvc5 must never receive Z3's :smt.* options (it answers `unsupported`,
-- which trips the print-success check).
#guard (SmtSolver.cvc5).config.defaultOptions.all (fun (o, _) => !o.startsWith ":smt.")

end SolverConfigChecks

end Tests.SmtSolverSelection
