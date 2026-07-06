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

#guard (SmtSolver.cvc5).config.spawnArgs ==
  #["--incremental", "--parsing-mode=lenient", "--dt-nested-rec"]
#guard (SmtSolver.cvc5).config.versionFlag == "--version"
#guard (SmtSolver.cvc5).config.usesGetValue == true
#guard (SmtSolver.cvc5).config.timeoutOption == ":tlimit-per"
#guard (SmtSolver.cvc5).config.seedOption == ":seed"
-- cvc5 must never receive Z3's :smt.* options (it answers `unsupported`,
-- which trips the print-success check).
#guard (SmtSolver.cvc5).config.defaultOptions.all
  (fun (o, _) => !o.startsWith ":smt." && o != ":auto_config")

end SolverConfigChecks

/-! SmtCommand.getValue renders as the standard get-value command. -/
section GetValueChecks
open Blaster.Smt

#guard toString (SmtCommand.getValue (smtSimpleVarId (mkNormalSymbol "x"))) == "(get-value (x))"

end GetValueChecks

/-! get-value response unwrapping (shapes verified against cvc5 1.2.1). -/
section UnwrapChecks
open Blaster.Smt

#guard unwrapGetValue "((x 4))\n" == "4\n"
#guard unwrapGetValue "(($5 (- 4)))\n" == "(- 4)\n"
#guard unwrapGetValue "((r Idle))\n" == "Idle\n"
#guard unwrapGetValue "((p (mk (- 7) 0)))\n" == "(mk (- 7) 0)\n"

end UnwrapChecks

/-! End-to-end cvc5 solving.
    NOTE: goals here are chosen so the pre-SMT optimizer cannot fold them
    to `True` — each invocation genuinely reaches the cvc5 process. -/
section Cvc5EndToEnd

-- Valid goal proved by cvc5 (unsat internally): uninterpreted-function congruence.
#blaster (solver: cvc5) [∀ (f : Nat → Nat) (x y : Nat), x = y → f x = f y]

-- Falsified goal: cvc5 produces a model through (get-model).
#blaster (solver: cvc5) (solve-result: 1) [∀ (x : Int), x < 0]

-- Falsified without counterexample generation.
#blaster (solver: cvc5) (solve-result: 1) (gen-cex: 0) [∀ (x : Int), x < 0]

-- Timeout option maps to :tlimit-per for cvc5.
#blaster (solver: cvc5) (timeout: 10) [∀ (f : Nat → Nat) (x y : Nat), x = y → f x = f y]

-- Random seed maps to :seed for cvc5.
#blaster (solver: cvc5) (random-seed: 42) [∀ (f : Nat → Nat) (x y : Nat), x = y → f x = f y]

-- The blaster tactic accepts the solver option too.
example : ∀ (f : Nat → Nat) (x y : Nat), x = y → f x = f y := by blaster (solver: cvc5)

end Cvc5EndToEnd

end Tests.SmtSolverSelection
