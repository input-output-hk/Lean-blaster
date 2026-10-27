import Lean
import Blaster.Command.Options

namespace Blaster.Cli

/-- Presentation-independent command configuration. Optional fields override source options. -/
structure Config where
  command : String := "help"
  file : Option String := none
  declarations : Array String := #[]
  timeout : Option (Option Nat) := none
  solver : Option String := none
  seed : Option Nat := none
  counterexamples : Bool := true
  /-- Terminal presentation of solver witnesses; JSON always preserves raw values. -/
  counterexampleView : String := "summary"
  verbose : Bool := false
  debug : Bool := false
  /-- Stream newline-delimited JSON events. -/
  json : Bool := false
  /-- Emit the legacy single JSON report after completion. -/
  jsonReport : Bool := false
  noProgress : Bool := false
  noBuild : Bool := false
  color : String := "auto"
  theme : String := "auto"
  ascii : Bool := false
  help : Bool := false
  version : Bool := false
  deriving Inhabited

def Config.machineOutput (cfg : Config) : Bool := cfg.json || cfg.jsonReport

structure Location where
  file : String
  line : Nat
  column : Nat
  deriving Lean.ToJson

/-- A source span uses one-based lines and columns and an exclusive end. -/
structure SourceRange where
  start : Location
  stop : Location
  deriving Lean.ToJson

/-- A syntactic Blaster site found without elaborating or invoking the solver. -/
structure DiscoveryItem where
  kind : String
  name : Option String := none
  body : String
  invocationRange : SourceRange
  bodyRange : SourceRange
  deriving Lean.ToJson

/-- A check result is data, independent of Lean's human-readable diagnostics. -/
structure CheckResult where
  property : String
  invocation : String := "command"
  status : String
  /-- Nondefault source expectation from `(solve-result: 1|2)`, if present. -/
  expectedStatus : Option String := none
  origin : String
  location : Location
  elapsedMs : Nat
  solverTimeoutSeconds : Option Nat
  goal : Option String := none
  counterexample : Array String := #[]
  reason : Option String := none
  deriving Lean.ToJson

structure Diagnostic where
  severity : String
  message : String
  location : Option Location := none
  /-- Stable category for consumers that want to distinguish routine Lean lint. -/
  code : Option String := none
  deriving Lean.ToJson

structure Report where
  schemaVersion : Nat := 1
  results : Array CheckResult := #[]
  diagnostics : Array Diagnostic := #[]
  interrupted : Bool := false
  signal : Option Nat := none
  trust : String := "I don't reconstruct Lean proofs yet; valid tactic goals use the Blaster.Tactic.blasterProven axiom."
  deriving Lean.ToJson

def Report.exitCode (r : Report) : UInt32 :=
  if r.interrupted then (128 + r.signal.getD 2).toUInt32
  else if r.diagnostics.any (·.severity == "error") ||
      r.results.any (fun result => result.status == "error" || result.status == "skipped") then 4
  else if r.results.any (·.status == "falsified") then 1
  else if r.results.any (·.status == "undetermined") then 3
  else 0

def Config.solverOptions (cfg : Config) (base : Options.BlasterOptions := {}) : Options.BlasterOptions :=
  { base with
    solverPath := cfg.solver.or base.solverPath
    timeout := cfg.timeout.getD base.timeout
    randomSeed := cfg.seed.or base.randomSeed
    generateCex := cfg.counterexamples && base.generateCex
    -- CLI rendering owns output, including progress. Library logging writes to stdout.
    verbose := 0
    dumpSmtLib := false }

end Blaster.Cli
