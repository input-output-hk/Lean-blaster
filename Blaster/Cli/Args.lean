import Blaster.Cli.Types

namespace Blaster.Cli

private def natural (flag value : String) : Except String Nat := do
  let some n := value.toNat? | throw s!"'{flag}' expects a nonnegative integer; received '{value}'"
  return n

private def duration (value : String) : Except String (Option Nat) := do
  if value == "none" then return none
  let (digits, multiplier) :=
    if value.endsWith "s" then (value.dropRight 1, 1)
    else if value.endsWith "m" then (value.dropRight 1, 60)
    else ("", 1)
  let some n := digits.toNat? |
    throw s!"'--solver-timeout' expects a duration; received '{value}'\n\n  Examples: 30s, 2m, none (no solver limit)"
  if n == 0 then throw "'--solver-timeout' must be positive; use 'none' for no solver limit"
  return some (n * multiplier)

private def valueFlags : List String :=
  ["--decl", "--solver-timeout", "--solver", "--seed", "--color", "--theme", "--counterexample", "--llm"]

private def knownFlags : List String := valueFlags ++
  ["--no-counterexample", "--verbose", "--debug", "--json", "--json-report", "--no-progress", "--no-build", "--ascii", "--help", "--version"]

private def unknownFlag (flag : String) : String := Id.run do
  let mut hint := ""
  if flag == "--timout" || flag == "--timeout" then
    hint := "\n\n  Did you mean '--solver-timeout'?"
  else if flag.startsWith "--" then
    if let some candidate := knownFlags.find? (fun f => f.dropRight 1 == flag) then
      hint := s!"\n\n  Did you mean '{candidate}'?"
  return s!"I don't recognize '{flag}'.{hint}\n\n  Run 'lean-blaster --help' to see the available options"

private def applyValue (cfg : Config) (flag value : String) : Except String Config := do
  if value.isEmpty then throw s!"'{flag}' needs a value"
  match flag with
  | "--decl" => return { cfg with declarations := cfg.declarations.push value }
  | "--solver-timeout" => return { cfg with timeout := some (← duration value) }
  | "--solver" => return { cfg with solver := some value }
  | "--seed" => return { cfg with seed := some (← natural flag value) }
  | "--counterexample" =>
    unless ["summary", "full", "raw", "none"].contains value do
      throw s!"'--counterexample' expects summary, full, raw, or none; received '{value}'"
    return { cfg with counterexamples := value != "none", counterexampleView := value }
  | "--llm" => return { cfg with llmReport := some value }
  | "--color" =>
    unless ["auto", "always", "never"].contains value do
      throw s!"'--color' expects auto, always, or never; received '{value}'"
    return { cfg with color := value }
  | "--theme" =>
    unless ["auto", "dark", "light"].contains value do
      throw s!"'--theme' expects auto, dark, or light; received '{value}'"
    return { cfg with theme := value }
  | _ => throw (unknownFlag flag)

private def positional (cfg : Config) (arg : String) (literal : Bool) : Except String Config := do
  if cfg.command == "help" && !literal then
    if ["check", "discover", "doctor"].contains arg then return { cfg with command := arg }
    throw s!"I don't recognize the command '{arg}'.\n\n  Try 'lean-blaster check FILE.lean', 'lean-blaster discover FILE.lean', or 'lean-blaster doctor'"
  if cfg.command != "check" && cfg.command != "discover" then
    throw s!"'{cfg.command}' doesn't accept a file argument"
  if cfg.file.isSome then throw "I accept one file or directory at a time; received more than one path"
  return { cfg with file := some arg }

private def parseLoop : List String → Config → Bool → Except String Config
  | [], cfg, _ => pure cfg
  | "--" :: rest, cfg, false => parseLoop rest cfg true
  | arg :: rest, cfg, literal => do
    if literal then return ← parseLoop rest (← positional cfg arg true) true
    match arg with
    | "-h" | "--help" => parseLoop rest { cfg with help := true } false
    | "--version" => parseLoop rest { cfg with version := true } false
    | "-v" | "--verbose" => parseLoop rest { cfg with verbose := true } false
    | "--debug" => parseLoop rest { cfg with debug := true, verbose := true } false
    | "--json" => parseLoop rest { cfg with json := true } false
    | "--json-report" => parseLoop rest { cfg with jsonReport := true } false
    | "--no-progress" => parseLoop rest { cfg with noProgress := true } false
    | "--no-build" => parseLoop rest { cfg with noBuild := true } false
    | "--no-counterexample" => parseLoop rest { cfg with counterexamples := false, counterexampleView := "none" } false
    | "--ascii" => parseLoop rest { cfg with ascii := true } false
    | _ =>
      if arg.startsWith "-" then
        let parts := arg.splitOn "="
        let flag := parts.head!
        unless valueFlags.contains flag do throw (unknownFlag flag)
        if parts.length > 1 then
          parseLoop rest (← applyValue cfg flag ("=".intercalate parts.tail!)) false
        else
          let value :: tail := rest | throw s!"'{flag}' needs a value"
          if value.startsWith "--" then throw s!"'{flag}' needs a value; received option '{value}'"
          parseLoop tail (← applyValue cfg flag value) false
      else
        parseLoop rest (← positional cfg arg false) false

def parseArgs (args : List String) : Except String Config := do
  let cfg ← parseLoop args {} false
  if cfg.help || cfg.version then return cfg
  if (cfg.command == "check" || cfg.command == "discover") && cfg.file.isNone then
    throw s!"I need a Lean file or directory to {cfg.command}.\n\n  lean-blaster {cfg.command} Properties.lean"
  if cfg.command != "check" && (!cfg.declarations.isEmpty || cfg.timeout.isSome ||
      cfg.seed.isSome || cfg.counterexampleView != "summary" || cfg.noBuild) then
    throw "Property selection and solver options belong to 'lean-blaster check'"
  if cfg.command == "discover" && cfg.solver.isSome then
    throw "'discover' reads source without running Z3, so it doesn't accept '--solver'"
  if cfg.command != "check" && cfg.llmReport.isSome then
    throw "'--llm' writes a report of executed checks, so use it with 'lean-blaster check'"
  if cfg.json && cfg.jsonReport then
    throw "Choose either '--json' (streaming events) or '--json-report' (one report)"
  if cfg.machineOutput && cfg.color == "always" then
    throw "JSON output and '--color always' cannot be combined; JSON contains unstyled data"
  return cfg

private def outputHelp : String :=
  "\n\nOutput options:\n  -v, --verbose         Show stages and elapsed time\n  --debug               Include additional diagnostic context\n  --json                Stream one JSON event per line to stdout\n  --json-report         Write one JSON report after completion\n  --llm FILE            Write a Markdown report for coding agents (check only)\n  --color MODE          auto, always, never [default: auto]\n  --theme MODE          auto, dark, light [default: auto]\n  --no-progress         Disable live progress\n  --ascii               Use ASCII status symbols\n  -h, --help            Show help\n  --version             Show the executable and Lean version\n"

def helpText (command : String) : String :=
  if command == "doctor" then
    "I'll check access to Lean's compiled libraries and Z3.\n\nUsage: lean-blaster doctor [OPTIONS]\n\nExamples:\n  lean-blaster doctor\n  lean-blaster doctor --solver /path/to/z3\n  lean-blaster doctor --json\n\nSolver option:\n  --solver PATH         Select a Z3 executable" ++ outputHelp
  else if command == "discover" then
    "I'll find direct '#blaster' commands and 'blaster' tactics in source, without elaboration or solver work.\n\nUsage: lean-blaster discover FILE.lean|DIRECTORY [OPTIONS]\n\nExamples:\n  lean-blaster discover Properties.lean\n  lean-blaster discover Properties.lean --json\n\nDirectories are scanned recursively. Each source is read once; import-only umbrellas don't repeat their children. Discovery is syntactic; macros and elaboration may change which checks execute." ++ outputHelp
  else if command == "check" then
    "Check #blaster commands and 'by blaster' tactic calls, or select named properties with --decl.\n\nUsage: lean-blaster check FILE.lean|DIRECTORY [OPTIONS]\n\nExamples:\n  lean-blaster check Properties.lean\n  lean-blaster check Properties.lean --decl balance_nonnegative --solver-timeout 30s\n  lean-blaster check Properties.lean --json\n\nDirectories are scanned recursively; import-only umbrellas don't schedule their children again.\n\nCheck options:\n  --decl NAME           Select a fully qualified property (repeatable)\n  --solver-timeout TIME  Per-query solver limit: 30s, 2m, none\n  --solver PATH         Select a Z3 executable\n  --seed N              Set the solver seed (including zero)\n  --counterexample MODE summary, full, raw, none [default: summary]\n  --no-counterexample   Skip counterexample retrieval (same as none)\n  --no-build            Use existing compiled imports without building" ++ outputHelp ++
    "\nRun 'lean-blaster doctor' to check your installation.\nValid results are not reconstructed as Lean proofs.\n"
  else
    "lean-blaster · a verification assistant for Lean\n\nUsage: lean-blaster COMMAND [OPTIONS]\n\nCommands:\n  check FILE|DIRECTORY      Check properties with Blaster\n  discover FILE|DIRECTORY   Find Blaster sites in source\n  doctor               Check Lean and solver setup\n\nExamples:\n  lean-blaster check Properties.lean\n  lean-blaster discover Properties.lean --json\n  lean-blaster doctor\n\nRun 'lean-blaster COMMAND --help' for command options.\nValid results are not reconstructed as Lean proofs.\n"

end Blaster.Cli
