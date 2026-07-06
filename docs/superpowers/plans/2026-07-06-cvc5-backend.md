# CVC5 Backend Solver Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add cvc5 as a selectable backend SMT solver (per-invocation `(solver: cvc5)` option), with the whole test suite passing under both Z3 and cvc5 via inline sibling test invocations.

**Architecture:** A `SmtSolver` enum in `BlasterOptions` selects the backend; a per-solver `SolverConfig` record centralizes every divergence (spawn command/args, version probe, startup `set-option` list, timeout/seed option names, `eval` vs `get-value`). `Blaster/Smt/Env.lean` becomes config-driven; Z3's command stream stays identical to today in the default configuration.

**Tech Stack:** Lean 4 (4.24.0), Lake, Z3 4.15.2, cvc5 1.2.1, Python 3 (test-duplication script).

**Spec:** `docs/superpowers/specs/2026-07-06-cvc5-backend-design.md`

**Verified solver facts** (probed against cvc5 1.2.1 — do not re-litigate):
- cvc5 reads SMT-Lib from stdin with no file argument; `--incremental` is required because BMC/K-Induction issue multiple `check-sat-assuming` queries.
- cvc5 rejects `(eval t)`; `(get-value (t))` responds `((t value))` on one line, e.g. `((x 4))`, `((i (- 4)))`, `((p (mk (- 7) 0)))`. The bare value matches Z3's `eval` output format.
- cvc5 answers `unsupported` (not `success`) to Z3's `:smt.*` / `:auto_config` options — that would trip `trySubmitCommand!`'s success check, so cvc5 must never receive them.
- cvc5 accepts `:print-success`, `:produce-models`, `:seed`, `:tlimit-per` (ms), `:full-saturate-quant`, quantifier annotations (`:qid`/`:pattern`/`:named`), `to_int`, `^`, `define-funs-rec`, `declare-datatype(s)`; `(get-model)` output has the same `(` … `)\n` bracket shape as Z3.
- `z3 -version` vs `cvc5 --version` (flag spelling differs).

**Build/test commands used throughout:**
- Build library: `lake build Blaster` (from repo root `/Users/romainsoulat/Lean-blaster`)
- Build one test module: `lake build Tests.Smt.SmtSolverSelection`
- Full suite: `LEAN_NUM_THREADS=5 lake test` (slow — only in the final tasks)

---

### Task 1: `SmtSolver` enum + `(solver: ...)` option syntax

**Files:**
- Modify: `Blaster/Command/Options.lean` (add enum + field to `BlasterOptions`)
- Modify: `Blaster/Command/Syntax.lean` (new `solveOption` syntax + parser)
- Create: `tests/Smt/SmtSolverSelection.lean` (new test module, grown across tasks)
- Modify: `tests/Smt.lean` (import the new module)

- [ ] **Step 1: Write the failing test**

Create `tests/Smt/SmtSolverSelection.lean`:

```lean
import Lean
import Blaster

/-! Tests for backend solver selection (`(solver: ...)` option) and the
    cvc5 backend. See docs/superpowers/specs/2026-07-06-cvc5-backend-design.md. -/

namespace Tests.SmtSolverSelection

-- Explicitly selecting z3 behaves exactly like the default.
#blaster (solver: z3) [∀ (x : Nat), x + 0 = x]

-- The cvc5 identifier parses (end-to-end cvc5 solving is exercised from Task 5 on).
#blaster (solver: cvc5) (only-smt-lib: 1) [∀ (x : Nat), x + 0 = x]

end Tests.SmtSolverSelection
```

Add to `tests/Smt.lean` (alphabetical position, after `import Tests.Smt.SmtRecFun`):

```lean
import Tests.Smt.SmtSolverSelection
```

- [ ] **Step 2: Run test to verify it fails**

Run: `lake build Tests.Smt.SmtSolverSelection`
Expected: FAIL — parse error on `(solver: z3)` (unknown solveOption syntax).

- [ ] **Step 3: Add the enum and option field**

In `Blaster/Command/Options.lean`, after the `isExpectedUndetermined` definition and before `structure BlasterOptions`, add:

```lean
/-- Backend SMT solver. -/
inductive SmtSolver where
  | z3
  | cvc5
deriving Repr, DecidableEq

instance : Inhabited SmtSolver where
  default := .z3
```

In `structure BlasterOptions`, after the `maxDepth` field, add:

```lean
  /-- The backend SMT solver to be used. It is set to `z3` by default. -/
  solver : SmtSolver := .z3
```

- [ ] **Step 4: Add the syntax and parser**

In `Blaster/Command/Syntax.lean`:

After `syntax "(random-seed:" num ")" : solveOption` add:

```lean
syntax "(solver:" ident ")" : solveOption
```

After `parseSolveResult` add:

```lean
def parseSolver (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (solver: $s:ident)) =>
      if s.getId == `z3 then return { sOpts with solver := .z3 }
      else if s.getId == `cvc5 then return { sOpts with solver := .cvc5 }
      else throwUnsupportedSyntax
  | _ => return sOpts
```

In `parseSolveOption`, after `let sOpts ← parseRandomSeed sOpts opt` add:

```lean
  let sOpts ← parseSolver sOpts opt
```

In the `#blaster` doc comment options list (after the `solve-result` line), add:

```lean
  - `solver`: select the backend SMT solver, `z3` or `cvc5` (default: z3)
```

Also add the same line to the options list in the `blaster` tactic doc comment in `Blaster/Command/Tactic.lean`.

- [ ] **Step 5: Run test to verify it passes**

Run: `lake build Blaster && lake build Tests.Smt.SmtSolverSelection`
Expected: PASS — module builds; first `#blaster` logs `✅ Valid`.
Note: `(solver: cvc5)` currently still runs Z3 (Env.lean is untouched); the second invocation uses `only-smt-lib: 1` so no solver runs at all. That's fine at this stage.

- [ ] **Step 6: Commit**

```bash
git add Blaster/Command/Options.lean Blaster/Command/Syntax.lean Blaster/Command/Tactic.lean tests/Smt/SmtSolverSelection.lean tests/Smt.lean
git commit -m "feat: add SmtSolver enum and (solver: ...) option syntax"
```

---

### Task 2: `SolverConfig` descriptor

**Files:**
- Create: `Blaster/Smt/SolverConfig.lean`
- Modify: `tests/Smt/SmtSolverSelection.lean` (config `#guard`s)

- [ ] **Step 1: Write the failing test**

Append to `tests/Smt/SmtSolverSelection.lean` (before `end Tests.SmtSolverSelection`):

```lean
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
#guard ((SmtSolver.cvc5).config.defaultOptions.all (fun (o, _) => !o.startsWith ":smt.")) == true

end SolverConfigChecks
```

- [ ] **Step 2: Run test to verify it fails**

Run: `lake build Tests.Smt.SmtSolverSelection`
Expected: FAIL — `unknown constant` / `invalid field 'config'`.

- [ ] **Step 3: Create `Blaster/Smt/SolverConfig.lean`**

```lean
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
```

Note the `_root_.Blaster.Options.SmtSolver.config` name: `SmtSolver` lives in
`Blaster.Options`, so dot-notation (`sOpts.solver.config`) only resolves if the
function is in the type's namespace, not in `Blaster.Smt`.

- [ ] **Step 4: Wire the module into the library**

Check whether `Blaster.lean` (or `Blaster/Smt.lean`) lists imports explicitly:

Run: `grep -n "Smt.Env\|Smt.Term" Blaster.lean Blaster/Smt.lean`

Add `import Blaster.Smt.SolverConfig` alongside the other `Blaster.Smt.*` imports in whichever file lists them (match the existing style/ordering).

- [ ] **Step 5: Run test to verify it passes**

Run: `lake build Blaster && lake build Tests.Smt.SmtSolverSelection`
Expected: PASS (all `#guard`s elaborate).

- [ ] **Step 6: Commit**

```bash
git add Blaster/Smt/SolverConfig.lean Blaster.lean Blaster/Smt.lean tests/Smt/SmtSolverSelection.lean
git commit -m "feat: add per-solver SolverConfig descriptor (z3, cvc5)"
```

---

### Task 3: `SmtCommand.getValue`

**Files:**
- Modify: `Blaster/Smt/Syntax.lean` (constructor + `toString` case)
- Modify: `Blaster/Smt/EmitCommand.lean` (emit case)
- Modify: `tests/Smt/SmtSolverSelection.lean` (toString `#guard`)

- [ ] **Step 1: Write the failing test**

Append to `tests/Smt/SmtSolverSelection.lean` (inside the file, before the final `end`):

```lean
/-! SmtCommand.getValue renders as the standard get-value command. -/
section GetValueChecks
open Blaster.Smt

#guard toString (SmtCommand.getValue (smtSimpleVarId (mkNormalSymbol "x"))) == "(get-value (x))"

end GetValueChecks
```

(`smtSimpleVarId` and `mkNormalSymbol` are existing helpers from `Blaster/Smt/Term.lean` / `Blaster/Smt/Syntax.lean`; if the names differ, check `grep -n "def smtSimpleVarId\|def mkNormalSymbol" Blaster/Smt/*.lean` and use the actual constructors.)

- [ ] **Step 2: Run test to verify it fails**

Run: `lake build Tests.Smt.SmtSolverSelection`
Expected: FAIL — `unknown constant 'Blaster.Smt.SmtCommand.getValue'`.

- [ ] **Step 3: Implement**

In `Blaster/Smt/Syntax.lean`, in `inductive SmtCommand`, after `| evalTerm (t : SmtTerm)` add:

```lean
  | getValue (t : SmtTerm)
```

In `SmtCommand.toString` (same file), after the `| .evalTerm t => s!"(eval {t})"` case add:

```lean
 | .getValue t => s!"(get-value ({t}))"
```

In `Blaster/Smt/EmitCommand.lean`, in `emitAux` after the `.evalTerm` case:

```lean
     | .getValue t =>
          h.putStr "(get-value ("
          t.emit
          h.putStr "))\n"
```

- [ ] **Step 4: Run test to verify it passes**

Run: `lake build Blaster && lake build Tests.Smt.SmtSolverSelection`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add Blaster/Smt/Syntax.lean Blaster/Smt/EmitCommand.lean tests/Smt/SmtSolverSelection.lean
git commit -m "feat: add SmtCommand.getValue (standard get-value command)"
```

---

### Task 4: Config-driven `Env.lean` (spawn, defaults, evalTerm)

This task refactors the solver interface while keeping the Z3 stream
byte-identical. Capture a Z3 baseline BEFORE touching anything.

**Files:**
- Modify: `Blaster/Smt/Env.lean`
- Modify: `tests/Smt/SmtSolverSelection.lean` (unwrap `#guard`s)

- [ ] **Step 1: Capture the pre-refactor Z3 command-stream baseline**

Create a scratch file `/tmp/baseline.lean` (outside the repo):

```lean
import Lean
import Blaster
#blaster (dump-smt-lib: 1) [∀ (x : Nat) (y : Nat), x + y ≥ x]
```

Run: `lake env lean /tmp/baseline.lean > /tmp/dump_before.txt 2>&1; cat /tmp/dump_before.txt`
Expected: output containing the full SMT command dump (starts with `(set-option :print-success true)`) and `✅ Valid`. Keep `/tmp/dump_before.txt`.

- [ ] **Step 2: Write the failing unwrap test**

Append to `tests/Smt/SmtSolverSelection.lean`:

```lean
/-! get-value response unwrapping (shapes verified against cvc5 1.2.1). -/
section UnwrapChecks
open Blaster.Smt

#guard unwrapGetValue "((x 4))\n" == "4\n"
#guard unwrapGetValue "(($5 (- 4)))\n" == "(- 4)\n"
#guard unwrapGetValue "((r Idle))\n" == "Idle\n"
#guard unwrapGetValue "((p (mk (- 7) 0)))\n" == "(mk (- 7) 0)\n"

end UnwrapChecks
```

Run: `lake build Tests.Smt.SmtSolverSelection`
Expected: FAIL — `unknown constant 'Blaster.Smt.unwrapGetValue'`.

- [ ] **Step 3: Refactor `Blaster/Smt/Env.lean`**

Add `import Blaster.Smt.SolverConfig` to the imports at the top.

Delete `private def minZ3Version` (line ~16) — superseded by `SolverConfig.minVersion`.

Replace `findZ3CmdAndVersion` (lines ~80–101) with:

```lean
/-- Tries to find the backend solver binary among `cfg.candidates`:
    natively in PATH first, then through WSL. -/
private def findSolverCmd (cfg : SolverConfig) : IO String := do
  -- We'll store a short log message for each candidate attempt
  let mut attemptLogs := #[]
  for candidate in cfg.candidates do
    try
      let out ← IO.Process.output { cmd := candidate, args := #[cfg.versionFlag] }
      if out.exitCode == 0 then
        -- Found a good candidate => Return immediately
        return candidate
      else
        attemptLogs := attemptLogs.push
          s!"Candidate '{candidate}': exit code {out.exitCode}"
    catch e =>
      -- “No such file or directory” or other IO error
      attemptLogs := attemptLogs.push
        s!"Candidate '{candidate}': IO error => {e}"

  -- If we get here, no candidate succeeded
  let attemptsReport := String.join (attemptLogs.toList.map (fun x => x ++ "\n"))
  throw <| IO.userError s!"❌ Could not find a working {cfg.displayName} ≥ {cfg.minVersion}.\n\nTried:\n{attemptsReport}"
```

Replace `createBlasterProcess` (lines ~104–113) with:

```lean
/-- Spawn the backend solver process described by `cfg`. -/
def createBlasterProcess (cfg : SolverConfig) : IO (IO.Process.Child ⟨.piped, .piped, .piped⟩) := do
  let solverCmd ← findSolverCmd cfg  -- ensures the binary is present
  IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := solverCmd
    args   := cfg.spawnArgs
  }
```

Replace `evalTerm` (lines ~486–491) with (keep its doc comment, adding the note about get-value):

```lean
/-- Unwrap a `(get-value (t))` response of shape `((t value))` and return the
    bare value string followed by a newline — the same shape Z3's `(eval t)`
    produces, so downstream counterexample rendering is solver-independent.
    Assumes the queried term is a single symbol (which holds for the only
    caller, `getModel.getVarValue`; SMT symbols never contain spaces). -/
def unwrapGetValue (s : String) : String :=
  let inner := ((s.trim.drop 2).dropRight 2).trim
  let val := match inner.splitOn " " with
    | [] => inner
    | _ :: rest => String.intercalate " " rest
  val.trim ++ "\n"

def evalTerm (t : SmtTerm) : TranslateEnvT String := do
  let env ← get
  let some p := env.smtEnv.smtProc | return ""
  checkCancelTk?
  if env.optEnv.options.solverOptions.solver.config.usesGetValue then
    submitCommand (.getValue t)
    return unwrapGetValue (← getOutputEval p.stdout)
  else
    submitCommand (.evalTerm t)
    getOutputEval p.stdout
```

(`evalTerm`'s existing doc comment about TODO/parsing stays on `evalTerm`.)

Replace `setRandomSeed`, `setTimeout`, `setDefaultSmtOptions`, `setBlasterProcess` (lines ~619–691) with:

```lean
/-- Set the Smt random seed option (solver-specific option name) to `n` or none. -/
def setRandomSeed (cfg : SolverConfig) (n : Option Nat) : TranslateEnvT Unit := do
  match n with
  | some n => trySubmitCommand! (.setOption cfg.seedOption (toString n))
  | none => pure ()

/-- Set the Smt timeout (solver-specific option name, in milliseconds)
    when the option is specified. -/
def setTimeout (cfg : SolverConfig) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let some n := sOpts.timeout | return ()
  -- need to convert timeout to milliseconds
  trySubmitCommand! (.setOption cfg.timeoutOption (toString (n * 1000)))

/-- Set the default Smt options of the selected backend solver, i.e. the
    solver's `SolverConfig.defaultOptions` pairs in order, followed by the
    random seed and timeout when provided in the solver options. -/
def setDefaultSmtOptions (sOpts : BlasterOptions) : TranslateEnvT Unit := do
  let cfg := sOpts.solver.config
  for (opt, val) in cfg.defaultOptions do
    trySubmitCommand! (.setOption opt val)
  setRandomSeed cfg sOpts.randomSeed
  setTimeout cfg

/-- Perform the following actions:
     - when option `only-smt-lib` is set to `false`:
       - Spawn the backend solver process and update TranslateEnv
       - set the default smt solver options by emitting the corresponding commands
     - when option `only-smt-lib` is set to `true`:
       - only add the solver options to the list of smt commands.
-/
def setBlasterProcess : TranslateEnvT Unit := do
  let env ← get
  let sOpts := env.optEnv.options.solverOptions
  unless sOpts.onlySmtLib do
    let proc ← createBlasterProcess sOpts.solver.config
    set { env with smtEnv.smtProc := proc }
  setDefaultSmtOptions sOpts
```

- [ ] **Step 4: Remove the now-dead per-option helpers (after verifying they're unused)**

Run: `grep -rn "setPrintSuccess\|setProduceModels\|setProduceProofs\|setMbqi\|setPullNestedQuantifiers\|setAutoConfig\|setMacroFinder" Blaster tests --include="*.lean" | grep -v "Blaster/Smt/Env.lean"`

Expected: no output (only definitions + `setDefaultSmtOptions` used them). If no output, delete the definitions of `setPrintSuccess`, `setProduceModels`, `setProduceProofs`, `setMbqi`, `setPullNestedQuantifiers`, `setAutoConfig`, `setMacroFinder` from `Env.lean` (their spellings now live in `z3Config.defaultOptions`). If there IS output, keep whichever helper is referenced and note it in the commit message.

Keep `setLogicAll`, `setCaseSplit`, `setQiEagerThreshold`, `setDelayUnits`, `setRelevancy` untouched (spec: Z3-only maintainer knobs, not abstracted).

- [ ] **Step 5: Verify build + unwrap guards + Z3 stream unchanged**

Run: `lake build Blaster && lake build Tests.Smt.SmtSolverSelection`
Expected: PASS.

Run: `lake env lean /tmp/baseline.lean > /tmp/dump_after.txt 2>&1; diff /tmp/dump_before.txt /tmp/dump_after.txt && echo Z3-STREAM-IDENTICAL`
Expected: `Z3-STREAM-IDENTICAL` (empty diff).

- [ ] **Step 6: Run a broader Z3 regression slice**

Run: `lake build Tests.FixedIssues Tests.StateMachine`
Expected: PASS (no new errors; pre-existing warnings are fine).

- [ ] **Step 7: Commit**

```bash
git add Blaster/Smt/Env.lean tests/Smt/SmtSolverSelection.lean
git commit -m "feat: config-driven solver process, options and model-value query"
```

---

### Task 5: cvc5 end-to-end tests

**Files:**
- Modify: `tests/Smt/SmtSolverSelection.lean`

- [ ] **Step 1: Add end-to-end cvc5 tests (they should now pass directly — write, then verify)**

Append to `tests/Smt/SmtSolverSelection.lean`:

```lean
/-! End-to-end cvc5 solving. -/
section Cvc5EndToEnd

-- Valid goal proved by cvc5 (unsat internally).
#blaster (solver: cvc5) [∀ (x : Nat) (y : Nat), x + y ≥ x]

-- Falsified goal: cvc5 produces a model through (get-model).
#blaster (solver: cvc5) (solve-result: 1) [∀ (x : Int), x < 0]

-- Falsified without counterexample generation.
#blaster (solver: cvc5) (solve-result: 1) (gen-cex: 0) [∀ (x : Int), x < 0]

-- Timeout option maps to :tlimit-per for cvc5.
#blaster (solver: cvc5) (timeout: 10) [∀ (x : Nat), x * 1 = x]

-- Random seed maps to :seed for cvc5.
#blaster (solver: cvc5) (random-seed: 42) [∀ (x : Nat), x + 1 > x]

-- The blaster tactic accepts the solver option too.
example : ∀ (x : Nat) (y : Nat), x + y ≥ x := by blaster (solver: cvc5)

end Cvc5EndToEnd
```

- [ ] **Step 2: Run and inspect**

Run: `lake build Tests.Smt.SmtSolverSelection`
Expected: PASS with `✅ Valid` / `✅ Expected Falsified` logs and no errors.

If the falsified cases error with an unexpected check-sat/model issue, debug
with `(dump-smt-lib: 1)` on the failing invocation and compare with piping the
dumped query to `cvc5 --incremental` manually. Do NOT weaken the test.

Note: the `evalTerm`/`get-value` path only triggers for state machines
(top-level vars); plain `#blaster` counterexamples go through `(get-model)`.
That path is covered in Task 8 by adding `#bmc`/`#kind` `(solver: cvc5)`
siblings to the existing Counter04–06 machines — `#bmc` and `#kind` accept
the option automatically since they share the `solveOption` syntax category.
No new state machine or test file is needed here.

- [ ] **Step 3: Commit**

```bash
git add tests/Smt/SmtSolverSelection.lean
git commit -m "test: cvc5 end-to-end coverage"
```

---

### Task 6: `cvc5check` executable

**Files:**
- Create: `Cvc5Check.lean`
- Modify: `lakefile.lean`

- [ ] **Step 1: Create `Cvc5Check.lean`** (mirrors `Z3Check.lean`)

```lean
/-
  This program checks if the cvc5 SMT solver is installed correctly
  and prints its version.

  To run this program, ensure that cvc5 is installed and accessible
  from your system's PATH; then, compile and execute this Lean code
  as follows:

     lake build cvc5check
     lake exe cvc5check

  If cvc5 is installed correctly, you will see

     Successfully ran cvc5:
     This is cvc5 version 1.2.1 [...]

  otherwise, it will print an error message.
-/

import Lean

open IO

def main : IO Unit := do
  let proc ← IO.Process.output { cmd := "cvc5", args := #["--version"] }
  if proc.exitCode == 0 then
    IO.println "Successfully ran cvc5:"
    IO.println proc.stdout
  else
    IO.eprintln "Failed to run cvc5:"
    IO.eprintln proc.stderr
```

- [ ] **Step 2: Register the executable in `lakefile.lean`** (after the `z3check` block)

```lean
lean_exe cvc5check where
  -- add executable configuration options here
  root := `Cvc5Check
```

- [ ] **Step 3: Verify**

Run: `lake build cvc5check && lake exe cvc5check`
Expected: `Successfully ran cvc5:` followed by the version line.

- [ ] **Step 4: Commit**

```bash
git add Cvc5Check.lean lakefile.lean
git commit -m "feat: add cvc5check executable"
```

---

### Task 7: Test-duplication script + bulk sibling generation

**Files:**
- Create: `scripts/add_cvc5_siblings.py`
- Modify: most files under `tests/` (script-generated)

- [ ] **Step 1: Create `scripts/add_cvc5_siblings.py`**

```python
#!/usr/bin/env python3
"""Add a `(solver: cvc5)` sibling after every backend-reaching test invocation.

For each `#blaster` / `#bmc` / `#kind` invocation under the given roots:
  - skip when its options contain `only-smt-lib: 1`, `only-optimize: 1`,
    or an explicit `solver:` (no backend reached / already covered);
  - skip when the invocation is wrapped in `#guard_msgs` (its expected
    messages are Z3 baselines — handled manually);
  - otherwise, duplicate the whole invocation right below it, inserting
    `(solver: cvc5)` after the command keyword.

Usage: python3 scripts/add_cvc5_siblings.py [--dry-run] [roots...]
"""
import re
import sys
import pathlib

CMD = re.compile(r'^(\s*)#(blaster|bmc|kind)\b')


def find_invocation_end(lines, i):
    """Index (inclusive) of the line closing the invocation's `[...]` term."""
    depth = 0
    seen_open = False
    for j in range(i, len(lines)):
        for ch in lines[j]:
            if ch == '[':
                depth += 1
                seen_open = True
            elif ch == ']':
                depth -= 1
        if seen_open and depth <= 0:
            return j
    raise ValueError(f"unbalanced brackets from line {i + 1}")


def process(path, dry):
    lines = path.read_text(encoding='utf-8').splitlines(keepends=True)
    out, i, changed = [], 0, 0
    while i < len(lines):
        line = lines[i]
        m = CMD.match(line)
        prev = out[-1].strip() if out else ''
        if not m or prev.startswith('#guard_msgs'):
            out.append(line)
            i += 1
            continue
        j = find_invocation_end(lines, i)
        block = lines[i:j + 1]
        text = ''.join(block)
        out.extend(block)
        if ('only-smt-lib: 1' not in text and 'only-optimize: 1' not in text
                and 'solver:' not in text):
            sib = text.replace(f'#{m.group(2)}', f'#{m.group(2)} (solver: cvc5)', 1)
            if not sib.endswith('\n'):
                sib += '\n'
            out.append(sib)
            changed += 1
        i = j + 1
    if changed and not dry:
        path.write_text(''.join(out), encoding='utf-8')
    return changed


def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    roots = [a for a in args if not a.startswith('--')] or ['tests']
    total = 0
    for root in roots:
        for p in sorted(pathlib.Path(root).rglob('*.lean')):
            n = process(p, dry)
            if n:
                print(f'{p}: {n} sibling(s)')
                total += n
    print(f'total: {total} sibling(s){" (dry run)" if dry else ""}')


if __name__ == '__main__':
    main()
```

- [ ] **Step 2: Dry-run and sanity-check**

Run: `python3 scripts/add_cvc5_siblings.py --dry-run tests`
Expected: per-file sibling counts; total roughly 450–520 (≈706 `#blaster` + 20 `#bmc/#kind` lines, minus ~220 `only-smt-lib/only-optimize` invocations, minus guard-wrapped and already-`solver:` ones, minus comment lines). Spot-check 2–3 listed files mentally against the skip rules.

Exclude `tests/Smt/SmtSolverSelection.lean` from concern — its invocations already carry `solver:` and are skipped automatically.

- [ ] **Step 3: Apply**

Run: `python3 scripts/add_cvc5_siblings.py tests`
Then: `git diff --stat | tail -5` to see the scale, and `git diff tests/FixedIssues/Issue1.lean | head -40` to eyeball one file: each sibling must read `#blaster (solver: cvc5) ...` immediately after its original, with identical options and term.

- [ ] **Step 4: Compile a fast subset before the big build**

Run: `lake build Tests.FixedIssues.Issue1 Tests.Smt.SmtNat`
Expected: PASS. If a file fails to parse, the script mis-handled an invocation shape — fix the file by hand AND fix the script, re-run from a clean tree (`git checkout -- tests && python3 ...`).

- [ ] **Step 5: Commit the script and the bulk edit**

```bash
git add scripts/add_cvc5_siblings.py tests
git commit -m "test: add (solver: cvc5) sibling invocations across the suite"
```

(Committing before the full-suite run is intentional: Task 9's re-baselining
edits are then reviewable as focused diffs on top of the mechanical bulk.)

---

### Task 8: Manual sibling sites (tactic uses, guard_msgs files)

**Files:**
- Modify: the 11 files/sites found by `grep -rn "by blaster" tests --include="*.lean"`
- Modify: `tests/StateMachine/Counter04.lean`, `Counter05.lean`, `Counter06.lean`
- Modify (comment only): `tests/FixedIssues/Issue8.lean`

- [ ] **Step 1: Duplicate the `by blaster` tactic sites**

Run: `grep -rn "by blaster" tests --include="*.lean"`

For each of the 11 sites: duplicate the enclosing theorem/example directly
below, rename (`<name>_cvc5`, or keep `example` anonymous), and change the
tactic to `by blaster (solver: cvc5)` (preserving any existing options).
Example transformation:

```lean
theorem thm5 : ∀ (f : FunRelThree) (x y : Nat), f.f x ≤ f.f y → f.f y ≤ f.f x → f.f y = f.f x := by blaster

theorem thm5_cvc5 : ∀ (f : FunRelThree) (x y : Nat), f.f x ≤ f.f y → f.f y ≤ f.f x → f.f y = f.f x := by blaster (solver: cvc5)
```

IMPORTANT: if cvc5 cannot prove one of these goals, the tactic leaves an
unsolved goal and the file fails to build. In that case remove that sibling and
leave a comment: `-- cvc5 (1.2.1) cannot prove this goal — sibling omitted`.

- [ ] **Step 2: Baseline cvc5 siblings for Counter04–06**

For each of `tests/StateMachine/Counter04.lean`, `Counter05.lean`,
`Counter06.lean`: after each `#guard_msgs in #bmc ...` / `#guard_msgs in
#kind ...` block, add a cvc5 sibling with an empty expectation:

```lean
/--  -/
#guard_msgs in
#bmc (solver: cvc5) (max-depth: 6) [counter]
```

Run: `lake build Tests.StateMachine.Counter04 Tests.StateMachine.Counter05 Tests.StateMachine.Counter06`
Expected: FAIL — each new guard reports the actual cvc5 messages.

Paste each actual message block into its doc comment verbatim, re-run, expect
PASS. Sanity-check pasted values are bare (`2`, `Request.Idle`), not
`((… …))`-wrapped.

- [ ] **Step 3: Document the Issue8 skip**

In `tests/FixedIssues/Issue8.lean`, add one comment near the top:

```lean
-- NOTE: no (solver: cvc5) siblings here — both invocations fail during
-- translation (ill-formed formulae) and never reach a backend solver.
```

- [ ] **Step 4: Verify the touched files build**

Run: `lake build Tests.StateMachine.Counter04 Tests.StateMachine.Counter05 Tests.StateMachine.Counter06 Tests.FixedIssues.Issue8` plus each module edited in Step 1.
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add tests
git commit -m "test: cvc5 siblings for tactic uses and state-machine guard baselines"
```

---

### Task 9: Full-suite run under both solvers + re-baselining

**Files:**
- Modify: individual `tests/**.lean` cvc5 siblings as dictated by results
- Possibly modify: `Blaster/Smt/SolverConfig.lean` (cvc5 `defaultOptions` tuning)

- [ ] **Step 1: Run the full suite**

Run: `LEAN_NUM_THREADS=5 lake test 2>&1 | tee /tmp/suite_run.log`

This is slow (hundreds of solver calls). If an invocation HANGS (build stalls
on one module for minutes), identify the module, add `(timeout: 10)` to the
offending cvc5 sibling, and re-run. `full-saturate-quant` can loop on
satisfiable quantified goals, so hangs are most likely on siblings of
`solve-result: 2` (expected-Undetermined) tests — check those first.

- [ ] **Step 2: Triage failures with these decision rules**

Scan `/tmp/suite_run.log` for `error:` lines. For each failing cvc5 sibling:

1. **`❌ Unexpected Valid`** (Z3 original expects `solve-result: 2`): cvc5
   proved what Z3 couldn't. Change the sibling's option to `(solve-result: 0)`
   with comment `-- cvc5 proves this (z3: undetermined)`.
2. **`❌ Falsified` where the original expects Valid**: STOP — this is a
   potential soundness/translation incompatibility, not a baseline issue.
   Reproduce with `(dump-smt-lib: 1)`, pipe the dump to `cvc5 --incremental`
   manually, and diagnose (use superpowers:systematic-debugging). Do not
   re-baseline; fix the translation/config.
3. **`⚠️ Undetermined` where the original expects Valid**: this is a warning,
   not an error — the suite still passes. Leave the sibling as-is (it
   documents cvc5's current capability and auto-upgrades if cvc5 improves).
4. **Unexpected smt error `unsupported`/`(error ...)`**: a command cvc5
   rejects reached it. Diagnose via `(dump-smt-lib: 1)`; fix in
   `SolverConfig`/translation, not in the test.
5. **Tactic sibling fails with unsolved goals**: remove that sibling with the
   `-- cvc5 (1.2.1) cannot prove this goal` comment (per Task 8 Step 1).
6. **Hang**: add `(timeout: 10)` to the sibling (10s → `:tlimit-per 10000`).

If MANY siblings return Undetermined on goals Z3 proves, try strengthening
`cvc5Config.defaultOptions` (e.g. add `(":finite-model-find", "true")` or
adjust `:full-saturate-quant`) — one config change, then re-run, rather than
annotating dozens of tests. Keep the config minimal; prefer 1–5 targeted test
annotations over a risky global option.

- [ ] **Step 3: Iterate to green**

Repeat Steps 1–2 until: `LEAN_NUM_THREADS=5 lake test` exits 0.
Then run the CI-equivalent check: `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests`
Expected: exits 0.

- [ ] **Step 4: Commit**

```bash
git add tests Blaster/Smt/SolverConfig.lean
git commit -m "test: re-baseline cvc5 sibling expectations across the suite"
```

---

### Task 10: CI + README

**Files:**
- Modify: `.github/workflows/ci-linux.yaml`
- Modify: `README.md`

- [ ] **Step 1: Verify the cvc5 release asset URL**

Run: `curl -sIL https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip | head -1`
Expected: `HTTP/2 200`. If 404, list assets with
`curl -s https://api.github.com/repos/cvc5/cvc5/releases/tags/cvc5-1.2.1 | grep browser_download_url`
and use the Linux x86_64 static zip asset name found there.

- [ ] **Step 2: Edit `.github/workflows/ci-linux.yaml`**

In the `env:` block add:

```yaml
  CVC5_VERSION: "1.2.1"
```

After the `Install Z3` step add:

```yaml
      - name: Install cvc5
        run: |
          cd /home/runner/
          wget -q https://github.com/cvc5/cvc5/releases/download/cvc5-${{ env.CVC5_VERSION }}/cvc5-Linux-x86_64-static.zip
          unzip -q cvc5-Linux-x86_64-static.zip
          chmod +x cvc5-Linux-x86_64-static/bin/cvc5
          echo "/home/runner/cvc5-Linux-x86_64-static/bin" >> $GITHUB_PATH
```

In the `Tools version` step, add a line:

```yaml
          cvc5 --version
```

- [ ] **Step 3: Sanity-check the workflow install commands locally**

Run (in a scratch dir, not the repo):

```bash
cd /tmp && wget -q https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip && unzip -l cvc5-Linux-x86_64-static.zip | grep "bin/cvc5"
```

Expected: the archive contains `cvc5-Linux-x86_64-static/bin/cvc5` (this
validates the `$GITHUB_PATH` line). Clean up the download afterwards.

- [ ] **Step 4: Update `README.md`**

- In the "Solver options" section, add a row/bullet documenting
  `solver`: `select the backend SMT solver, z3 or cvc5 (default: z3)`,
  matching the surrounding format.
- Add a short "Installing cvc5" subsection next to "Installing Z3":
  currently tested version 1.2.1, install from
  https://github.com/cvc5/cvc5/releases (or `brew install cvc5` /
  the Linux release zip), verify with `lake exe cvc5check`.
- Mention in the prerequisites list: `cvc5 v1.2.1 (optional — only needed
  when using (solver: cvc5))`.

- [ ] **Step 5: Commit**

```bash
git add .github/workflows/ci-linux.yaml README.md
git commit -m "ci,docs: install cvc5 in CI and document the solver option"
```

---

### Task 11: Final verification

- [ ] **Step 1: Clean full build + test**

Run: `lake clean && lake build Blaster && LEAN_NUM_THREADS=5 lake test`
Expected: exit 0.

- [ ] **Step 2: CI-equivalent script checks**

Run: `./scripts/check_lean_project_compilation.sh Blaster && LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests`
Expected: both exit 0.

- [ ] **Step 3: Verify the executables**

Run: `lake exe z3check && lake exe cvc5check`
Expected: both print their success line.

- [ ] **Step 4: Invoke superpowers:verification-before-completion, then superpowers:finishing-a-development-branch**

Confirm all evidence above before claiming completion; then decide merge/PR
handling for `feat/cvc5` with the user.
