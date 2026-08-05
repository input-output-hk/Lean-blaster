# Optimizer Growth Telemetry (`stats-file`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Opt-in JSONL telemetry recording optimizer cache growth per stack step, so issue #138's exponential residual can be attributed to a specific structure.

**Architecture:** A `stats : OptimizeStats` record in `TranslateEnv` state; `optimizeExprAux` bumps a step counter and every `interval` steps appends one flushed JSON line with all O(1) cache sizes; command entry points wrap their pipeline in `withOptimizeStats` (init → run → finalize). Two new solve options (`stats-file`, `stats-interval`) ride `BlasterOptions`.

**Tech Stack:** Lean 4.24 (`StateRefT` state monad, `Lean.Data.Json`, `IO.FS.Handle`, `IO.monoMsNow`). Spec: `docs/superpowers/specs/2026-08-05-optimizer-stats-design.md`.

**Branch:** `feat/issue138-optimizer-stats` (already created; spec committed). The working tree also carries UNRELATED uncommitted changes (`Blaster/Smt/Env.lean`, `Z3Check.lean`, `Tests/Smt/SmtNat/SmtNatMod.lean`, `Tests/StateMachine/Counter06.lean`, `nat_mod.smt2` — Z3 5.0.0 evaluation leftovers). NEVER `git add` those files or `git add -A`; stage each file explicitly.

---

### Task 1: Data structures — `BlasterOptions` fields, `OptimizeStats`, `TranslateEnv.stats`

**Files:**
- Modify: `Blaster/Command/Options.lean` (structure `BlasterOptions`, ends line ~74)
- Modify: `Blaster/Optimize/Env.lean` (insert before `structure TranslateEnv` at line ~467; update the `Inhabited TranslateEnv` instance at ~473)

- [ ] **Step 1: Add the two option fields to `BlasterOptions`**

In `Blaster/Command/Options.lean`, inside `structure BlasterOptions where`, after the `maxDepth` field (line ~73, before ` deriving Repr`), add:

```lean
  /-- When set, write optimizer growth telemetry as JSON-lines to this file.
      One `sample` event is emitted every `statsInterval` optimizer stack steps
      (see `Blaster/Optimize/Stats.lean` and
      docs/superpowers/specs/2026-08-05-optimizer-stats-design.md).
      It is set to `none` by default (i.e., telemetry disabled). -/
  statsFile : Option String := none

  /-- Number of optimizer stack steps between two telemetry samples.
      Only meaningful when `statsFile` is set. Values below 1 are clamped to 1. -/
  statsInterval : Nat := 100000
```

Note: `BlasterOptions` derives `Repr`; `Option String` and `Nat` both have `Repr`, so no change needed there.

- [ ] **Step 2: Add `OptimizeStats` to `Blaster/Optimize/Env.lean`**

Insert immediately BEFORE `/-- Type defining the environment used when optimizing a lean theorem and translating to Smt-lib. -/` (the `TranslateEnv` doc comment, line ~466):

```lean
/-- Runtime state for optimizer growth telemetry (issue #138).
    Disabled (`handle = none`) unless the `stats-file` solve option is set.
    Operations live in `Blaster/Optimize/Stats.lean`. -/
structure OptimizeStats where
  /-- JSONL sink. `none` means telemetry is disabled (the default). -/
  handle : Option IO.FS.Handle := none
  /-- Optimizer stack steps between two samples. -/
  interval : Nat := 100000
  /-- Number of `optimizeExprAux` iterations so far. -/
  steps : Nat := 0
  /-- Step count at which the next sample fires. -/
  nextSampleAt : Nat := 100000
  /-- `IO.monoMsNow` reading at `initStats` time. -/
  startMs : Nat := 0
  /-- Number of `sample` events written so far. -/
  samples : Nat := 0

instance : Inhabited OptimizeStats where
  default := {}
```

- [ ] **Step 3: Add the `stats` field to `TranslateEnv` and its `Inhabited` instance**

Change (line ~467):

```lean
structure TranslateEnv where
  /-- Environment used when translating to Smt-ling. -/
  smtEnv : SmtEnv
  /-- Environment used when optimization a lean expression. -/
  optEnv : OptimizeEnv

instance : Inhabited TranslateEnv where
  default :=
    { smtEnv := default,
      optEnv := default
    }
```

to:

```lean
structure TranslateEnv where
  /-- Environment used when translating to Smt-ling. -/
  smtEnv : SmtEnv
  /-- Environment used when optimization a lean expression. -/
  optEnv : OptimizeEnv
  /-- Optimizer growth telemetry state (see note on OptimizeStats). -/
  stats : OptimizeStats

instance : Inhabited TranslateEnv where
  default :=
    { smtEnv := default,
      optEnv := default,
      stats := default
    }
```

- [ ] **Step 4: Build**

Run: `lake build Blaster`
Expected: `Build completed successfully`. (All existing `{(default : TranslateEnv) with ...}` constructions still work — the new field has a default.)

- [ ] **Step 5: Commit**

```bash
git add Blaster/Command/Options.lean Blaster/Optimize/Env.lean
git commit -m "feat: OptimizeStats state and stats-file/stats-interval options (#138)"
```

---

### Task 2: `Blaster/Optimize/Stats.lean` — init / bump / sample / finalize

**Files:**
- Create: `Blaster/Optimize/Stats.lean`
- Modify: `Blaster/Optimize.lean` (aggregate import list)

- [ ] **Step 1: Create `Blaster/Optimize/Stats.lean` with this exact content**

```lean
import Lean
import Blaster.Optimize.Env

open Lean

namespace Blaster.Optimize

/-! # Optimizer growth telemetry (issue #138)

Opt-in JSONL recording of optimizer cache sizes over stack steps, enabled by
the `stats-file` solve option. Design:
docs/superpowers/specs/2026-08-05-optimizer-stats-design.md

Events (one JSON object per line, flushed per line so killed runs stay analyzable):
 - `{"ev":"start", "schema":1, "unfoldDepth":…, "maxDepth":…, "interval":…}`
 - `{"ev":"sample", "steps":…, "ms":…, "mcDepth":…, "<cache>":<size>, …}`
 - `{"ev":"end", "steps":…, "ms":…, "samples":…}`
-/

/-- Sizes of all tracked optimizer caches. All reads are O(1).
    `Name`-keyed memoization caches are bounded by program size and reported
    as one aggregate (`memNamed`); `Expr`-keyed ones are reported individually. -/
def cacheSizes (env : TranslateEnv) : List (String × Nat) :=
  let o := env.optEnv
  let m := o.memCache
  [ ("globalRewrite",  o.globalRewriteCache.size),
    ("localRewrite",   o.localRewriteCache.size),
    ("synthInstance",  o.synthInstanceCache.size),
    ("whnf",           o.whnfCache.size),
    ("match",          o.matchCache.size),
    ("recFunInst",     o.recFunInstCache.size),
    ("recFun",         o.recFunCache.size),
    ("recFunMap",      o.recFunMap.size),
    ("hypMap",         o.hypothesisContext.hypothesisMap.size),
    ("eqMap",          o.hypothesisContext.equalityMap.size),
    ("matchInCtx",     o.matchInContext.size),
    ("inferType",      m.inferTypeCache.size),
    ("isProp",         m.isPropCache.size),
    ("getFunBody",     m.getFunBodyCache.size),
    ("isResolvable",   m.isResolvableCache.size),
    ("isType",         m.isTypeCache.size),
    ("isNotFun",       m.isNotFunCache.size),
    ("isCstMatchProp", m.isCstMatchPropCache.size),
    ("getFunEnvInfo",  m.getFunEnvInfoCache.size),
    ("memNamed",       m.isRecFunCache.size + m.isInstanceCache.size
                       + m.isClassCache.size + m.isInductiveCache.size
                       + m.getMatcherCache.size + m.getConstInfoCache.size
                       + m.isMatcherCache.size + m.isPartialCache.size
                       + m.isMatchToIte.size) ]

private def writeEvent (h : IO.FS.Handle) (fields : List (String × Json)) : IO Unit := do
  h.putStr ((Json.mkObj fields).compress ++ "\n")
  h.flush

/-- Emit one `sample` event. A write failure disables telemetry silently
    (no error spam at sample cadence). -/
def sampleStats : TranslateEnvT Unit := do
  let env ← get
  let some h := env.stats.handle | return ()
  let now ← IO.monoMsNow
  let fields :=
    [ ("ev", Json.str "sample"),
      ("steps", toJson env.stats.steps),
      ("ms", toJson (now - env.stats.startMs)),
      ("mcDepth", toJson env.optEnv.options.mcDepth) ]
    ++ (cacheSizes env).map (fun (n, v) => (n, toJson v))
  try
    writeEvent h fields
    modify fun e => { e with stats.samples := e.stats.samples + 1 }
  catch _ =>
    modify fun e => { e with stats.handle := none }

/-- Count one optimizer stack step; emit a sample every `interval` steps.
    Disabled path (the default): a single `Option` check. -/
@[always_inline, inline]
def bumpStatsAndMaybeSample : TranslateEnvT Unit := do
  let s := (← get).stats
  if s.handle.isSome then
    let steps := s.steps + 1
    if steps ≥ s.nextSampleAt then
      modify fun e => { e with stats.steps := steps, stats.nextSampleAt := steps + s.interval }
      sampleStats
    else
      modify fun e => { e with stats.steps := steps }

/-- Open the stats file and write the `start` event when `stats-file` is set.
    Open failure logs a warning and leaves telemetry disabled — it never
    fails the solve. -/
def initStats : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let some path := sOpts.statsFile | return ()
  let interval := max 1 sOpts.statsInterval
  try
    let h ← IO.FS.Handle.mk path .write
    writeEvent h
      [ ("ev", Json.str "start"),
        ("schema", toJson (1 : Nat)),
        ("unfoldDepth", toJson sOpts.unfoldDepth),
        ("maxDepth", toJson sOpts.maxDepth),
        ("interval", toJson interval) ]
    let now ← IO.monoMsNow
    modify fun e =>
      { e with stats := { handle := some h, interval, steps := 0,
                          nextSampleAt := interval, startMs := now, samples := 0 } }
  catch ex =>
    logWarning m!"stats-file: could not open '{path}' ({ex.toMessageData}); telemetry disabled"

/-- Emit the `end` event and drop the handle. At `verbose ≥ 1`, log a human
    summary (total steps, elapsed, top-8 caches by final size). -/
def finalizeStats : TranslateEnvT Unit := do
  let env ← get
  let some h := env.stats.handle | return ()
  let now ← IO.monoMsNow
  try
    writeEvent h
      [ ("ev", Json.str "end"),
        ("steps", toJson env.stats.steps),
        ("ms", toJson (now - env.stats.startMs)),
        ("samples", toJson env.stats.samples) ]
  catch _ => pure ()
  modify fun e => { e with stats.handle := none }
  if env.optEnv.options.solverOptions.verbose ≥ 1 then
    let top := ((cacheSizes env).toArray.qsort (fun a b => a.2 > b.2)).extract 0 8
    let lines := top.toList.map (fun (n, v) => s!"  {n}: {v}")
    logInfo m!"optimizer stats: {env.stats.steps} steps, {now - env.stats.startMs} ms\n{String.intercalate "\n" lines}"

/-- Run `act` with telemetry initialized before and finalized after (when the
    `stats-file` option is set; otherwise both hooks are no-ops). -/
def withOptimizeStats (act : TranslateEnvT α) : TranslateEnvT α := do
  initStats
  try act finally finalizeStats

end Blaster.Optimize
```

- [ ] **Step 2: Register the module in the aggregate import**

Open `Blaster/Optimize.lean`; it is a list of `import Blaster.Optimize.*` lines. Add, keeping alphabetical order:

```lean
import Blaster.Optimize.Stats
```

- [ ] **Step 3: Build**

Run: `lake build Blaster`
Expected: `Build completed successfully`. If `ex.toMessageData` fails to elaborate (Exception message API drift), use `logWarning m!"stats-file: could not open '{path}'; telemetry disabled"` (drop the reason) — the test in Task 5 only asserts the `stats-file: could not open` prefix behavior, not the reason text.

- [ ] **Step 4: Commit**

```bash
git add Blaster/Optimize/Stats.lean Blaster/Optimize.lean
git commit -m "feat: optimizer growth telemetry module (init/bump/sample/finalize) (#138)"
```

---

### Task 3: Hook the counter into `optimizeExprAux` and wrap the four entry points

**Files:**
- Modify: `Blaster/Optimize/Basic.lean:16` (loop hook) and `:305-312` (`Optimize.command`), plus its import list (line ~1-8)
- Modify: `Blaster/Smt/Translate.lean:90-94` (`Smt.command`)
- Modify: `Blaster/StateMachine/BMC.lean:101-104` (`bmcCommand`)
- Modify: `Blaster/StateMachine/KInduction.lean:158-161` (`kIndCommand`)

- [ ] **Step 1: Import Stats in `Blaster/Optimize/Basic.lean`**

Add to the import block at the top (after `import Blaster.Optimize.Rewriting.OptimizeForAll`):

```lean
import Blaster.Optimize.Stats
```

- [ ] **Step 2: Bump at the top of the loop**

In `Blaster/Optimize/Basic.lean:16`, change:

```lean
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT Expr := do
  match stack with
```

to:

```lean
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT Expr := do
  bumpStatsAndMaybeSample
  match stack with
```

- [ ] **Step 3: Wrap `Optimize.command` (test entry point)**

In `Blaster/Optimize/Basic.lean:305-312`, change the line

```lean
  let res ← Optimize.main e|>.run env
```

to:

```lean
  let res ← (withOptimizeStats <| Optimize.main e)|>.run env
```

- [ ] **Step 4: Wrap `Smt.command` (#blaster / #solve path)**

In `Blaster/Smt/Translate.lean:94`, change

```lean
       discard $ Translate.main e|>.run env
```

to:

```lean
       discard $ (withOptimizeStats <| Translate.main e)|>.run env
```

(The file already has `open … Blaster.Optimize …` at line 8, so `withOptimizeStats` resolves.)

- [ ] **Step 5: Wrap `bmcCommand` (#bmc) and `kIndCommand` (#kind)**

`Blaster/StateMachine/BMC.lean:104`: change

```lean
     discard $ bmcStrategy e|>.run env
```

to:

```lean
     discard $ (withOptimizeStats <| bmcStrategy e)|>.run env
```

`Blaster/StateMachine/KInduction.lean:161`: change

```lean
    discard $ kIndStrategy e|>.run env
```

to:

```lean
    discard $ (withOptimizeStats <| kIndStrategy e)|>.run env
```

Both files `open … Blaster.Optimize` (verify with `grep -n "open" <file> | head -3`; if `Blaster.Optimize` is missing from the open, qualify the call as `Blaster.Optimize.withOptimizeStats`).

- [ ] **Step 6: Build**

Run: `lake build Blaster`
Expected: `Build completed successfully`.

- [ ] **Step 7: Commit**

```bash
git add Blaster/Optimize/Basic.lean Blaster/Smt/Translate.lean Blaster/StateMachine/BMC.lean Blaster/StateMachine/KInduction.lean
git commit -m "feat: wire telemetry into optimizeExprAux and command entry points (#138)"
```

---

### Task 4: Option syntax and parsers

**Files:**
- Modify: `Blaster/Command/Syntax.lean` (docstring ~line 12-23, syntax decls ~line 30-40, parsers ~line 98-126)
- Modify: `Blaster/Command/Tactic.lean` (docstring option list, ~line 22-23)

- [ ] **Step 1: Declare the syntax**

In `Blaster/Command/Syntax.lean`, after `syntax "(random-seed:" num ")" : solveOption` (line 40), add:

```lean
syntax "(stats-file:" str ")" : solveOption
syntax "(stats-interval:" num ")" : solveOption
```

- [ ] **Step 2: Add the parsers**

After `parseRandomSeed` (ends line ~103), add:

```lean
def parseStatsFile (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (stats-file: $s:str)) => return { sOpts with statsFile := some s.getString }
  | _ => return sOpts

def parseStatsInterval (sOpts : BlasterOptions) : TSyntax `solveOption → m BlasterOptions
  | `(solveOption| (stats-interval: $n:num)) => return { sOpts with statsInterval := n.getNat }
  | _ => return sOpts
```

- [ ] **Step 3: Chain them in `parseSolveOption`**

In `parseSolveOption` (line ~115-126), after `let sOpts ← parseRandomSeed sOpts opt`, add:

```lean
  let sOpts ← parseStatsFile sOpts opt
  let sOpts ← parseStatsInterval sOpts opt
```

- [ ] **Step 4: Document the options**

In the `#blaster` docstring in `Blaster/Command/Syntax.lean` (after the `solve-result` line, ~line 22), add:

```
  - `stats-file`: write optimizer growth telemetry (JSON lines) to this file (default: none)
  - `stats-interval`: optimizer stack steps between telemetry samples (default: 100000)
```

Add the same two lines to the option list in the `Blaster/Command/Tactic.lean` docstring (after its `random-seed` line, ~line 23).

- [ ] **Step 5: Build**

Run: `lake build Blaster`
Expected: `Build completed successfully`.

- [ ] **Step 6: Commit**

```bash
git add Blaster/Command/Syntax.lean Blaster/Command/Tactic.lean
git commit -m "feat: stats-file / stats-interval solve options (#138)"
```

---

### Task 5: Tests

**Files:**
- Create: `tests/Smt/SmtStats.lean`
- Create: `tests/Smt/SmtStats/SmtStatsBasic.lean`
- Modify: `tests/Smt.lean` (import list)

Note: test paths are lowercase `tests/` on disk (case-insensitive FS; module names use `Tests.`). The `#blaster` command elaborates asynchronously (snapshot task), so file-content assertions must NOT follow a `#blaster` invocation — the synchronous path via `Tests.callOptimize` (which calls `Blaster.Optimize.command`, now wrapped in `withOptimizeStats`) is used instead.

- [ ] **Step 1: Create `tests/Smt/SmtStats/SmtStatsBasic.lean`**

```lean
import Tests.Utils

/-! # Tests for the optimizer growth telemetry (stats-file / stats-interval)

Covers:
 - JSONL structure: start/sample/end events, parseable lines, monotone steps
 - default-off behavior (statsFile defaults to none)
 - open-failure resilience (bad path → warning, optimization still succeeds)
 - end-to-end option syntax smoke test through #blaster
-/

open Lean Elab Command Term Meta Blaster.Options Tests

namespace Test.SmtStatsBasic

private def statsPath : String := ".lake/smtstats_basic_test.jsonl"

private def getEv (j : Json) : String :=
  ((j.getObjVal? "ev").bind Json.getStr?).toOption.getD "<none>"

private def getNatField (j : Json) (k : String) : Nat :=
  ((j.getObjVal? k).bind Json.getNat?).toOption.getD 0

/-- Run optimization with telemetry enabled and validate the JSONL output. -/
elab "#testStatsJsonl" : command => do
  runTermElabM fun _ => do
    let sOpts : BlasterOptions :=
      { statsFile := some statsPath, statsInterval := 10, onlyOptimize := true }
    let stx ← `(∀ (x y : Nat), x + y ≥ x)
    discard <| callOptimize sOpts stx
    let content ← IO.FS.readFile statsPath
    IO.FS.removeFile statsPath
    let lines := (content.splitOn "\n").filter (· ≠ "")
    -- every line parses as JSON
    let mut events : Array Json := #[]
    for l in lines do
      match Json.parse l with
      | .ok j => events := events.push j
      | .error err => logError s!"SmtStats ❌ unparseable JSONL line: {l} ({err})"
    -- exactly one start (first) and one end (last), ≥1 sample between
    if events.size < 3 then
      logError s!"SmtStats ❌ expected ≥3 events (start/sample.../end), got {events.size}"
    if getEv events[0]! ≠ "start" then
      logError s!"SmtStats ❌ first event is not start: {events[0]!.compress}"
    if getEv events[events.size - 1]! ≠ "end" then
      logError s!"SmtStats ❌ last event is not end: {events[events.size - 1]!.compress}"
    let samples := events.filter (fun j => getEv j == "sample")
    if samples.isEmpty then
      logError "SmtStats ❌ no sample events (interval 10 should have fired)"
    -- steps strictly monotone across samples; sample carries a known cache field
    let mut prev := 0
    for s in samples do
      let steps := getNatField s "steps"
      if steps ≤ prev then
        logError s!"SmtStats ❌ non-monotone steps: {steps} after {prev}"
      prev := steps
      if (s.getObjVal? "globalRewrite").toOption.isNone then
        logError s!"SmtStats ❌ sample missing globalRewrite field: {s.compress}"
    -- end totals are consistent
    let endEv := events[events.size - 1]!
    if getNatField endEv "steps" < prev then
      logError "SmtStats ❌ end.steps below last sample steps"
    if getNatField endEv "samples" ≠ samples.size then
      logError s!"SmtStats ❌ end.samples={getNatField endEv \"samples\"} but counted {samples.size}"
    logInfo "SmtStats JSONL ✅"

#testStatsJsonl

/-- Default options leave telemetry off: no handle is opened and behavior is
    unchanged. Asserted at the options level (the whole existing suite covers
    the no-file behavior dynamically). -/
#guard (default : BlasterOptions).statsFile.isNone
#guard (default : BlasterOptions).statsInterval == 100000

/-- A bad path must warn but never fail the run. -/
elab "#testStatsBadPath" : command => do
  runTermElabM fun _ => do
    let sOpts : BlasterOptions :=
      { statsFile := some "/nonexistent-dir-smtstats-test/out.jsonl", onlyOptimize := true }
    let stx ← `(∀ (x y : Nat), x + y ≥ x)
    -- must not throw; the warning is logged by initStats
    discard <| callOptimize sOpts stx
    logInfo "SmtStats bad-path ✅"

#testStatsBadPath

-- End-to-end surface smoke test: options parse and the command completes.
-- (No file-content assertions here: #blaster elaborates asynchronously.)
#blaster (stats-file: ".lake/smtstats_syntax_test.jsonl") (stats-interval: 1000) (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat), x + y ≥ x]

end Test.SmtStatsBasic
```

- [ ] **Step 2: Create `tests/Smt/SmtStats.lean`**

```lean
import Tests.Smt.SmtStats.SmtStatsBasic
```

- [ ] **Step 3: Register in `tests/Smt.lean`**

Add to the import list (alphabetical, after `import Tests.Smt.SmtRecFun`):

```lean
import Tests.Smt.SmtStats
```

- [ ] **Step 4: Run the new test module (expect failures only if Tasks 1-4 were mis-implemented)**

Run: `lake build Tests.Smt.SmtStats.SmtStatsBasic`
Expected: build succeeds; output contains `SmtStats JSONL ✅`, `SmtStats bad-path ✅`, one `stats-file: could not open` warning (from the bad-path test — intentional), and `✅ Expected Undetermined` for the smoke `#blaster` (it runs with `only-optimize` and `solve-result: 2`).

If `Json.getNat?` does not exist under that name in Lean 4.24, use `(j.getObjVal? k).toOption.bind (fun v => v.getNat?.toOption)` style accessors — check `Lean.Data.Json` for the exact `Except`-vs-`Option` signatures and adapt the two helper functions only.

- [ ] **Step 5: Fix anything the test caught, re-run until green**

Run: `lake build Tests.Smt.SmtStats.SmtStatsBasic`
Expected: no `error:` lines, no `❌` in output.

- [ ] **Step 6: Commit**

```bash
git add tests/Smt/SmtStats.lean tests/Smt/SmtStats/SmtStatsBasic.lean tests/Smt.lean
git commit -m "test: optimizer growth telemetry JSONL structure and failure paths (#138)"
```

---

### Task 6: Full verification and wrap-up

- [ ] **Step 1: Full library build**

Run: `lake build Blaster`
Expected: `Build completed successfully`.

- [ ] **Step 2: Full test suite (regression check for the disabled path)**

Run: `LEAN_NUM_THREADS=5 lake test`
Expected: exit 0. Wall time within noise of the pre-change baseline (~90-115 s on this machine; the disabled path adds one `Option` check per stack step). If wall time regresses by >10% versus a re-measured baseline on the same machine, investigate the bump placement before proceeding.

- [ ] **Step 3: Verify no unrelated files are staged**

Run: `git status --short`
Expected: the Z3-evaluation leftovers (`Blaster/Smt/Env.lean`, `Z3Check.lean`, `Tests/Smt/SmtNat/SmtNatMod.lean`, `Tests/StateMachine/Counter06.lean`, `nat_mod.smt2`, `.claude/`) remain UNSTAGED/untracked; everything else committed.

- [ ] **Step 4: Commit the plan checkboxes and push the branch**

```bash
git add docs/superpowers/plans/2026-08-05-optimizer-stats.md
git commit -m "docs: implementation plan for optimizer telemetry (#138)"
git push -u origin feat/issue138-optimizer-stats
```

(PR creation is a separate decision for the user — do not open one unprompted.)

---

## Post-merge usage (for the #138 investigation — not part of this plan)

```
#prep_uplc (stats-file: "prep_g2200.jsonl") (stats-interval: 500000) …
```

then plot each cache column against `steps` across colll78's budget ladder; the curve
tracking the ×1.84-per-100-budget residual growth identifies the structure to target
with a DAG-merge/streaming fix. (Downstream may need the two option keywords
whitelisted in PlutusCoreBlaster's own syntax — one line, out of scope here.)
