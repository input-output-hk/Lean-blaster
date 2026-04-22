# blast-check Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a `blast_check` executable to blaster that shows clean, Elm-style formatted proof results — zero `lake build` noise, live log lines per theorem, first-person failure messages, and a summary footer.

**Architecture:** During elaboration, `#blaster` and `by blaster` write NDJSON records to `.lake/blast-results/<module>.ndjson` (suppressing all `logInfo` output when `BLAST_CHECK=1`). The `blast_check` executable sets that env var, spawns `lake build` with stdout+stderr suppressed, polls the NDJSON file every 200ms, and renders results with Pigment in Elm compiler style.

**Tech Stack:** Lean 4.24.0, Lake, Pigment (`github.com/RSoulatIOHK/Pigment`), `Lean.Data.Json`

**Spec:** `docs/superpowers/specs/2026-04-22-blast-check-design.md`

---

## File Map

| File | Action | Responsibility |
|------|--------|----------------|
| `lakefile.lean` | Modify | Add Pigment dependency; add `lean_exe blast_check` |
| `Blaster/BlastResults.lean` | **Create** | NDJSON record types, JSON serialisation, file I/O |
| `Blaster/Smt/Env.lean` | Modify | Suppress `logResult` output when `BLAST_CHECK=1` |
| `Blaster/Logging/Basic.lean` | Modify | Suppress `profileTask` stdout when `BLAST_CHECK=1` |
| `Blaster/Command/Syntax.lean` | Modify | Thread source line number to `command`; write start record |
| `Blaster/Smt/Translate.lean` | Modify | `command` writes start/end records with timing |
| `Blaster/Command/Tactic.lean` | Modify | `blasterTacticImp` writes start/end records with timing |
| `BlastCheck.lean` | **Create** | Executable: process spawn, NDJSON polling, Pigment output |
| `blast-check.sh` | **Create** | Convenience wrapper shell script |
| `Tests/BlastCheck/BlastResultsTest.lean` | **Create** | Unit tests for NDJSON serialisation |

---

## Task 1: Create feature branch

**Files:** none

- [ ] **Step 1: Create and switch to branch**

```bash
git checkout -b feat/blast-check
```

- [ ] **Step 2: Verify clean state**

```bash
git status
```
Expected: `nothing to commit, working tree clean`

---

## Task 2: Update lakefile.lean — add Pigment and blast_check

**Files:**
- Modify: `lakefile.lean`

- [ ] **Step 1: Read the current lakefile**

```bash
cat lakefile.lean
```

- [ ] **Step 2: Add Pigment dependency and blast_check executable**

Open `lakefile.lean` and replace its contents with:

```lean
import Lake
open Lake DSL

package «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

require «Pigment» from git "https://github.com/RSoulatIOHK/Pigment.git" @ "main"

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  root := `Z3Check

lean_exe blast_check where
  root := `BlastCheck
```

- [ ] **Step 3: Verify lake resolves the new dependency**

```bash
lake update
```
Expected: downloads/updates Pigment, no errors.

- [ ] **Step 4: Commit**

```bash
git add lakefile.lean lake-manifest.json
git commit -m "feat: add Pigment dependency and blast_check executable skeleton"
```

---

## Task 3: Create Blaster/BlastResults.lean with tests

**Files:**
- Create: `Blaster/BlastResults.lean`
- Create: `Tests/BlastCheck/BlastResultsTest.lean`

This module handles all NDJSON file I/O and record serialisation. It lives in the `Blaster` library so both the tactic/command instrumentation and the `blast_check` executable can import it.

- [ ] **Step 1: Create `Blaster/BlastResults.lean`**

```lean
import Lean
open Lean System

namespace Blaster.BlastResults

-- ── JSON helpers ──────────────────────────────────────────────────────────────

private def jsonEscape (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c    => acc.push c) "" ++ "\""

private def getStr (j : Json) (key : String) : Option String :=
  match j with
  | .obj fields => match fields.find? key with | some (.str s) => some s | _ => none
  | _ => none

private def getNat (j : Json) (key : String) : Option Nat :=
  match j with
  | .obj fields => match fields.find? key with
    | some (.num ⟨m, 0⟩) => if m ≥ 0 then some m.toNat else none
    | _ => none
  | _ => none

private def getStrList (j : Json) (key : String) : List String :=
  match j with
  | .obj fields => match fields.find? key with
    | some (.arr elems) => elems.toList.filterMap (fun e => match e with | .str s => some s | _ => none)
    | _ => []
  | _ => []

-- ── Record types ──────────────────────────────────────────────────────────────

structure StartRecord where
  name       : String
  desc       : String
  decl       : String
  moduleName : String
  line       : Nat

structure EndRecord where
  name         : String
  status       : String   -- "proved" | "falsified" | "undetermined" | "timeout"
  time_ms      : Nat
  memory_bytes : Option Nat := none
  cex          : List String := []

inductive Record where
  | start (r : StartRecord)
  | end_  (r : EndRecord)
  | unknown

-- ── Serialisation ─────────────────────────────────────────────────────────────

def startRecordJson (r : StartRecord) : String :=
  s!"\{\"event\":\"start\",\"name\":{jsonEscape r.name},\"desc\":{jsonEscape r.desc}," ++
  s!"\"decl\":{jsonEscape r.decl},\"module\":{jsonEscape r.moduleName},\"line\":{r.line}}"

def endRecordJson (r : EndRecord) : String :=
  let base := s!"\{\"event\":\"end\",\"name\":{jsonEscape r.name}," ++
              s!"\"status\":{jsonEscape r.status},\"time_ms\":{r.time_ms}"
  let withMem := match r.memory_bytes with
    | none   => base
    | some b => base ++ s!",\"memory_bytes\":{b}"
  let withCex :=
    if r.cex.isEmpty then withMem
    else withMem ++ ",\"cex\":[" ++ (",".intercalate (r.cex.map jsonEscape)) ++ "]"
  withCex ++ "}"

-- ── Deserialisation ───────────────────────────────────────────────────────────

def parseRecord (line : String) : Record :=
  match Json.parse line with
  | .error _ => .unknown
  | .ok json =>
    match getStr json "event" with
    | some "start" =>
      match getStr json "name", getStr json "desc", getStr json "decl",
            getStr json "module", getNat json "line" with
      | some name, some desc, some decl, some modName, some ln =>
        .start { name, desc, decl, moduleName := modName, line := ln }
      | _ => .unknown
    | some "end" =>
      match getStr json "name", getStr json "status", getNat json "time_ms" with
      | some name, some status, some time_ms =>
        .end_ { name, status, time_ms,
                memory_bytes := getNat json "memory_bytes",
                cex := getStrList json "cex" }
      | _ => .unknown
    | _ => .unknown

-- ── File I/O ──────────────────────────────────────────────────────────────────

private def resultsDir : FilePath := ".lake" / "blast-results"

def resultsPath (moduleName : String) : FilePath :=
  resultsDir / (moduleName ++ ".ndjson")

-- Tracks which modules have been truncated during this OS process lifetime.
private initialize truncatedModules : IO.Ref (List String) ← IO.mkRef []

def writeStart (r : StartRecord) : IO Unit := do
  IO.FS.createDirAll resultsDir
  let path := resultsPath r.moduleName
  let truncated ← truncatedModules.get
  if !truncated.contains r.moduleName then
    IO.FS.writeFile path ""
    truncatedModules.set (r.moduleName :: truncated)
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn (startRecordJson r)
  h.flush

def writeEnd (r : EndRecord) (moduleName : String) : IO Unit := do
  let h ← IO.FS.Handle.mk (resultsPath moduleName) .append
  h.putStrLn (endRecordJson r)
  h.flush

/-- Read all lines from the results file. Returns empty array if file absent. -/
def readAllLines (moduleName : String) : IO (Array String) := do
  let path := resultsPath moduleName
  if !(← path.pathExists) then return #[]
  let content ← IO.FS.readFile path
  return content.splitOn "\n" |>.filter (· ≠ "") |>.toArray

/-- Read lines added after `lastCount` lines. Returns new lines and new total. -/
def readNewLines (moduleName : String) (lastCount : Nat) : IO (Array String × Nat) := do
  let all ← readAllLines moduleName
  return (all.extract lastCount all.size, all.size)

end Blaster.BlastResults
```

- [ ] **Step 2: Create `Tests/BlastCheck/BlastResultsTest.lean`**

`#test` does not exist in Lean4. Use `#eval` with `IO.ofExcept` / `throw` to make failures visible as elaboration errors (which cause `lake test` to fail).

```lean
import Blaster.BlastResults
open Blaster.BlastResults

-- ── JSON round-trip tests ─────────────────────────────────────────────────────

private def check (label : String) (cond : Bool) : IO Unit :=
  if cond then pure ()
  else throw (IO.userError s!"BlastResults test FAILED: {label}")

-- StartRecord round-trip
#eval show IO Unit from do
  let r : StartRecord := { name := "myThm", desc := "Proves foo", decl := "theorem myThm : True",
                           moduleName := "My.Module", line := 42 }
  let json := startRecordJson r
  match parseRecord json with
  | .start s =>
    check "name"   (s.name == "myThm")
    check "line"   (s.line == 42)
    check "module" (s.moduleName == "My.Module")
  | _ => throw (IO.userError "StartRecord round-trip: wrong variant")

-- EndRecord proved round-trip
#eval show IO Unit from do
  let r : EndRecord := { name := "myThm", status := "proved", time_ms := 1234 }
  let json := endRecordJson r
  match parseRecord json with
  | .end_ e =>
    check "status"   (e.status == "proved")
    check "time_ms"  (e.time_ms == 1234)
    check "cex empty" e.cex.isEmpty
  | _ => throw (IO.userError "EndRecord proved round-trip: wrong variant")

-- EndRecord with counterexample
#eval show IO Unit from do
  let r : EndRecord := { name := "bad", status := "falsified", time_ms := 99,
                         cex := ["x = 1", "y = 2"] }
  let json := endRecordJson r
  match parseRecord json with
  | .end_ e => check "cex" (e.cex == ["x = 1", "y = 2"])
  | _ => throw (IO.userError "EndRecord cex round-trip: wrong variant")

-- Special characters in strings should round-trip
#eval show IO Unit from do
  let r : StartRecord := { name := "has\"quote", desc := "line1\nline2", decl := "d",
                           moduleName := "M", line := 1 }
  let json := startRecordJson r
  match parseRecord json with
  | .start s =>
    check "escaped quote" (s.name == "has\"quote")
    check "escaped newline" (s.desc == "line1\nline2")
  | _ => throw (IO.userError "Special chars round-trip: wrong variant")

-- Malformed lines return .unknown
#eval show IO Unit from do
  match parseRecord "not json" with
  | .unknown => pure ()
  | _ => throw (IO.userError "Malformed line should return .unknown")
```

- [ ] **Step 3: Add the test file to `Tests/Basic.lean`**

Open `Tests/Basic.lean` and add at the end:

```lean
import Tests.BlastCheck.BlastResultsTest
```

- [ ] **Step 4: Run the tests**

```bash
lake test
```
Expected: all `#eval` blocks complete without errors, `lake test` exits 0.

- [ ] **Step 5: Commit**

```bash
git add Blaster/BlastResults.lean Tests/BlastCheck/BlastResultsTest.lean Tests/Basic.lean
git commit -m "feat: add BlastResults NDJSON serialisation and file I/O"
```

---

## Task 4: Suppress log output when BLAST_CHECK=1

**Files:**
- Modify: `Blaster/Smt/Env.lean` (lines 55–80, the `logResult` function)
- Modify: `Blaster/Logging/Basic.lean` (lines 36–47, the `profileTask` function)

When `blast_check` runs, it sets `BLAST_CHECK=1` so all Lean elaboration logging is silent. Normal `lake build` and editor use are unaffected (env var absent → existing behaviour).

- [ ] **Step 1: Suppress `logResult` in `Blaster/Smt/Env.lean`**

Find the `logResult` definition (line ~55) and add an early return at the top:

```lean
def logResult (r : Result) (isCTI := false) (indLabel := "") (cexLabel := "Counterexample") : TranslateEnvT Unit := do
  -- In blast-check mode all output goes through the NDJSON file, not logInfo.
  if (← IO.getEnv "BLAST_CHECK") == some "1" then return ()
  let sOpts := (← get).optEnv.options.solverOptions
  -- ... rest of existing function unchanged ...
```

- [ ] **Step 2: Suppress `profileTask` in `Blaster/Logging/Basic.lean`**

Find `profileTask` (line ~36) and add an early return at the top of the `if verbose` branch:

```lean
def profileTask (msg : String) (p : TranslateEnvT α) (verboseLevel := 1) : TranslateEnvT α := do
  let sOpts := (← get).optEnv.options.solverOptions
  if sOpts.verbose ≥ verboseLevel && (← IO.getEnv "BLAST_CHECK") != some "1" then
    let startTime ← IO.monoMsNow
    IO.println f!"[Start]: {msg}"
    (← IO.getStdout).flush
    let res ← p
    let stopTime ← IO.monoMsNow
    let elapseTime := (stopTime - startTime).toFloat / 1000.0
    IO.println f!"[End]: {msg} ({reprPrec elapseTime 2}s)"
    return res
  else p
```

- [ ] **Step 3: Build to verify no compile errors**

```bash
lake build Blaster
```
Expected: compiles cleanly.

- [ ] **Step 4: Commit**

```bash
git add Blaster/Smt/Env.lean Blaster/Logging/Basic.lean
git commit -m "feat: suppress logResult and profileTask output when BLAST_CHECK=1"
```

---

## Task 5: Instrument the #blaster command

**Files:**
- Modify: `Blaster/Command/Syntax.lean` (thread source line into `commandInvoker`)
- Modify: `Blaster/Smt/Translate.lean` (update `command` to write NDJSON records)

- [ ] **Step 1: Thread source line through `commandInvoker` in `Blaster/Command/Syntax.lean`**

Change `commandInvoker` to compute the source line and pass it to `f`. Replace the existing `commandInvoker` definition:

```lean
def commandInvoker (f : BlasterOptions → Syntax → Nat → TermElabM Unit) : CommandElab := fun stx => do
  let some cancelTk := (← read).cancelTk? | unreachable!
  let opts := stx[1].getArgs
  let sOpts ← parseSolveOptions opts default
  let tr ← parseTerm ⟨stx[2]⟩
  -- Compute source line for blast-check output (position of the #blaster keyword).
  let fm ← getFileMap
  let line := stx.getPos?.map (fm.toPosition ·) |>.map (·.line) |>.getD 0
  let act ← wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ =>
    withoutModifyingEnv $ runTermElabM fun _ =>
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0, maxRecDepth := 0 }) $ do
        f sOpts tr line
  let task ← BaseIO.asTask (prio := Task.Priority.dedicated) (act ())
  logSnapshotTask { stx? := some stx, task, cancelTk? := cancelTk }

@[command_elab solve]
def solveImp : CommandElab :=
  commandInvoker (fun opts tr line => Blaster.Smt.command opts tr line)
```

- [ ] **Step 2: Update `command` in `Blaster/Smt/Translate.lean` to write NDJSON records**

Replace the existing `command` function (lines 90–94):

```lean
def command (sOpts : BlasterOptions) (stx : Syntax) (sourceLine : Nat := 0) : TermElabM Unit := do
  withRef stx do
    let e ← instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none)
    let modName := (← getEnv).mainModule.toString
    -- Pretty-print the expression for the decl field.
    let declStr := s!"#blaster [{← ppExpr e}]"
    let startRec : Blaster.BlastResults.StartRecord :=
      { name := s!"Line {sourceLine}", desc := s!"Line {sourceLine}",
        decl := declStr, moduleName := modName, line := sourceLine }
    (Blaster.BlastResults.writeStart startRec).catchExceptions fun _ => pure ()
    let startMs ← IO.monoMsNow
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    let ((result, _), _) ← Translate.main e |>.run env
    let endMs ← IO.monoMsNow
    let (status, cex) := match result with
      | .Valid          => ("proved",      [])
      | .Falsified cex  => ("falsified",   cex)
      | .Undetermined   => ("undetermined",[])
    let endRec : Blaster.BlastResults.EndRecord :=
      { name := s!"Line {sourceLine}", status, time_ms := endMs - startMs }
    let endRecWithCex := { endRec with cex }
    (Blaster.BlastResults.writeEnd endRecWithCex modName).catchExceptions fun _ => pure ()
```

Also add the import at the top of `Blaster/Smt/Translate.lean`:

```lean
import Blaster.BlastResults
```

- [ ] **Step 3: Build to verify**

```bash
lake build Blaster
```
Expected: compiles cleanly.

- [ ] **Step 4: Quick manual check — run a #blaster test and inspect the NDJSON file**

```bash
BLAST_CHECK=1 lake build Tests.Smt.SmtEqArith 2>/dev/null
cat .lake/blast-results/Tests.Smt.SmtEqArith.ndjson | head -6
```
Expected: several JSON lines with `"event":"start"` and `"event":"end"`.

- [ ] **Step 5: Commit**

```bash
git add Blaster/Command/Syntax.lean Blaster/Smt/Translate.lean
git commit -m "feat: instrument #blaster command to write NDJSON start/end records"
```

---

## Task 6: Instrument the blaster tactic

**Files:**
- Modify: `Blaster/Command/Tactic.lean`

- [ ] **Step 1: Update `blasterTacticImp` to write NDJSON records**

Add `import Blaster.BlastResults` at the top of the file, then replace the `blasterTacticImp` definition:

```lean
import Blaster.BlastResults

-- (existing imports unchanged)

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
    let opts := stx[1].getArgs
    let sOpts ← parseSolveOptions opts default
    -- Capture the original goal type for display before hypotheses are reverted.
    let origGoalType ← (← getMainGoal).getType
    let goal ← revertHypotheses (← getMainGoal)
    -- Gather theorem identity from the enclosing declaration.
    let declName? ← liftTermElabM do return (← read).declName?
    let name    := declName?.map (·.toString) |>.getD "anonymous"
    let docStr? ← liftTermElabM do
      if let some n := declName? then findDocString? (← getEnv) n
      else return none
    let desc    := docStr?.getD name
    let declStr := s!"theorem {name} : {← ppExpr origGoalType}"
    let modName := (← getEnv).mainModule.toString
    -- Source line from the `by blaster` syntax position.
    let fm ← getFileMap
    let line := stx.getPos?.map (fm.toPosition ·) |>.map (·.line) |>.getD 0
    let startRec : Blaster.BlastResults.StartRecord :=
      { name, desc, decl := declStr, moduleName := modName, line }
    (Blaster.BlastResults.writeStart startRec).catchExceptions fun _ => pure ()
    let startMs ← IO.monoMsNow
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    let ((result, optExpr), _) ←
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
        IO.setNumHeartbeats 0
        Translate.main (← goal.getType) (logUndetermined := false) |>.run env
    let endMs ← IO.monoMsNow
    let (status, cex) := match result with
      | .Valid         => ("proved",       [])
      | .Falsified cex => ("falsified",    cex)
      | .Undetermined  => ("undetermined", [])
    let endRec : Blaster.BlastResults.EndRecord :=
      { name, status, time_ms := endMs - startMs, cex }
    (Blaster.BlastResults.writeEnd endRec modName).catchExceptions fun _ => pure ()
    -- Original result-handling logic unchanged.
    match result with
    | .Valid       => goal.admit
    | .Falsified _ => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
    | .Undetermined =>
        let newGoal ← goal.replaceTargetDefEq optExpr
        replaceMainGoal [newGoal]

  where

    @[always_inline, inline]
    revertHypotheses (goal : MVarId) : TacticM MVarId :=
      goal.withContext $ do
        let lctx ← getLCtx
        let mut hyps := #[]
        for decl in lctx do
          if decl.isImplementationDetail then continue
          if ← isProp decl.type then
            hyps := hyps.push decl.fvarId
        hyps.foldrM
          (fun h g => do let (_, g) ← g.revert #[h]; return g) goal
```

- [ ] **Step 2: Build to verify**

```bash
lake build Blaster
```
Expected: compiles cleanly.

- [ ] **Step 3: Quick manual check — run a by blaster test**

Create a temp file `/tmp/TacticCheck.lean`:
```lean
import Blaster
theorem testAdd : ∀ (n : Nat), n + 0 = n := by blaster
```

```bash
BLAST_CHECK=1 lake build 2>/dev/null
cat .lake/blast-results/*.ndjson 2>/dev/null | grep testAdd
```
Expected: a `start` record and `end` record with `"name":"testAdd"`.

- [ ] **Step 4: Commit**

```bash
git add Blaster/Command/Tactic.lean
git commit -m "feat: instrument blaster tactic to write NDJSON start/end records"
```

---

## Task 7: Create BlastCheck.lean — the executable

**Files:**
- Create: `BlastCheck.lean`

This is the entry point for `lean_exe blast_check`. It:
1. Sets `BLAST_CHECK=1` and spawns `lake build <module>` with all output suppressed
2. Polls `.lake/blast-results/<module>.ndjson` for new lines every 200ms
3. Renders each record in Elm-compiler style with Pigment
4. Prints a summary footer and exits with code 0/1

- [ ] **Step 1: Create `BlastCheck.lean`**

```lean
import Blaster.BlastResults
import Pigment
open Pigment Blaster.BlastResults System

-- ── Formatting helpers ────────────────────────────────────────────────────────

private def dashes (n : Nat) : String := String.mk (List.replicate n '-')

private def moduleToFilePath (moduleName : String) : String :=
  moduleName.replace "." "/" ++ ".lean"

private def formatMs (ms : Nat) : String :=
  let s := (ms.toFloat / 1000.0)
  let rounded := (s * 100.0).round / 100.0
  s!"{rounded}s"

private def headerWidth : Nat := 60

private def paddedHeader (label : String) (right : String) : String :=
  let core := "-- " ++ label ++ " "
  let available := headerWidth - core.length - right.length
  let fill := if available > 0 then dashes available else ""
  core ++ fill ++ " " ++ right

-- ── Per-record renderers ──────────────────────────────────────────────────────

private def renderStart (r : StartRecord) : PigmentM Unit := do
  -- Show "name  desc" when they differ; just "name" when both are the same (e.g. #blaster Line N).
  let label := if r.desc == r.name then r.name else s!"{r.name}  {r.desc}"
  println (empty s!"  ⟳  {label}" |> dim)

private def renderProved (start : StartRecord) (e : EndRecord) : PigmentM Unit := do
  let right := s!"{moduleToFilePath start.moduleName}:{start.line}  {formatMs e.time_ms}"
  println (empty (paddedHeader "PROVED" right) |> green |> bold)
  println (empty "")
  println (empty s!"    {start.decl}")
  println (empty "")

private def renderFalsified (start : StartRecord) (e : EndRecord) : PigmentM Unit := do
  let right := s!"{moduleToFilePath start.moduleName}:{start.line}  {formatMs e.time_ms}"
  println (empty (paddedHeader "FALSIFIED" right) |> red |> bold)
  println (empty "")
  println (empty s!"    {start.decl}")
  println (empty "")
  println (empty "I found a counterexample:")
  println (empty "")
  for assignment in e.cex do
    println (empty s!"    {assignment}" |> yellow)
  println (empty "")

private def renderUndetermined (start : StartRecord) (e : EndRecord) : PigmentM Unit := do
  let right := s!"{moduleToFilePath start.moduleName}:{start.line}  {formatMs e.time_ms}"
  println (empty (paddedHeader "UNDETERMINED" right) |> yellow |> bold)
  println (empty "")
  println (empty s!"    {start.decl}")
  println (empty "")
  println (empty "I ran out of time before reaching a verdict.")
  println (empty "")

private def renderBuildFailed (moduleName : String) : PigmentM Unit := do
  println (empty (paddedHeader "BUILD FAILED" "") |> red |> bold)
  println (empty "")
  println (empty s!"I could not compile {moduleName}. Run lake build {moduleName} to see why.")
  println (empty "")

private def renderSummary (proved falsified undetermined : Nat) (totalMs : Nat) : PigmentM Unit := do
  println (empty (dashes headerWidth))
  let p := empty s!"  {proved} proved" |> green
  let f := empty s!"  {falsified} failed" |> (if falsified > 0 then red else green)
  let u := empty s!"  {undetermined} undetermined" |> (if undetermined > 0 then yellow else green)
  let t := empty s!"  {formatMs totalMs} total"
  printLine [p, empty "  ·", f, empty "  ·", u, empty "  ·", t]
  println (empty "")

-- ── Polling loop ──────────────────────────────────────────────────────────────

private structure RunState where
  lineCount    : Nat := 0
  pendingStart : Option StartRecord := none  -- start record waiting for its end
  proved       : Nat := 0
  falsified    : Nat := 0
  undetermined : Nat := 0
  totalMs      : Nat := 0

private def processLine (state : RunState) (line : String) : PigmentM RunState :=
  match parseRecord line with
  | .start r =>
    renderStart r
    return { state with pendingStart := some r }
  | .end_ e =>
    let newState := { state with pendingStart := none,
                                 totalMs := state.totalMs + e.time_ms }
    match state.pendingStart with
    | none => return newState  -- shouldn't happen but safe to skip
    | some startRec =>
      match e.status with
      | "proved" =>
        renderProved startRec e
        return { newState with proved := newState.proved + 1 }
      | "falsified" =>
        renderFalsified startRec e
        return { newState with falsified := newState.falsified + 1 }
      | _ =>
        renderUndetermined startRec e
        return { newState with undetermined := newState.undetermined + 1 }
  | .unknown => return state

private def drainFile (moduleName : String) (state : RunState) : PigmentM RunState := do
  let (newLines, newCount) ← BlastResults.readNewLines moduleName state.lineCount
  let mut s := { state with lineCount := newCount }
  for line in newLines do
    s ← processLine s line
  return s

-- ── Main ─────────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  let some moduleName := args.head? | do
    IO.eprintln "Usage: blast-check <ModuleName>"
    IO.eprintln "Example: blast-check MyProject.Theorems"
    return (1 : UInt32)
  -- Spawn lake build with all output suppressed and BLAST_CHECK set.
  let proc ← IO.Process.spawn {
    cmd    := "lake"
    args   := #["build", moduleName]
    stdout := .null
    stderr := .null
    env    := #[("BLAST_CHECK", "1")]
  }
  -- Spawn proc.wait as a non-blocking task so we can poll the NDJSON file concurrently.
  -- IO.asTask : IO α → BaseIO (Task (Except IO.Error α))
  -- Task.getResult? : Task (Except ε α) → Option (Except ε α)  (non-blocking)
  let waitTask ← IO.asTask proc.wait
  -- Enter Pigment context for all output.
  run do
    let mut state : RunState := {}
    -- Live polling loop: render records as they arrive in the NDJSON file.
    repeat
      state ← drainFile moduleName state
      if waitTask.getResult?.isSome then break
      IO.sleep 200
    -- Final drain: flush any lines written between the last poll and process exit.
    state ← drainFile moduleName state
    let buildOk : Bool := match waitTask.getResult? with
      | some (.ok code) => code == 0
      | _               => false
    if !buildOk && state.lineCount == 0 then
      renderBuildFailed moduleName
      return (1 : UInt32)
    renderSummary state.proved state.falsified state.undetermined state.totalMs
    return (if state.falsified > 0 then (1 : UInt32) else (0 : UInt32))
```

- [ ] **Step 2: Build the executable**

```bash
lake build blast_check
```
Expected: compiles cleanly. Binary at `.lake/build/bin/blast_check`.

- [ ] **Step 3: Quick smoke test — run against an existing test module**

```bash
.lake/build/bin/blast_check Tests.Smt.SmtEqArith
```
Expected:
- No `lake build` noise
- Lines like `⟳  Line 7  Line 7` followed by `-- PROVED ---...` blocks
- A summary footer at the end

- [ ] **Step 4: Commit**

```bash
git add BlastCheck.lean
git commit -m "feat: add BlastCheck executable with Elm-style Pigment output"
```

---

## Task 8: Create blast-check.sh convenience wrapper

**Files:**
- Create: `blast-check.sh`

- [ ] **Step 1: Create the wrapper script**

```bash
#!/usr/bin/env bash
# blast-check.sh — convenience wrapper for projects that use Blaster as a dependency.
#
# Usage: ./blast-check.sh <ModuleName>
# Example: ./blast-check.sh MyProject.Theorems
#
# On first run (or after `lake update`), builds the blast_check binary from the
# Blaster dependency. Subsequent runs skip the build step if the binary exists.

set -euo pipefail

BINARY=".lake/packages/Blaster/build/bin/blast_check"

if [ ! -f "$BINARY" ]; then
  echo "Building blast-check binary..."
  lake build +Blaster:blast_check
fi

exec "$BINARY" "$@"
```

- [ ] **Step 2: Make it executable**

```bash
chmod +x blast-check.sh
```

- [ ] **Step 3: Verify the script works from the blaster repo itself**

```bash
./blast-check.sh Tests.Smt.SmtEqArith
```
Expected: same Elm-style output as in Task 7 Step 3.

- [ ] **Step 4: Commit**

```bash
git add blast-check.sh
git commit -m "feat: add blast-check.sh convenience wrapper script"
```

---

## Task 9: Add blast-check target to Makefile and update README

**Files:**
- Modify: `Makefile`
- Modify: `README.md`

- [ ] **Step 1: Add Makefile target**

Open `Makefile` and add:

```makefile
blast-check: ## Run blast-check on a module. Usage: make blast-check MODULE=Tests.Smt.SmtEqArith
	@lake build blast_check
	@.lake/build/bin/blast_check $(MODULE)
```

- [ ] **Step 2: Add usage section to README.md**

Find the section in `README.md` that describes how to run blaster (probably the "Usage" or "Getting Started" section) and add a subsection:

```markdown
## blast-check: Human-Friendly Output

Instead of reading raw `lake build` output, use `blast-check` for clean, formatted results.

**For blaster developers (in this repo):**
```bash
make blast-check MODULE=Tests.Smt.SmtEqArith
```

**For projects that use Blaster as a dependency:**
```bash
# Build the binary once after adding the dependency
lake build +Blaster:blast_check

# Run it
.lake/packages/Blaster/build/bin/blast_check MyProject.Theorems
```

Or copy `blast-check.sh` to your project and run:
```bash
./blast-check.sh MyProject.Theorems
```
```

- [ ] **Step 3: Commit**

```bash
git add Makefile README.md
git commit -m "docs: add blast-check Makefile target and README section"
```

---

## Task 10: Integration test — verify end-to-end output

**Files:**
- Create: `Tests/BlastCheck/IntegrationTheorems.lean` (a small module with `#blaster` and `by blaster` calls for testing)

- [ ] **Step 1: Create a test module that covers all output cases**

```lean
import Blaster

/-- Commutativity of addition -/
theorem addComm : ∀ (n m : Nat), n + m = m + n := by blaster

/-- Zero is the additive identity -/
theorem zeroAdd : ∀ (n : Nat), 0 + n = n := by blaster

-- A falsified case: this is wrong on purpose
#blaster (solve-result: 1) [∀ (x : Nat), x + 1 = x]

-- An undetermined case: Z3 cannot handle Nat.pow in general.
#blaster (timeout: 2) (solve-result: 2) [∀ (x : Nat), 0 < 2^x]
```

- [ ] **Step 2: Run blast-check on the integration module**

```bash
.lake/build/bin/blast_check Tests.BlastCheck.IntegrationTheorems
```

Expected output structure (exact values will vary):
```
  ⟳  addComm  Commutativity of addition
-- PROVED --------------------------------- Tests/BlastCheck/IntegrationTheorems.lean:4  1.23s

    theorem addComm : ∀ (n m : Nat), n + m = m + n

  ⟳  zeroAdd  Zero is the additive identity
-- PROVED --------------------------------- Tests/BlastCheck/IntegrationTheorems.lean:7  0.45s

    theorem zeroAdd : ∀ (n : Nat), 0 + n = n

  ⟳  Line 10  Line 10
-- FALSIFIED ------------------------------- Tests/BlastCheck/IntegrationTheorems.lean:10  0.12s

    #blaster [∀ (x : Nat), x + 1 = x]

I found a counterexample:

    x = 0

============================================================
  2 proved  ·  1 failed  ·  0 undetermined  ·  1.80s total
```

- [ ] **Step 3: Verify exit code**

```bash
.lake/build/bin/blast_check Tests.BlastCheck.IntegrationTheorems; echo "Exit: $?"
```
Expected: `Exit: 1` (because there is a falsified theorem).

```bash
.lake/build/bin/blast_check Tests.Smt.SmtEqArith; echo "Exit: $?"
```
Expected: `Exit: 0` (all theorems in that file prove).

- [ ] **Step 4: Commit**

```bash
git add Tests/BlastCheck/IntegrationTheorems.lean
git commit -m "test: add blast-check integration theorem module"
```

---

## Task 11: Final review and branch cleanup

- [ ] **Step 1: Run the full test suite to verify nothing regressed**

```bash
lake test
```
Expected: all existing tests pass.

- [ ] **Step 2: Run blast-check on the blaster test suite itself**

```bash
.lake/build/bin/blast_check Tests.Smt.SmtEqArith
.lake/build/bin/blast_check Tests.Smt.SmtMatch
```
Expected: clean formatted output for both, exit code 0.

- [ ] **Step 3: Verify the binary path used in blast-check.sh is correct for dependent projects**

The script uses `.lake/packages/Blaster/build/bin/blast_check`. Confirm this path is produced when a project does `lake build +Blaster:blast_check`. (Can verify by checking that `lake build blast_check` puts the binary at `.lake/build/bin/blast_check` in the blaster repo itself — dependent projects use the packages path.)

- [ ] **Step 4: Push the branch**

```bash
git push -u origin feat/blast-check
```
