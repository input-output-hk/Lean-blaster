# blast-check: Human-Friendly Proof Runner

**Date:** 2026-04-22
**Status:** Approved for implementation

## Summary

`blast-check` is a single-command proof runner for projects that use Blaster as a dependency. It replaces the noisy `lake build` output with clean, Elm-style terminal output: first-person language, source-linked headers, and detailed failure blocks. Users point it at a module and get a clear, scannable report of every proof attempt.

---

## Context & Goals

### Problem

Running `lake build` on a module that uses `#blaster` or `by blaster` produces noisy, hard-to-scan output: interleaved build progress, misaligned messages, and raw `sorry` warnings. There is no summary, no timing, no memory info, and failures are hard to distinguish from noise.

### Goal

A single command — no multi-step workflow — that:
- Produces zero terminal pollution from `lake build`
- Shows a live log line as each proof attempt starts and completes
- Presents failures in the Elm compiler style: first-person, source-located, with counterexamples
- Gives a clean summary with pass/fail counts and total time
- Works for any project that `require`s Blaster

---

## Architecture

Two phases, cleanly separated:

### Phase 1 — Elaboration (inside `lake build`)

When `#blaster` or `by blaster` elaborates, it:
1. Writes a `start` record to `.lake/blast-results/<ModuleName>.ndjson`
2. Runs the optimization pass + Z3 call (timed as one span)
3. Writes an `end` record with the result

When `BLAST_CHECK=1` is set in the environment, all `logInfoAt` / `logErrorAt` / `logWarningAt` calls are suppressed. Normal `lake build` and editor behaviour is unchanged when the variable is absent.

The NDJSON file is **truncated** when the first `start` event for a module is written, so stale results never accumulate.

### Phase 2 — Display (`blast-check` executable)

The `blast-check` executable (Lean4, depends on Pigment):
1. Sets `BLAST_CHECK=1` in the environment
2. Spawns `lake build <ModuleName>` with both stdout and stderr redirected to `/dev/null`
3. Polls `.lake/blast-results/<ModuleName>.ndjson` every 200ms for new lines
4. Prints a live log line for each `start` and `end` event, using Pigment for colour
5. After `lake build` exits, prints a summary footer
6. Exits with code `0` if all theorems proved, `1` otherwise

If `lake build` exits non-zero and the results file is empty or missing:
```
-- BUILD FAILED --------------------------------------------------

I could not compile MyModule. Run lake build MyModule to see why.

```

---

## NDJSON Record Format

One JSON object per line. Two event types:

**Start event:**
```json
{"event":"start","name":"myThm","desc":"Proves addition is commutative","decl":"theorem myThm : ∀ (n m : Nat), n + m = m + n","module":"MyModule","line":42}
```

**End event:**
```json
{"event":"end","name":"myThm","status":"proved","time_ms":1234,"memory_bytes":2097152}
{"event":"end","name":"myThm","status":"falsified","time_ms":567,"cex":["x = 1","y = 2"]}
{"event":"end","name":"myThm","status":"undetermined","time_ms":10000}
{"event":"end","name":"myThm","status":"timeout","time_ms":30000}
```

Field rules:
- `name`: theorem declared name (for `by blaster`) or `"Line N"` (for `#blaster` with no docstring)
- `desc`: docstring if present; for `#blaster` with no docstring, `"Line N"`; for `by blaster` with no docstring, same as `name`
- `decl`: the formatted theorem declaration string shown in output blocks. For `by blaster`: `"theorem <name> : <type>"`. For `#blaster`: the expression as a pretty-printed string.
- `time_ms`: wall-clock span from start of optimization pass to end of Z3 call
- `memory_bytes`: optional, omitted if not measurable
- `cex`: list of assignment strings, only present when `status` is `"falsified"`

---

## Changes to Blaster Source

### `#blaster` command (`Blaster/Command/Syntax.lean`)

- Before proof attempt: write `start` record; check `BLAST_CHECK` env var to suppress `logInfoAt` calls
- After proof attempt: write `end` record
- Extract preceding docstring from syntax node for `desc`

### `blaster` tactic (`Blaster/Command/Tactic.lean`)

- Same start/end writes
- `name` = theorem declared name from the tactic's goal declaration
- `desc` = theorem docstring if present, otherwise same as `name`
- Suppress log output when `BLAST_CHECK=1`

### Timing

Wrap the full proof pipeline (optimization + Z3) in a single `IO.monoNanosNow` span. This is the value written to `time_ms`.

### New helper (`Blaster/BlastResults.lean`)

Handles all NDJSON file I/O:
- `BlastResults.writeStart : StartRecord → IO Unit`
- `BlastResults.writeEnd : EndRecord → IO Unit`
- `BlastResults.resultsPath : ModuleName → FilePath`
- Truncates the file on the first `writeStart` call for a given module in the current process

---

## `blast-check` Executable

Defined in `lakefile.lean` as:
```lean
lean_exe blast_check where
  root := "BlastCheck"
```

`BlastCheck.lean` entry point:
1. Parse CLI args: `blast_check <ModuleName>` (e.g. `MyProject.Theorems`)
2. Set `BLAST_CHECK=1` via `IO.setEnv`
3. Spawn `lake build <ModuleName>` with stdout+stderr → `/dev/null`
4. Start a polling loop (200ms interval) reading new lines from the results file
5. For each `start` line: print a gray `⟳ name  desc` line
6. For each `end` line: print the appropriate block (see Output Format)
7. When `lake build` exits: drain any remaining unread lines from the results file, then print the summary footer
8. Return exit code

Depends on `Pigment` (added to lakefile as `require «Pigment» from git "https://github.com/RSoulatIOHK/Pigment.git"`).

---

## Output Format

All output uses Pigment for colour. The style follows Elm's compiler output: named section headers, first-person language, source location on the header line.

### Live start line (gray, printed when `start` event arrives)

```
  ⟳  myThm  Proves addition is commutative
```

### Proved block (green header)

```
-- PROVED -------------------------------- MyModule.lean:10  1.23s  2.1MB

    theorem addComm : ∀ (n m : Nat), n + m = m + n

```

### Falsified block (red header)

```
-- FALSIFIED ----------------------------- MyModule.lean:38  0.89s  1.4MB

    theorem wrongClaim : ∀ (x : Nat), x + 1 = x

I found a counterexample:

    x = 0

```

### Undetermined / timeout block (yellow header)

```
-- UNDETERMINED -------------------------- MyModule.lean:52  10.0s

    theorem slowThing : ...

I ran out of time before reaching a verdict.

```

### Build failure

```
-- BUILD FAILED --------------------------------------------------

I could not compile MyModule. Run lake build MyModule to see why.

```

### Summary footer

```
====================================================
3 proved  ·  1 failed  ·  1 undetermined  ·  12.57s
```

Counts coloured green / red / yellow respectively.

---

## Invocation

`blast-check` is a `lean_exe` defined in blaster's `lakefile.lean`. After `require Blaster`, users:

```bash
# Build the binary (once, or after updating blaster)
lake build +Blaster:blast_check

# Run it
.lake/packages/Blaster/build/bin/blast_check MyProject.Theorems
```

A convenience shell script `blast-check.sh` is shipped at the blaster repo root:

```bash
#!/usr/bin/env bash
lake build +Blaster:blast_check && .lake/packages/Blaster/build/bin/blast_check "$@"
```

Users symlink or copy it into their project and run:

```bash
./blast-check MyProject.Theorems
```

A `blast-check` target is added to blaster's own `Makefile` as a reference example.

---

## Out of Scope

- Solver progress caching / resume (save Z3 search state across interrupted runs) — deferred
- `--verbose` flag to surface raw build errors — deferred
- Multiple modules in one invocation — deferred
- Watch mode (re-run on file change) — deferred
