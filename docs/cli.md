# lean-blaster executable

First milestone for [#402](https://github.com/input-output-hk/Lean-blaster/issues/402),
[#404](https://github.com/input-output-hk/Lean-blaster/issues/404), and
[#405](https://github.com/input-output-hk/Lean-blaster/issues/405).
Built from `beta-lambda-cache-optimization`.

## Install and run

```sh
make install

lean-blaster
lean-blaster doctor
lean-blaster check Properties.lean
lean-blaster discover Properties.lean
lean-blaster check Tests/Smt
lean-blaster discover Tests/Smt --json
lean-blaster check Properties.lean --llm blaster-report.md
```

`make install` builds the executable, installs its own compiled Blaster libraries and
Z3, and creates `~/.local/bin/lean-blaster`. That directory must be on `PATH`; the
installer tells you if it is missing. Shell profiles are not edited. A custom prefix
is available through `python3 scripts/install_cli.py --prefix /your/install/location`.
An existing unrelated command is preserved. Reinstalling switches the command to a
finished release directory and preserves resources used by already-running processes.
Source builds require a C compiler (`cc`), in addition to the pinned Lean toolchain,
for the executable's small OS adapter. That adapter is linked into the installed
command and adds no separate native library installation step.
On macOS, the installer adds the matching Lean toolchain's `lib/lean` directory
to the executable's runpaths. This lets native libraries loaded from a caller's
Lake project resolve Lean's shared libraries, including `libLake_shared.dylib`.
The caller's native libraries remain in their own project or package directories.

The command locates the installed files through its resolved executable path, so
launching it through the PATH symlink works from other directories. It remembers
the matching Lean toolchain instead of using whichever Lean happens to be active
in the current shell. For a Lake project, it discovers compiled dependencies
automatically from the input file's location, falling back to the current directory.
You do not need to prefix commands with `lake env` or point into `.lake/build/bin`.
Projects must use a compatible Lean toolchain. Missing or stale imports are prepared
automatically with Lake before the selected file is elaborated. The progress stage
says "I'm preparing your dependencies"; successful dependency build logs and warnings
stay out of the normal report. `--debug` shows Lake's raw build output, and build
failures still include their diagnostics. The selected source
is not compiled first and then checked a second time. `--no-build` uses existing
compiled imports and reports a recovery action when they are missing.

If a project also declares Blaster as a Lake dependency, its compiled Blaster modules
must match those bundled with the installed executable. Lean cannot initialize two
different builds of the same module in one process. The CLI checks the imported
Blaster artifacts before loading the project's native plugin; for matching builds it
uses its own already initialized code. For a mismatch, update the project's Blaster
dependency to the revision used for the CLI installation and rebuild the project's
dependencies, or install a CLI built from the project's Blaster revision.

Try `check examples/Properties.lean` for a valid tactic result, a counterexample,
and an unresolved optimizer-only check. This demonstration intentionally exits 1
because one property is false. Select just the valid example with
`check examples/Properties.lean --decl CliDemo.reflexive`.

The fetch script installs the pinned official **Z3 5.3.2** release privately under
`.lake/build/libexec/lean-blaster/`. Its platform archive must match the SHA-256 in
`scripts/z3-release.json`. Binaries and downloads remain ignored build products.
The archive's MIT license is retained alongside the solver. The script does not
replace the system's Z3 installation or modify shell configuration.

Solver selection is `--solver PATH`, then nonempty `BLASTER_SOLVER`, then the installation's private solver, then
`z3` on `PATH`. A broken explicit or bundled solver is reported rather than silently
switching versions. `doctor` reports the selected path, source, and actual version.
Dependency builds inherit the selected solver through `BLASTER_SOLVER`, so they can
use the private bundle without a system Z3 installation. Source options govern
checks executed while compiling imported modules; CLI timeout/seed options govern
the checks captured from the selected file.

The installer keeps private releases under `~/.local/share/lean-blaster/releases/`.
Each contains `bin/lean-blaster`, compiled Blaster modules in `lib/lean/`, and the
solver and required runtime libraries in `libexec/lean-blaster/`, including
`LICENSE-Z3.txt`, `release.json`, and the Lean toolchain's `runtime.json`. Downloads are
pinned for macOS, Linux, and Windows on arm64 and x64; the Linux archives require
their named glibc version. Only the host platform has been exercised locally.

This milestone still uses an installed Lean toolchain. A fully relocatable release that also packages Lean's runtime
libraries and module artifacts is subsequent work. Normal invocations already use
the short `lean-blaster` command.

## What is checked

Given a file that imports `Blaster`, the CLI elaborates the source with Lean and
captures actual `#blaster` commands and `blaster` tactic invocations, including
`theorem ... := by blaster`. A tactic invocation is associated with its enclosing
declaration. A declaration may have multiple calls, each with its own result.
Results describe Blaster invocations; they do not assert that the complete file or
every enclosing proof was independently verified by Blaster.

```lean
import Blaster

theorem reflexive (n : Nat) : n = n := by blaster
#blaster [∀ a b : Nat, a + b = b + a]
```

`--decl NAME` is repeatable and uses fully qualified declaration names. It filters
captured calls to the selected declarations. Selected declarations with a captured
tactic result are not solved a second time. Other selected propositions are checked
after successful elaboration. Unselected `#blaster` commands are not solved.

Lean must still elaborate the whole file, including unselected theorem bodies,
ordinary tactics, macros, and `#eval`. It is not possible to skip arbitrary theorem
bodies while retaining their normal checked declarations. Source diagnostics are
preserved, and direct source output is redirected to stderr.

Results from speculative tactic branches are invocation results, not a claim about
which branch was ultimately used. Imported precompiled modules are not re-elaborated.
State-machine commands retain their existing diagnostics; structured BMC and
k-induction reporting is outside this milestone. A file with no captured or selected
checks exits unsuccessfully rather than reporting a vacuous success.

An umbrella such as `Tests/Smt/SmtNat.lean` only imports test modules. With no
`--decl` selection, the CLI walks local source imports, checks each leaf source,
and combines their results. It does not compile the umbrella before doing this.
Each local source is selected once, including through nested umbrellas. The report
warns about nonstandard imports without local source files; they are not traversed.
An imported source may still be compiled as a dependency of another source when Lean needs
its declarations.

`check DIRECTORY` and `discover DIRECTORY` recursively enumerate `.lean` sources in
stable path order. They canonicalize paths so a linked file is visited once, skip
linked directories, `.lake`/`.git`, and `lakefile.lean`; they do not follow imports while selecting
files. Thus an import-only umbrella and another umbrella that names the same leaf
do not schedule that leaf twice in one invocation. `check` elaborates each selected source directly
and combines its results; files with no direct checks do not cause individual
errors. An empty directory check exits with an error. `--decl` requires a single
file. Lake may still compile a source as a dependency of another source on a cold
build; that compilation is separate from the CLI's selected-source pass.
Successful Lake build logs stay quiet; failing build jobs remain visible.
Terminal output nests imported source sections. Every Blaster invocation appears inside
its source section, including valid results. Section totals count invocations rather
than declarations: one proof may call `blaster` more than once. Source annotations
such as `(solve-result: 1)` mark falsifications as expected in the display. JSON
retains individual actual results and source locations without presentation grouping.

### Counterexample diagnostics

For a falsified check, the terminal report shows the check's source line with one
line of context on either side, a compact goal, and up to six named witness values.
Long source lines scroll to keep the invocation column visible and are clipped to
keep reports readable for large declarations. Source frames come from the checked
file; if that file is unavailable, the location and goal remain in the result.
The frame points to the reported `#blaster` goal or tactic site, which may be
separate from the definition of a named property. For a deeply nested proof, the
frame remains three lines long and its highlighted line follows the reported column
on a long source line.

Illustrative presentation (the solver may choose different witness values):

```text
│  × Falsified · CliDemo.subtractionRoundTrip at 12:1 · 42ms
│    I found this property false.
│
│      11 │
│    > 12 │ #blaster (solve-result: 1) [subtractionRoundTrip]
│      13 │
│    Goal: ∀ (a b : Nat), a - b + b = a
│    Counterexample
│      a = 0
│      b = 1
```

`--counterexample=summary|full|raw|none` controls terminal detail. `summary` is the
default; `full` prints every witness value without clipping, `raw` labels and prints
the original solver values, and `none` skips model retrieval. `--no-counterexample` is
an alias for `none`. The last counterexample option on the command line wins.
JSON output keeps the existing raw `counterexample` array regardless of the
terminal presentation mode, except when retrieval is disabled. Complex SMT values
are shown as previews and identified as solver syntax in summary mode. The CLI does not
claim a Lean evaluation of the proposition from these strings. When optimization
reduces a property to `False`, it reports that there is no solver model; when model
retrieval is disabled or produces no usable values, it says so separately.

The aggregate report shows actual `valid`, `falsified`, and `undetermined` outcomes.
Test files may annotate deliberately false or unresolved properties with expected
results. These still have falsified or undetermined actual status and retain their
exit-code meaning in `lean-blaster check`; the expected count is shown separately.
`lake test` validates the repository's expected-result annotations as a test suite.

## Discover source sites

`lean-blaster discover FILE.lean` lists direct `#blaster` commands and `blaster`
tactic sites without elaborating the file, building project imports, or running Z3.
It loads parser syntax from already compiled imports when available, so project
notations such as `Recursor.any` can be parsed. Import syntax is cached across
files with the same import header. If compiled imports are unavailable, discovery
continues with Blaster's grammar and marks the partial result with
`discovery.importSyntax` warnings or `discovery.parse` errors. Build the missing
imports and retry for a complete inventory.
For an import-only umbrella it walks local source imports once, just as `check`
does by default. An empty discovery succeeds and reports zero sites.
`discover DIRECTORY` parses each source in the directory inventory once and emits
each site's location once per invocation, even when several umbrellas import that source.

Each site has a `kind` (`command` or `tactic`), optional source-qualified declaration
`name`, and the exact source `body`. For a tactic, `body` is its enclosing theorem,
example, or other declaration; for a command, it is the complete `#blaster`
command. `invocationRange` identifies the call and `bodyRange` identifies the
returned source text. Both ranges contain `start` and exclusive `stop` locations
with one-based line and column numbers.

`discover --json` emits `start`, optional `moduleStart` and `moduleComplete`, one
`discovery` event per site, diagnostics if parsing fails, and `complete` with
`discoveryCount` and `exitCode`. `discover --json-report` emits one object with a
`discoveries` array. This is a source scan: macro expansion, custom syntax defined
inside the file, conditional tactics, and elaboration can change which invocations
actually run. Use `check --json` for executed calls and their outcomes. Discovery
does not accept solver or `--decl` selection options.

## Agent report

`lean-blaster check FILE.lean --llm report.md` writes a Markdown snapshot for coding
agents. The path is relative to the current directory unless absolute. It may be
combined with `--json` or `--json-report`; those stdout formats keep their existing
meaning. The report is written through a temporary file and replaced only when
complete. A write failure is reported as a check error. The flag is available only
for `check`, and `.lean` output paths are rejected to protect source files.

The snapshot records the project root, Git revision and dirty state when available,
Lean and Z3 versions, effective CLI overrides, exit status, selected source count,
recorded call counts, trust statement, and a compact index of every result. Each
non-valid result includes its location, source excerpt, elaborated goal when
available, reason, raw counterexample values when available, and matching Lean
diagnostics. Routine unused-variable warnings are counted but omitted from detail.
Syntactic discovery counts and executions that occur inside Lake dependency builds
are not claimed as captured check results. The report is evidence for an agent to
inspect, not a reconstructed Lean proof or an automatically generated fix.

## Options and precedence

```sh
lean-blaster check Properties.lean --decl Demo.property --solver-timeout 30s
lean-blaster --json check Properties.lean --decl Demo.property
lean-blaster check Properties.lean --seed=0 --no-counterexample
lean-blaster check -- --filename-starting-with-dashes.lean
```

Explicit CLI solver options override source options; omitted options preserve source
settings. The default solver timeout remains unlimited. Positive whole seconds and
minutes are supported (`30s`, `2m`); `none` removes the limit. The limit applies to
each solver query, not elaboration or optimization. Unsupported precision is rejected.
Zero is a valid random seed. Counterexample retrieval is enabled unless disabled in
the source or through `--no-counterexample`.

`-v`/`--verbose` shows actual stages, timing, Lean information messages, and
unused-variable linter warnings. The normal terminal report omits routine Lean
information messages and unused-variable warnings; JSON output retains them.
The normal report also omits the tactic's duplicate falsification diagnostic
and per-tactic `blasterProven` warning. JSON retains them as `blaster.falsified`
and `blaster.trust`; verbose mode shows them. A single trust note remains at the
end of reports containing valid results. Other Lean warnings remain visible.
`--debug` enables additional diagnostic context. The CLI owns progress and
result rendering, so it suppresses the library's stdout-based profiling and SMT
dumping. Use existing Lean options
directly for raw SMT-query inspection until `inspect` and `export` are implemented.

## Voice and presentation

The voice follows the first-person compiler tradition exemplified by
[Elm's Compilers as Assistants](https://elm-lang.org/news/compilers-as-assistants).

- **I/me:** actions, findings, limitations: "I'm optimizing…", "I found a counterexample".
- **We/our:** occasional shared progress: "We're done…".
- State what happened, relevant evidence, and a concrete recovery action.
- Keep status rows compact. Avoid jokes, blame, canned apologies, and random copy variants.
- Never claim a timeout solely because an unknown result had a time limit configured.

`--theme dark|light` selects the agreed truecolor palette:

| Role | Dark | Light |
| --- | --- | --- |
| Identity / progress | `#C4B5FD` | `#6D28D9` |
| Source location / action | `#67E8F9` | `#0E7490` |
| Valid | `#86EFAC` | `#166534` |
| Undetermined / warning | `#FCD34D` | `#92400E` |
| Falsified / error | `#FDA4AF` | `#BE123C` |
| Secondary information | `#A1A1AA` | `#52525B` |

`--theme auto` uses truecolor when `COLORTERM` advertises it and `COLORFGBG` identifies
the background; otherwise it uses the terminal's semantic ANSI palette. Explicit
themes opt into truecolor. Text and symbols carry the same information without
color. Status columns align, with locations accented and timing/stage details muted.

`--color auto|always|never` is independent of progress. Auto mode honors nonempty
`NO_COLOR`, non-TTY output, and `TERM=dumb`; explicit `always` overrides color
detection. `--no-progress` removes live updates, `--ascii` replaces status symbols.
Redirected output is static. Progress appears on stderr and results on stdout.
The CLI never changes the terminal's background or font.
Live frames use the actual stderr terminal width, refreshed while running, with
`COLUMNS` as a fallback. Unicode display widths are respected. A shared output lock
keeps progress from interrupting completed result blocks.

## Structured output and exit codes

`--json` writes newline-delimited JSON events on stdout. Each event is one complete
JSON object followed by `\n`, and is flushed before the next check starts. This
lets a JSON-RPC server or editor extension consume results while Lean is still
working. The event stream contains:

| `event` | Contents |
| --- | --- |
| `start` | `command` and optional `file` |
| `moduleStart` | Imported source module about to be checked |
| `result` | One `result` object for each Blaster invocation |
| `discovery` | One `item` with source text and spans, for `discover --json` |
| `moduleComplete` | Imported module name and its outcome counts for `check`, or `discoveryCount` for `discover` |
| `diagnostic` | One `diagnostic` object for each reported diagnostic |
| `doctor` | Lean version and selected solver, for `doctor --json` |
| `complete` | Final `exitCode` and elapsed time; `check` adds outcome counts and interruption fields, while `discover` adds `discoveryCount` |

Every event has `schemaVersion: 1`. The stream ends with exactly one `complete`
event after normal completion, source errors, invalid arguments, or handled
interruption. A process crash can end the stream without `complete`; consumers
should treat that as an incomplete run. Results already emitted remain usable.
`moduleComplete` counts include nested modules, so consumers should use `result`
events or the final `complete` counts for run-wide totals.
`--json-report` preserves the previous single-object report after completion.
Neither mode writes ANSI escapes or progress frames to stdout; source and build
output remains on stderr. A `result` object contains:

- `property`, `invocation` (`command`, `tactic`, `declaration`), and source `location`;
- `status` (`valid`, `falsified`, `undetermined`, `error`, `skipped`), `origin`,
  and `expectedStatus` when the source requests falsified or undetermined;
- `elapsedMs`, `solverTimeoutSeconds`, the input `goal`, raw `counterexample` strings,
  and optional `reason`. `skipped` denotes an explicitly selected declaration that
  could not safely be checked after elaboration failed.

Single-object reports also include `diagnostics`, `trust`, `interrupted`, `signal`,
and `exitCode`. Consumers should tolerate additional fields. Usage errors produce
stream events with `--json` and one report with `--json-report`. Help and version
requests intentionally print text.

| Exit | Meaning |
| --- | --- |
| 0 | All captured checks valid, or doctor successful |
| 1 | At least one falsified result |
| 2 | Invalid invocation or options |
| 3 | At least one undetermined result, with none falsified |
| 4 | File, Lean elaboration, translation, or solver failure |
| 130 | Interrupted with SIGINT (Ctrl-C) |
| 143 | Interrupted with SIGTERM |

Operational/source errors take precedence over falsification, which takes precedence
over undetermined. A falsified tactic has a typed diagnostic tag and is classified
as falsification. A tactic leaving an incomplete Lean proof still produces Lean's
source error; capturing its unknown result does not admit or repair the proof.

SIGINT and SIGTERM preserve completed results and produce a final `complete` event
in streaming mode, or one report with `--json-report`, with `interrupted: true` and
the signal number. The CLI freezes reporting,
stops and reaps supervised solvers, and exits promptly even during blocking source
IO. On POSIX, supervised commands use separate process groups so cancelling a Lake
dependency build also stops its solver descendants. The native adapter redirects
OS stdout as well as Lean's stream, keeping inherited subprocess output on stderr.

If elaboration fails, selections which were not reached are explicitly marked
`skipped` ("Not checked"), and missing declaration names are diagnosed. The CLI does
not solve new declarations using Lean's error-recovery environment. Skipped
selections produce exit 4 rather than silently disappearing from a batch report.

Valid results are **not reconstructed Lean proofs**. The existing tactic uses
`Blaster.Tactic.blasterProven`, including optimizer-only success. The report retains
that trust boundary as a terminal note and structured warning. Raw solver values
are not claimed to be decoded Lean values. No new axioms or admissions are introduced.

## Validation

```sh
lake build lean-blaster
python3 scripts/fetch_z3.py
python3 scripts/test_cli.py
python3 scripts/test_install_cli.py
python3 scripts/fetch_z3.py --destination .lake/toolchains/z3-5.3.2
PATH="$PWD/.lake/toolchains/z3-5.3.2:$PATH" make check_all
```

The integration checks cover commands and tactics, selection without duplicate solver
runs, optimizer/SMT origins, counterexamples, unresolved results, malformed flags,
source errors, JSON isolation, monochrome output, and bundled solver selection.
Installation checks run outside the checkout without Lean, Lake, or Z3 on `PATH`,
including dependency discovery in a separate Lake project and preservation of an
unrelated existing command.

Local validation on macOS arm64 with Lean 4.24.0 and Z3 5.3.2 passed the executable
build, all 22 CLI integration checks, and all six installation checks. Coverage
includes inherited subprocess output, SIGINT/SIGTERM, blocking source IO, narrow
Unicode terminals, light/dark palettes, missing/stale imports, single elaboration
of the selected file, and cancellation during a dependency build. Linux and macOS
CLI CI jobs run independently of the full SMT suite.
The clean library check also passed. The full test build was stopped at 733/747 jobs after
the existing `Tests/Smt/SmtNat/SmtNatMod.lean` module spent more than six minutes
solving nonlinear modulo queries without a timeout. The full suite therefore
remains incomplete; this does not establish a regression from the base branch.
Keep the solver outside `.lake/build` for `make check_all`, which cleans that directory.

## Following milestones

1. Richer reason-unknown reporting.
2. `inspect` and `export`, and shell completion.
3. Structured BMC and k-induction results with explicit analysis bounds.
4. Relocatable release bundles including required Lean runtime/module artifacts,
   followed by signed platform packages and release automation.
5. Optional interactive watch mode once the ordinary CLI contract is stable.
