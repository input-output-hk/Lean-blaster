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
```

`make install` builds the executable, installs its own compiled Blaster libraries and
Z3, and creates `~/.local/bin/lean-blaster`. That directory must be on `PATH`; the
installer tells you if it is missing. Shell profiles are not edited. A custom prefix
is available through `python3 scripts/install_cli.py --prefix /your/install/location`.
An existing unrelated command is preserved. Reinstalling switches the command to a
finished release directory and preserves resources used by already-running processes.

The command locates the installed files through its resolved executable path, so
launching it through the PATH symlink works from other directories. It remembers
the matching Lean toolchain instead of using whichever Lean happens to be active
in the current shell. For a Lake project, it discovers compiled dependencies
automatically from the input file's location, falling back to the current directory.
You do not need to prefix commands with `lake env` or point into `.lake/build/bin`.
Projects must have their dependencies built and use a compatible Lean toolchain.

Try `check examples/Properties.lean` for a valid tactic result, a counterexample,
and an unresolved optimizer-only check. This demonstration intentionally exits 1
because one property is false. Select just the valid example with
`check examples/Properties.lean --decl CliDemo.reflexive`.

The fetch script installs the pinned official **Z3 5.3.2** release privately under
`.lake/build/libexec/lean-blaster/`. Its platform archive must match the SHA-256 in
`scripts/z3-release.json`. Binaries and downloads remain ignored build products.
The archive's MIT license is retained alongside the solver. The script does not
replace the system's Z3 installation or modify shell configuration.

Solver selection is `--solver PATH`, then the installation's private solver, then
`z3` on `PATH`. A broken explicit or bundled solver is reported rather than silently
switching versions. `doctor` reports the selected path, source, and actual version.

The installer keeps private releases under `~/.local/share/lean-blaster/releases/`.
Each contains `bin/lean-blaster`, compiled Blaster modules in `lib/lean/`, and the
solver and required runtime libraries in `libexec/lean-blaster/`, including
`LICENSE-Z3.txt`, `release.json`, and the Lean toolchain's `runtime.json`. Downloads are
pinned for macOS, Linux, and Windows on arm64 and x64; the Linux archives require
their named glibc version. Only the host platform has been exercised locally.

This milestone still uses an installed Lean toolchain and compiled project
dependencies. A fully relocatable release that also packages Lean's runtime
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

`-v`/`--verbose` shows actual stages and timing; `--debug` enables additional
diagnostic context. The CLI owns progress and result rendering, so it suppresses the
library's stdout-based profiling and SMT dumping. Use existing Lean options directly
for raw SMT-query inspection until `inspect` and `export` are implemented.

## Voice and presentation

The voice follows the first-person compiler tradition exemplified by
[Elm's Compilers as Assistants](https://elm-lang.org/news/compilers-as-assistants).

- **I/me:** actions, findings, limitations: "I'm optimizing…", "I found a counterexample".
- **We/our:** occasional shared progress: "We're done…".
- State what happened, relevant evidence, and a concrete recovery action.
- Keep status rows compact. Avoid jokes, blame, canned apologies, and random copy variants.
- Never claim a timeout solely because an unknown result had a time limit configured.

Identity uses the terminal's magenta role; green denotes valid, red denotes falsified
or operational failure, and yellow denotes undetermined or warning. Text and symbols
carry the same information without color. ANSI roles inherit the user's light/dark
terminal palette. The proposed lilac/cyan truecolor palette remains a future preset.

`--color auto|always|never` is independent of progress. Auto mode honors nonempty
`NO_COLOR`, non-TTY output, and `TERM=dumb`; explicit `always` overrides color
detection. `--no-progress` removes live updates, `--ascii` replaces status symbols.
Redirected output is static. Progress appears on stderr and results on stdout.
The CLI never changes the terminal's background or font.

## Structured output and exit codes

`--json` produces one versioned JSON object on stdout, with no ANSI escapes or
progress frames. Source output remains on stderr. The result array contains:

- `property`, `invocation` (`command`, `tactic`, `declaration`), and source `location`;
- `status` (`valid`, `falsified`, `undetermined`, `error`) and `origin`;
- `elapsedMs`, `solverTimeoutSeconds`, the input `goal`, raw `counterexample` strings,
  and optional `reason`.

Reports also include `diagnostics`, `trust`, and `exitCode`. Consumers should tolerate
additional fields. Doctor reports contain `leanVersion`, selected `solver`, and
diagnostics. Usage errors also produce JSON when `--json` is requested. Help and
version requests intentionally print text.

| Exit | Meaning |
| --- | --- |
| 0 | All captured checks valid, or doctor successful |
| 1 | At least one falsified result |
| 2 | Invalid invocation or options |
| 3 | At least one undetermined result, with none falsified |
| 4 | File, Lean elaboration, translation, or solver failure |

Operational/source errors take precedence over falsification, which takes precedence
over undetermined. A falsified tactic has a typed diagnostic tag and is classified
as falsification. A tactic leaving an incomplete Lean proof still produces Lean's
source error; capturing its unknown result does not admit or repair the proof.

Valid results are **not reconstructed Lean proofs**. The existing tactic uses
`Blaster.Tactic.blasterProven`, including optimizer-only success. The report retains
that trust boundary and the tactic's existing warning. Raw solver values are not
claimed to be decoded Lean values. No new axioms or admissions are introduced.

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
build, all 16 CLI integration checks, and all four installation checks. The clean
library check also passed. The full test build was stopped at 724/738 jobs after
the existing `Tests/Smt/SmtNat/SmtNatMod.lean` module spent more than five minutes
solving nonlinear modulo queries without a timeout. The full suite therefore
remains incomplete; this does not establish a regression from the base branch.
Keep the solver outside `.lake/build` for `make check_all`, which cleans that directory.

## Following milestones

1. Richer reason-unknown reporting, cancellation, and progress coordination.
2. `inspect` and `export`, shell completion, and the truecolor palette preset.
3. Structured BMC and k-induction results with explicit analysis bounds.
4. Relocatable release bundles including required Lean runtime/module artifacts,
   followed by signed platform packages and release automation.
5. Optional interactive watch mode once the ordinary CLI contract is stable.
