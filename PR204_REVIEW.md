# PR #204 review package

## Scope and starting state

The local branch is ready for human review. This is not a merge approval.
No confirmed defect remains from the three requested risk checks.
The original six cvc5 counterexample inputs remain a validation gap.

- Branch: `feat/cvc5-concurrency`.
- Starting HEAD: `7bb57b597d62559530be026a33cfd63621082f3d`.
- Starting tree: `081e6ed3b85c9d0970dc1bffc97a2fdbf5a8be21`.
  This is also the tree of `9f44746`.
- PR target: `feat/cvc5-backend`, confirmed from the GitHub API.
- Target HEAD and merge base: `6dedd0fb38cd57019d9288527dc16b0a108ecd81`.
- At the start, the remote PR still pointed to `75c4660`.
  The owner must publish the local branch to update that PR.
- No push, merge, history rewrite, or PR comment was made.
- No `AGENTS.md` or `CLAUDE.md` was found in the repository.
  No `AGENTS.md` was found in its parent directories.

The local deletion of `COUNTEREXAMPLE_SPIKE.md` is unchanged and not staged.
The untracked `WATCHDOG.yml` and `demo/` files are unchanged.

The complete PR adds `single`, `first`, and `agree` execution policies over
one shared SMT query. It adds per-solver sessions, result diagnostics, and
restart/replay for incremental checks. `single` remains the default.
Agreement compares solver verdicts. It does not add a checked-proof guarantee.

This task does not add process groups, a native helper, solver build tools,
CI jobs, runtime options, or environment variables. Stock solver flags,
SMT encoding, proof handling, and optimization rules are unchanged.

## Separate changes

| Commit | Change | User-visible effect |
|---|---|---|
| `4b8fd12` | Stop agreement checks after an execution failure. | A failed peer cannot leave `agree` waiting for an unlimited check. |
| `aa2404b` | Compare agreement verdicts before model requests. | A model wait cannot hide a known disagreement. |
| `42eda1f` | Limit each optional model response read to 5000 ms. | A stalled reply gives incomplete evidence, not loss of `Falsified`. |
| `40a9b4d` | Separate outcome collection from agreement decisions. Remove unused response helpers. | No intended behavior change. |
| `37c85c1` | Test option rejection without exact message text. | No runtime change. |
| `a235b15` | Remove duplicate single-session timeout test calls. | Keep both reader paths and both agreement orders. |

The removed helpers are `getErrorMsg`, `dropSexp`, and
`unwrapGetValueOutput`. Repository reference searches found no remaining
callers. The active model parser remains unchanged.

Five seconds is a fixed, local limit for optional response reads. It prevents
an unbounded wait after `sat` without a new public option or transport system.
A valid response that takes longer can lose counterexample detail. The verdict
remains `Falsified`. The limit starts after submission. It does not bound
submission, parsing, value expansion, all model requests together, or shutdown.
The existing cleanup path stops the child before the response task is joined.

## Reproductions and regression tests

All three defects were reproduced against the restored source before edits.
The saved `risks-before.log` has six watchdog failures and exit code 1.
The same paths pass after the fixes.

| Finding | Affected path | Controlled reproduction | Final check |
|---|---|---|---|
| Agreement waits after failure | `collectAgreementOutcomes`, formerly in `runAgreementCheck` | One child closes stdout with `CHECK_FAILURE`; its peer never returns a verdict. No check timeout is set. | `testAgreementFailure`, both solver orders. |
| A model hides disagreement | `runAgreementCheck` | One child returns `sat`, then stalls on a model request. Its peer returns `unsat`. | `testDisagreementBeforeModel`, both orders. No model request is sent. |
| Optional model read has no deadline | `requestModelResponse` and its former `awaitTaskCancelable` call | A child returns `sat`, then never answers `get-model` or `get-value`. | `testModelFailure`, both reader paths. `Falsified` and timeout details remain. |

Run the committed regression module with an external 90-second limit:

```sh
python3 -c 'import subprocess; subprocess.run(["lake", "env", "lean", "Tests/Smt/ResponseLifecycle.lean"], check=True, timeout=90)'
```

The module uses command-readiness files. Its watchdog stops direct children
if a response does not finish. Each case checks that its children are gone.
The production timeout path joins its reader task. No external test deadline
was reached in the final runs.

The module also checks EOF, malformed value replies, and matching falsified
results when either solver times out during evidence collection. The complete
peer value `x: 42` must remain available in both orders.

An additional direct child that ignored SIGTERM also stopped correctly.
That suspected shutdown defect was not reproduced. Lean 4.24.0's native POSIX
`Child.kill` uses SIGKILL. No general process-tree shutdown bound is claimed.

## Reviewer guide

1. Read `Blaster/Command/Options.lean`, `Syntax.lean`, and `Tactic.lean`.
   Check mode defaults, option conflicts, and the unchanged option precedence.
2. Read `SolverVerdict`, `SolverOutcome`, and `aggregateAgreement` in
   `Blaster/Smt/Env.lean`. Verdicts, execution failures, and evidence are separate.
3. Read `SolverSession`, `SolverRecord`, and `SmtEnv` in
   `Blaster/Optimize/Env.lean`. `sessions` owns live children. `emitProc` is only
   the temporary command target. Records survive session retirement.
4. Read `sendCommandToSession`, `trySubmitCommand!`,
   `spawnAndInitializeSolver`, and `ensureConfiguredSessions` in `Smt/Env.lean`.
   Follow the canonical query into each session and through restart/replay.
   `Blaster/Smt/EmitCommand.lean` writes to the selected session.
5. Read `runSingleCheck`, `runFirstCheck`, `collectAgreementOutcomes`,
   `requireAgreement`, and `runAgreementCheck`. `first` selects a decisive
   verdict before evidence. `agree` rejects failures and mismatched verdicts
   before evidence. Matching falsified results keep the existing quality policy.
6. Read `requestModelResponse`, `awaitModelResponse`, `attachCounterexample`,
   and the existing retirement functions. Follow the timeout through cleanup
   and reader-task join. Model failure must not become a verdict failure.
7. Read `Blaster/Smt/Translate.lean` and `Blaster/StateMachine/` for owner
   boundaries and incremental checks. Concurrent startup still requires both
   solvers. `only-optimize` remains solver-free.
8. Read `Tests/Smt/ResponseLifecycle.lean`, `CrashLifecycle.lean`,
   `SolverOutcomePolicy.lean`, `ConcurrentSolvers.lean`, and `ConcurrentDump.lean`.

## Test results

All listed baseline and final commands completed with exit code 0, except the
intentional pre-fix reproductions and expected CLI rejection cases.
Shared build-cleaning targets ran one at a time.

| Command | Baseline | Final |
|---|---|---|
| `lake build Blaster` | Pass, 71.50 s | Pass, 0.51 s after the final edits |
| `make check_all` | Not run as an aggregate; component checks below | Pass, 212.90 s |
| `make test-pure` | Pass, 15.82 s | Pass within `make check_all` |
| `make test-z3` | Pass, 89.52 s | Pass within `make check_all` |
| `make test-cvc5` | Pass, 136.87 s | Pass, 140.48 s |
| `make test-all-solvers` | Pass, 74.92 s | Pass, 110.18 s |
| `PATH="$PWD/.blaster/cvc5-parity-20260922/solvers/floor:$PATH" make test-cvc5-floor` | Pass, 4.60 s | Pass, 4.38 s |
| `lake env lean Tests/Smt/ResponseLifecycle.lean` | Six failures before fixes, in the temporary reproduction module | Pass, 22.85 s for the final module |
| `BLASTER_TIMEOUT=30 lake env lean Tests/Smt/CounterexampleSpike.lean` | Not run separately | Pass, 3.01 s |

`check_all` includes a clean Blaster compilation check, `test-pure`, and
`test-z3`. Those final tiers were not run again as separate Make targets.
The diagnostic spike is excluded by the restored aggregate target, so it was
run separately. No new test exclusion or weaker solver expectation was added.

Twenty-three CLI smoke cases also passed their expected contracts. They cover
single-backend isolation, solver-free paths, invalid options before startup,
`gen-cex: 0`, first-mode selection after unknown or failure in both orders,
first-mode model timeout in both orders, and all nine agree verdict pairs.
Expected rejection cases exited 1. Successful cases exited 0. All recorded
fake-solver PIDs were gone after each command.

Existing regression suites cover cancellation, incremental checks,
restart/replay, version checks, option precedence, saved transcripts, and
ordinary solver output. Focused policy, lifecycle, and transcript checks also
passed during the separate fixes and cleanup.

Tools used:

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- Lake `5.0.0-src+797c613`, from `/Users/rileykilgore/.elan/bin/lake`.
- Z3 4.15.4, `/opt/homebrew/bin/z3`.
- Stock cvc5 1.3.4, git `f3b21c4`, `/opt/homebrew/bin/cvc5`.
- Floor cvc5 1.2.1, `.blaster/cvc5-parity-20260922/solvers/floor/cvc5`.
- Host: macOS, arm64. Linux and Windows execution was not run here.

No `BLASTER_*`, `LEAN_*`, `CVC5_*`, or `Z3_*` setting was present at the start.
The Makefile sets `LEAN_NUM_THREADS=5` and the backend-specific settings.
Solver tiers use `BLASTER_TIMEOUT=30`; strict cvc5 tiers use
`BLASTER_STRICT_CVC5_RESULTS=1`. The floor target removes `BLASTER_TIMEOUT`.
CLI smoke cases used temporary PATH wrappers and the `LEAN_PATH` from
`lake env`. They removed solver and timeout overrides.

Local evidence is in `.blaster/review-204-20260923/`. It is not tracked.
`results.json` records exact commands, exit codes, durations, and environment
overrides. `versions.json` records full banners, paths, and binary hashes.
The folder includes baseline and final logs, reproduction output, input
records, agreement artifacts, and the two review diffs. Temporary executable
probes were removed. Committed regressions remain in `Tests/Smt/`.

## External cvc5 checks and remaining work

The available patched binary was used without a rebuild or new build system:

`.blaster/cvc5-parity-20260922/verified-pair/patched/build-parity/bin/cvc5`

Its SHA-256 matches the saved build record:
`232e538a0a3e9c76813b5d6bb4a098e45f848ac558f310431d096bcab7ccf83b`.
The matched control binary also matches its saved hash.
The recorded source base is `67954d09dcc955eba282155766cf452fc0ff1bd6`.
The patch heads are:

- PR #1: `6eaca4bf1303a69c2c3aaddc0e50b1bf7d3df6e7`.
- PR #2: `18ed35b885c1655520e2ffe9d1c143017ce907d9`.

PR #1 preserves recursive definitions while simplifying FMF aliases.
PR #2 adds macro inference for fixed ground arguments.
The version banner was not used as evidence that these patches were present.
Build provenance is recorded evidence, not a claim of byte-reproducible builds.

Five exact upstream inputs passed with all expected values and verdicts:

| Input | Checked values |
|---|---|
| `rec-alias-preprocess.smt2` | `witness=(leaf 0)`, both predicates `true` |
| `macros-ground-argument.smt2` | identity application `17`, other application `99` |
| `macros-ground-full-core.smt2` | both queried terms `8` |
| `macros-ground-multiple-arguments.smt2` | `205`, `99`, `88` |
| `macros-ground-redefine.smt2` | pairs `7/99`, `8/55`, `9/44` across scopes |

Each input used its own `COMMAND-LINE` arguments, plus `--tlimit-per=3000`.
An external 20-second limit covered each invocation. The matched control
returned `unknown` for the relevant satisfiable checks in all five inputs.
Its values after `unknown` are not treated as validated counterexamples.
Exact commands, input hashes, expected output, and returned output are in
`patched-witness-results.json`. Input copies are in `solver-inputs/`.
These flags were not added to the Blaster stock-cvc5 configuration.

**Confirmed blockers from this task:** none remain in the three requested
paths. A suspected K-induction stale-flag issue was also checked and rejected:
only the continuing path needs to deactivate the flag, and it does so.

**Validation gap:** the exact six original Lean-blaster counterexamples and
their expected reconstructed values were not found in the linked discussions
or available local records. The five upstream inputs above are not substitutes.
Do not claim that all six cases are fixed. Obtain the original Lean inputs or
SMT transcripts and expected values before making that claim.

**Review limits:** this task does not establish a bound for blocked command
submission, parsing/value expansion, graceful shutdown, or descendants that
retain pipes. These are outside the new response-read limit. No general
process-management change was made.

**Existing coverage limit:** the restored PR changes three Issue24 cases to
translation-only checks in `Tests/FixedIssues/Issue24.lean`. This task leaves
those checks unchanged. A green suite does not establish their solver results.
A separate decision is needed before adding new solver-result expectations.

Optional later work is broader platform testing and a separate review of
transport/shutdown limits. Neither is hidden inside this cleanup.

## Draft PR description

### Purpose

Add concurrent Z3 and cvc5 execution over one shared SMT query. Keep the
selected single-backend path as the default. Make result selection and session
handling clear for maintainers.

### Scope

- `single` runs only the selected backend.
- `first` uses the first decisive verdict. Unknown and execution failure do not
  beat a pending decisive result. Evidence quality does not choose the winner.
- `agree` compares verdicts, not counterexample text. Disagreement and execution
  failure remain errors. Both solvers are required at startup.
- Keep cancellation, session cleanup, incremental checks, and restart/replay.
- Stop agreement checks after a peer fails. Compare verdicts before models.
- Give each optional model response read a five-second limit. Keep `Falsified`
  if evidence fails. Preserve the existing evidence-selection policy.
- Separate behavior fixes from code cleanup. Remove unused response helpers.

### Tests

Baseline and final build, pure, Z3, cvc5, all-solvers, and cvc5 1.2.1 floor
checks pass locally. Controlled pre-fix cases fail, then pass after each fix.
The final regression module checks both agreement orders and child cleanup.
CLI smoke checks cover all agree verdict pairs, isolation, option conflicts,
no-model operation, and first-mode failure order.

### Risks and limits

The model limit bounds response reads, not full processing or shutdown.
Slow model replies can lose optional detail without losing `Falsified`.
Agreement is not a new checked-proof guarantee. Stock solver flags are unchanged.
The original six external counterexample reports are not validated here.
No process framework, solver build pipeline, or new runtime option is added.

### Related work

- Main PR: https://github.com/input-output-hk/Lean-blaster/pull/204
- Backend: https://github.com/input-output-hk/Lean-blaster/pull/145
- cvc5 patches: https://github.com/RSoulatIOHK/cvc5/pull/1 and https://github.com/RSoulatIOHK/cvc5/pull/2
- Separate SMT emission work: https://github.com/input-output-hk/Lean-blaster/issues/231 and https://github.com/input-output-hk/Lean-blaster/pull/234

The SMT emission work is not included in this cleanup.
