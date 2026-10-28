# FFM-10 ticket report and job summary

**Current project gates pass (2026-10-28 refresh):** `make check_blaster` passed
with the required Z3-only PATH. `make check_tests` failed once in unchanged
`Tests.Smt.CrashLifecycle`, then passed on its one permitted full-target rerun
in this job, including both pure and Z3 tiers. The unchanged-test flake rule
therefore applies; no test, expected result, implementation or timeout was
changed to obtain that pass. Exact current evidence follows in the refresh
section at the end of this report.

The implementation and earlier validation record below were already present in
the supplied checkout. This refresh preserves them, including the earlier job's
two failed project-test runs; it does not relabel those historical runs as passes.
The refresh changes only this report, not protected scripts, tests, workflows,
root Lake files, toolchain pins, Make recipes or the child implementation.

## Change

Added an isolated `BlasterFFTests` child package, deterministic pure discovery,
additive Make gates, a proposed finite-fields workflow, and the ownership matrix.
The child depends only on local `..` Blaster and inherits Lean 4.24.0. Its committed
Lake manifest records that local dependency, avoiding first-build generation of
a redundant child toolchain file. `TestsFF` uses `.andSubmodules` for root and
recursive module discovery. Four initial native cases exercise two UNSAT queries
and two SAT/get-value queries, validating the field-model equation modulo seven.
They are capability observations, not Lean reconstruction or proof export.

`run_pure_tests.py` discovers all pure FF sources, checks exact individual import
registration, clears only their own output files, removes solver/timeout/strictness
overrides, disables artifact reuse and requires fresh compilation coverage.
`test-pure`, `test-cvc5` and `test-all-solvers` gain prerequisite-only extensions.
All old Make recipe text is retained. `.NOTPARALLEL:` serializes shared-output
suites in a single Make invocation, including `make -j`.

`ff-stage` uses the unchanged FFM-09 fetch-only and offline-check interfaces.
`test-cvc5-ff` consumes only the offline-verified staged executable via an absolute
`BLASTER_FF_CVC5`, never adding it to ordinary PATH. The standalone baseline stays
outside the live tree and runs from the root with ordinary cvc5.

No existing Tests, scripts, workflows, root Lake declarations or toolchain pins
were edited. The only protected-namespace addition is
`scripts/finite_fields/run_pure_tests.py`. No new pure module/import was needed;
all five parent modules were already individually registered. Nothing was created
under `.github/`. `docs/finite-fields/finite-fields.workflow.yaml` is a proposal
for Riley's manual handoff. `test-ff-verified` is reserved only in documentation.

## Environment

Native Linux arm64 worker; root and child `lake env lean --version` report Lean
4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. `lake --version` reports
Lake `5.0.0-src+797c613`. No child `lean-toolchain` is retained.

`cvc5 --show-config` reports ordinary image cvc5 1.4.1, git `2b2e844`:

```text
package       : cvc5
version       : 1.4.1
scm           : git 2b2e844 on branch HEAD
safe-mode     : no
stable-mode   : no
debug code    : no
statistics    : yes
tracing       : no
muzzled       : no
assertions    : no
coverage      : no
profiling     : no
asan          : no
ubsan         : no
tsan          : no
competition   : no
portfolio     : yes
cln           : yes
glpk          : yes
cryptominisat : no
gmp           : no
kissat        : no
poly          : yes
cocoa         : yes
normaliz      : yes
editline      : yes
```

CoCoA presence in the ordinary worker binary is recorded, not a failure. The
standalone baseline uses no FiniteField sorts. No alternate ordinary cvc5 or
support-floor executable was downloaded. Only the approved solving artifact was
acquired by `make ff-stage`; it is separate from the image binary.

## Validation commands and outcomes

Commands run from the repository root unless a working directory is stated.

| Command | Outcome |
| --- | --- |
| `make ff-stage` | PASS. Pinned arm64 archive/executable and configuration verified; four protocol cases passed; setup, solving and model required capabilities passed. Proof export remains deferred, not required. |
| `make test-cvc5-fin-baseline` | PASS with image ordinary cvc5 1.4.1, default Make timeout 30; parent Blaster built, standalone Lean assertions passed. |
| `make test-cvc5-ff` | PASS after fixing a new Lean identifier syntax error; four live cases executed, root and Capability freshly built, complete live source coverage. Offline checks passed before compilation. |
| `env PATH=/home/agent/.elan/bin:/usr/bin:/bin BLASTER_SOLVER=invalid BLASTER_TIMEOUT=invalid BLASTER_STRICT_CVC5_RESULTS=invalid python3 scripts/finite_fields/run_pure_tests.py` | PASS, 5/5 modules freshly compiled. Neither `z3` nor `cvc5` exists on this PATH; invalid inherited overrides were cleared. |
| `lake env lean --version` (cwd `ff-tests/`) | PASS, inherited Lean 4.24.0; no child toolchain file. |
| `env -u BLASTER_FF_CVC5 lake env lean TestsFF/Capability.lean` (cwd `ff-tests/`) | Expected failure, exit 1: explicit verified solver required. |
| `BLASTER_FF_CVC5=cvc5 lake env lean TestsFF/Capability.lean` (cwd `ff-tests/`) | Expected failure, exit 1: PATH fallback forbidden. |

The required library check passed (183 build jobs and complete source coverage):

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

It reported `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.

The required tests command was run twice, unchanged:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both invocations exited 2. Their nested `make test-pure` passed, including fresh
5/5 FF coverage and the unchanged `Tests.Pure` recipe. Their nested
`make test-z3` failed at `Tests.Smt.CrashLifecycle`. The execution service truncated
the middle of both full logs before retaining them, so the precise inner assertion
diagnostic is unavailable; the failing module and final exit status are retained.
No further success-chasing rerun, test edit, timeout change, expected-result
weakening or gate waiver was applied. Resolving this repeated existing-test
failure is a prerequisite to acceptance.

The strict ordinary suite passed with the image's cvc5 1.4.1 (671 build jobs),
including the added baseline before the unchanged clearing recipe:

```sh
bash -o pipefail -c 'make BLASTER_TIMEOUT=120 test-cvc5 2>&1 | tee .artifacts/ffm-10-cvc5.log'
```

Existing per-test allowed-cvc5 outcomes remain unchanged. The log is a local,
ignored artifact, not an additional committed report or solver input.

The cross-backend suite passed (698 build jobs), including the baseline,
concurrency tests and unchanged complete-root-source coverage:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin" bash -o pipefail -c 'z3 --version && cvc5 --version && make test-all-solvers 2>&1 | tee .artifacts/ffm-10-all-solvers.log'
```

The versions printed were Z3 4.15.2 and cvc5 1.4.1. No staged FF directory was on
PATH. The unchanged all-solvers recipe removed `BLASTER_TIMEOUT` itself. This
passing different target does not waive the repeated `check_tests` failure.

`make -j4 test-pure test-cvc5-fin-baseline test-cvc5-ff` also passed. Its output
shows sequential execution: pure discovery (55 own generated files removed,
5/5 modules freshly compiled), unchanged pure clearing/build, ordinary baseline,
then offline verification and four live cases. The final live tree contained only
the permanent Capability module and root; the temporary discovery module was gone.

Implementation smoke checks also passed:

- Thirteen Python API checks in an isolated temporary directory: missing/empty
  discovery, nested discovery, missing/duplicate/stale registration, nested
  comments, invalid module paths, exact cleanup preserving siblings and nested
  modules, missing/zero coverage, fresh-versus-replayed log evidence, and cleared
  solver overrides. All temporary files were removed.
- A temporary independent Lake package executed a newly discovered nested pure
  module with `run_build`; changing its assertion to `6 + 1 = 8` produced Lean
  exit 1, which the runner propagated. The temporary package was removed.
- `make test-cvc5-ff` with temporary unimported
  `TestsFF/DiscoverySmoke/Nested.lean` freshly built that module and printed its
  execution marker, alongside all four capability cases and the root. This proves
  recursive glob discovery without root/import/runner/workflow edits. The source
  was removed afterward.
- `Bun.YAML.parse` parsed the proposed workflow: pull request, integration-branch
  push and manual triggers; native linux-arm64 and linux-x86_64 matrix entries.
  Parsing is not a GitHub Actions execution claim.
- An offline probe against an empty temporary artifact root rejected missing
  `solving/metadata.json` with exit 1; it did not fall back to ordinary PATH.

The first live build rejected the newly introduced reserved Lean identifier
`prefix`. Renaming that local variable to `expectedSetup` fixed compilation; no
expected result was changed. First-time Lake resolution generated a redundant
child toolchain file; it was removed, and the local-only child manifest is
retained so clean checkouts inherit the unchanged parent toolchain.

## Public CI evidence and remaining scope

Observed [PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412) head
`3c871a0458d939552f02fc7afb637119f1c54251` before this ticket is published.
[Check-run API](https://api.github.com/repos/input-output-hk/Lean-blaster/commits/3c871a0458d939552f02fc7afb637119f1c54251/check-runs)
reports all four existing lanes successful:

- [solver tests (cvc5-1.2.1)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40597317426/job/122516401425): success.
- [solver tests (z3)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40597317426/job/122516401342): success.
- [solver tests (cvc5)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40597317426/job/122516401278): success.
- [solver tests (all-solvers)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40597317426/job/122516401120): success.

These are **pre-ticket** results, not evidence that the added baseline ran in CI.
For this ticket's eventual pushed head, `solver tests (cvc5)` non-CoCoA baseline,
`solver tests (cvc5-1.2.1)` floor, and x86_64 ordinary coverage are **pending**.
The worker cannot execute those environments and did not provision replacements.
The installed ordinary ci-linux pin is still 1.3.4; Riley's approved post-M1 move
to 1.4.1 remains pending. Both proposed finite-field workflow jobs are **pending**
maintainer installation and CI execution; only native arm64 FF execution is
claimed here. Publication, head-specific CI acceptance and final signoff remain
with Riley/the stack.

## Validation refresh — 2026-10-28

### Scope and environment

All requested implementation files already existed in the supplied checkout.
Inspection confirmed recursive `.andSubmodules` child globs, the local root
dependency, nonempty pure discovery and fresh coverage, prerequisite-only
ordinary gate extensions, four checked native cases, and the documentation-only
workflow handoff. They were retained unchanged. This job updates this report
with new execution evidence rather than recreating the protected runner.

`cvc5 --show-config` again reports image cvc5 **1.4.1**, revision **2b2e844**,
and **cocoa: yes**; its complete configuration matches the Environment section
above. `lake --version` reports Lake `5.0.0-src+797c613` / Lean `4.24.0`.
`lake env lean --version` from `ff-tests/` confirms inherited Lean `4.24.0`,
commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, native aarch64.
No other ordinary cvc5 or floor binary was acquired.

### Current command evidence

Commands ran from the repository root unless noted. Clearing/build suites ran
sequentially; acquisition did not alter any ordinary solver installation.

| Command | Current outcome |
| --- | --- |
| `make ff-stage` | PASS; fetched the approved arm64 solving profile into `.artifacts/finite-fields`, then verified hashes/configuration and all four required protocol cases offline. |
| `env PATH=/home/agent/.elan/bin:/usr/bin:/bin BLASTER_SOLVER=invalid BLASTER_TIMEOUT=invalid BLASTER_STRICT_CVC5_RESULTS=invalid python3 scripts/finite_fields/run_pure_tests.py` | PASS; 5/5 modules freshly compiled. `shutil.which` returned `None` for both solvers on that exact PATH. Invalid inherited overrides did not reach the pure build. |
| `make test-cvc5-fin-baseline` | PASS with image ordinary cvc5 1.4.1 and Make's unchanged default timeout 30. No live child library was built by this target. |
| `make test-cvc5-ff` | PASS; offline verification passed, `TestsFF.Capability` reported **4 live finite-field cases**, root and capability module freshly compiled, complete child-source coverage. |

The exact required project build command passed, with 183 build jobs and
complete Blaster source coverage:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

The required project-test command used the same pinned-only PATH. The first
invocation failed; its single full-target rerun passed. Output was retained with
`tee` under `bash -o pipefail` so failure status was not hidden:

```sh
bash -o pipefail -c 'PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests 2>&1 | tee .artifacts/ffm-10-check-tests-refresh.log'
bash -o pipefail -c 'PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests 2>&1 | tee .artifacts/ffm-10-check-tests-rerun.log'
```

Both printed `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version **4.15.2**.
The first exited 2 during the unchanged `Tests.Pure` recipe after the dedicated
FF corpus had passed. The retained diagnostic at `CrashLifecycle.lean:597` was:

```text
already-exited solver diagnostics were lost: z3 solver failure:
solver=z3; stage=check submission; command=(check-sat);
response=IO error while executing (check-sat): resource vanished
(error code: 32, broken pipe); elapsed=0ms
Solver stderr:
FAKE_DEAD_CHILD: deliberate stderr
```

`testAlreadyExitedChildIsHandled` requires the phrase `closed stdout` as well as
that stderr. Here stderr was retained, but submission encountered a broken pipe
instead. This is an unchanged fake-child lifecycle assertion, not a native FF
failure. The full rerun exited 0: **5/5** dedicated pure modules, **212** pure
build jobs, and **668** Z3 build jobs. Thus both `make test-pure` and
`make test-z3` ran and passed as the actual nested targets of `check_tests`.
The same-target, same-job full rerun satisfies the ticket's explicit flake rule.
No protected test or production diagnostic was changed; the historical failures
above remain part of the record.

Additional boundary checks in this job:

- Ten isolated Python checks passed: missing/empty source discovery, recursive
  sorted discovery, missing registration, exact per-module cleanup preserving
  siblings and child outputs, empty/partial/full coverage, rejection of replayed
  evidence, and solver-override clearing with artifact-cache disabling.
- `Bun.YAML.parse` accepted the proposed workflow, its three triggers and native
  arm64/x86_64 matrix. This does not claim GitHub workflow execution.
- `python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root <empty-temporary-directory> --profile solving --offline --check`
  exited 1 for missing `solving/metadata.json`; it did not use ordinary PATH.
  The temporary directory was removed.

The strict ordinary cvc5 suite also passed its one permitted full-target rerun:

```sh
bash -o pipefail -c 'make BLASTER_TIMEOUT=120 test-cvc5 2>&1 | tee .artifacts/ffm-10-cvc5-refresh.log'
bash -o pipefail -c 'make BLASTER_TIMEOUT=120 test-cvc5 2>&1 | tee .artifacts/ffm-10-cvc5-rerun.log'
```

The first exited 2 in unchanged `Tests/Smt/SmtMatch.lean:377`, reporting
`solver closed stdout before reporting a verdict; elapsed=112792ms`.
The underlying process-exit cause was not established. Its ordinary baseline
prerequisite passed. The full unchanged rerun exited 0 with **671 build jobs**,
again executing the baseline first and then the strict suite from clean Tests
outputs. Both used the image's ordinary cvc5 1.4.1 and the requested timeout 120.
The ticket's same-target full-rerun rule applies to this separate flake as well;
no existing allowed outcome, assertion, solver option or recipe was changed.

The ordinary cross-backend gate passed on its first invocation in this job:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin" bash -o pipefail -c 'z3 --version && cvc5 --version && make test-all-solvers 2>&1 | tee .artifacts/ffm-10-all-solvers-refresh.log'
```

It printed Z3 **4.15.2** and image cvc5 **1.4.1**, executed the ordinary baseline,
then completed **698 build jobs**, concurrency assertions and complete root Tests
source coverage. The recipe itself cleared `BLASTER_TIMEOUT`. The staged FF
directory was never added to PATH.

Recursive child discovery was exercised with a temporary, unimported
`ff-tests/TestsFF/DiscoveryRefresh/Nested.lean` containing a checked arithmetic
example and an execution marker. `make test-cvc5-ff` freshly built it, printed
`FFM-10 recursive discovery refresh executed`, and also executed all four native
capability cases. No import, runner, package or workflow edit was needed.
The temporary source and directory were removed; another `make test-cvc5-ff`
passed against the final source tree, freshly building the root and Capability
and reporting **4 live cases**. The target's cleanup removed the temporary
module's generated child outputs too.

Direct negative capability invocations from `ff-tests/` both exited 1:

```sh
env -u BLASTER_FF_CVC5 lake env lean TestsFF/Capability.lean
BLASTER_FF_CVC5=cvc5 lake env lean TestsFF/Capability.lean
```

The first required the explicit verified solver, and the second rejected relative
PATH fallback. All temporary smoke sources were removed. Full suite logs remain
ignored local `.artifacts/` evidence, not committed project inputs.

**Current local acceptance:** all requested executable gates have passed in this
job, with the two initial unchanged-test failures and their same-job full reruns
recorded explicitly. This is not a fix for either intermittent failure and does
not guarantee later runs are flake-free. The only retained change is this report.

### Current published-head CI evidence

The [PR #412 API](https://api.github.com/repos/input-output-hk/Lean-blaster/pulls/412)
now identifies head **`7b07a3ac46fca4945c0bbcec50878984a333a31d`**.
Unlike the pre-ticket head recorded above, its
[Makefile](https://github.com/input-output-hk/Lean-blaster/blob/7b07a3ac46fca4945c0bbcec50878984a333a31d/Makefile)
contains `test-cvc5: test-cvc5-fin-baseline` and the standalone baseline recipe.
The [head's check runs](https://api.github.com/repos/input-output-hk/Lean-blaster/commits/7b07a3ac46fca4945c0bbcec50878984a333a31d/check-runs)
and the completed cvc5 check report:

| Published-head lane | Observed result |
| --- | --- |
| [solver tests (cvc5)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40617732847/job/122584067486) | **Success**; ordinary non-GPL/non-CoCoA x86_64 baseline and strict lane. Completed 2026-10-28T02:07:54Z. The unchanged workflow still pins ordinary cvc5 1.3.4; this does not claim the pending maintainer update to 1.4.1. |
| [solver tests (cvc5-1.2.1)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40617732847/job/122584067399) | **Success**; support floor on x86_64. Completed 2026-10-28T01:57:10Z. |
| [solver tests (z3)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40617732847/job/122584067472) | **Success**; Z3/pure x86_64 coverage. Completed 2026-10-28T01:59:23Z. |
| [solver tests (all-solvers)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40617732847/job/122584067126) | **Success**; ordinary cross-backend x86_64 coverage. Completed 2026-10-28T01:57:55Z. |
| finite-field solving (linux-arm64) | **Pending** maintainer installation of the proposed workflow. Local arm64 execution is recorded separately. |
| finite-field solving (linux-x86_64) | **Pending** maintainer installation and native CI execution; not run in this arm64 worker. |

These results bind the named published head, not a future commit containing this
report refresh. Head-specific checks after publication and final signoff remain
with Riley/the stack. No workflow was installed or edited by this job, and the
reserved M2 `test-ff-verified` name remains documentation only.
