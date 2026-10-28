# FFM-10 ticket report and job summary

**Acceptance blocked:** the required `make check_tests` failed in unchanged
`Tests.Smt.CrashLifecycle` during `test-z3`, then failed in the same module on the
permitted full-target rerun. The pure tier passed both times. This is a repeated
failure, not a waived flake; the ticket cannot claim a green project gate.

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
