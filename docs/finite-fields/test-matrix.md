# Finite-field test ownership and gates

FFM-10 implements the additive M1 layout. This document supersedes the draft
runner names and acquisition details in `m1-test-layout-decision.md`: the approved
runner is Python, the solving profile is cvc5 **1.4.1 GPL/CoCoA**, acquisition uses
FFM-09, and the workflow is a handoff proposal, not an installed workflow.

| Gate | Owned sources and registration | Solver environment |
| --- | --- | --- |
| `test-ff-pure` | Every `Tests/FiniteField/**/*.lean`, discovered recursively and sorted by module name | No solver; selection, timeout and strictness overrides removed |
| `test-pure` | New pure prerequisite, followed by unchanged `Tests.Pure` recipe | No solver |
| `test-cvc5-fin-baseline` | Parent's standalone `ff-tests/OrdinaryCvc5Baseline.lean`, executed from the repository root with `lake env lean` | Ordinary PATH cvc5; strict results; Make timeout |
| `test-cvc5` | Standalone baseline prerequisite, then unchanged strict ordinary suite | Ordinary cvc5 1.4.1; no native FF requirement |
| `test-all-solvers` | Standalone baseline prerequisite, then unchanged concurrency and complete root Tests coverage | Ordinary cvc5 plus Z3 4.15.2; existing all-solvers recipe clears `BLASTER_TIMEOUT` |
| `test-cvc5-floor` | Unchanged support-floor smoke and discovery tests | cvc5 1.2.1, CI-only in this worker |
| `test-cvc5-ff` | Child `TestsFF.lean` and every recursive `TestsFF/**/*.lean` | Only the explicit, offline-verified staged solving executable is passed to FF cases |
| `test-ff-verified` | **Reserved M2 name only; no target or required job exists** | Future kernel-checked reconstruction, not M1 solving |

## Adding tests without changing runners

Pure-test authors create a new file under `Tests/FiniteField/` (nested directories
are supported) and append its individual `import Tests.FiniteField.…` to the end
of `Tests/FixedIssues.lean`. Never rewrite, remove or reorder earlier imports.
The runner requires a one-to-one match between discovered modules and these
registrations. Registration reaches the ordinary `lake test` import graph;
`Tests.Pure` does not import `FixedIssues`, so the explicit pure gate is necessary.
Do not use `lake test` in the default worker solver environment as validation.
Pure files must contain deterministic checks without invoking external solvers.

The pure runner removes only generated outputs belonging to discovered modules,
then explicitly builds all of them. Fresh build evidence must cover every module;
empty discovery, bad registration, compiler failures and missing coverage fail.
Future pure additions do not require runner or workflow edits.

Live-test authors add files below `ff-tests/TestsFF/`. The child library's Lake
globs select its root and all recursive submodules, including files not imported
by the root. No runner, workflow or root import-list change is needed. Each live
module must execute real assertions, not merely declare uncalled test functions.
The unchanged coverage script enumerates every source in `TestsFF/` and requires
fresh compilation evidence after the child outputs are removed. The root is also
a required Lake glob target. The initial capability suite executes real native
SAT/model and UNSAT cases and reports a nonzero case count. It is solver/protocol
coverage, not production translation, a Lean proof or M2 reconstruction.

The standalone ordinary baseline remains outside the live tree. It is never
imported into `TestsFF`, built by the child library, or given the staged FF
executable. Its `Fin` rejection and bounded-Nat arithmetic require no finite-field
theory. The worker's ordinary cvc5 has CoCoA support, which is recorded but is not
required or reached by those queries. The non-CoCoA run belongs to ci-linux.

## Acquisition, offline consumption and isolation

From a fresh checkout/artifact directory:

```sh
make ff-stage
python3 scripts/finite_fields/run_pure_tests.py
make test-cvc5-fin-baseline
make test-cvc5-ff
```

`ff-stage` is the only FF network step: it invokes the unchanged parent's
`--fetch-only` interface for `solving` into `.artifacts/finite-fields`, then
`--offline --check`. Acquisition deliberately refuses an already-existing profile;
use `make test-cvc5-ff` to validate/reuse provisioned artifacts, not another fetch.
The offline probe verifies archive/executable identities, configuration, real
protocol cases and required capabilities before the child compilation can start.
The Make target passes the manifest's fixed `solving/bin/cvc5` path through
`BLASTER_FF_CVC5`, never through PATH, and overwrites any inherited value.
Missing or invalid inventory is a failure, not fallback to the image's cvc5.
Offline mode is the parent's no-acquisition contract, not an OS network sandbox.

The child uses `require Blaster from ".."` and inherits the root `lean-toolchain`.
There is no child toolchain pin, external dependency or root Lake change. Its
manifest contains only the local parent. Child build outputs live in its own
`.lake/`; no ordinary tier requires those outputs or the FF artifact.

Clearing suites run sequentially in one checkout. The appended `.NOTPARALLEL:`
also serializes a single `make -j` invocation without changing existing recipes.
Do not launch independent Make processes against the same build tree concurrently.
The existing all-solvers recipe clears timeout itself; its baseline prerequisite
uses the ordinary Make timeout convention.

## Workflow handoff and CI ownership

`finite-fields.workflow.yaml` in this directory is the only workflow proposal.
Riley must review and copy it to `.github/workflows/finite-fields.yaml`; this ticket
creates nothing under `.github/`. It proposes native Linux arm64 and x86_64 jobs,
solver-free pure execution before acquisition, `make ff-stage` in network-enabled
setup, and offline `make test-cvc5-ff`. Build and clearing steps are sequential.
Both architectures use the unchanged root toolchain and pinned host-specific
solving artifacts. No staged executable enters `GITHUB_PATH`.

`ci-linux.yaml` remains unchanged. Its existing Z3 **4.15.2** and support-floor
**1.2.1** installations remain owned by that workflow. Riley changes its ordinary
cvc5 pin from 1.3.4 to **1.4.1** after M1. The ordinary non-GPL cvc5 lane exercises
the added baseline through `make BLASTER_TIMEOUT=120 test-cvc5`. Neither that lane
nor pure, Z3, floor or concurrency lanes acquire the FF artifact. The proposed
FF workflow's CI results remain pending until maintainer handoff. See
`ffm-10-ticket-report.md` for exact local evidence and head-specific CI status.
