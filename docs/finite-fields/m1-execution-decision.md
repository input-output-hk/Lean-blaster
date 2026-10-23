# FFM-01: M1 integration branch and job execution contract

## Decision and scope

The owner-approved integration branch is `agent/feat-cvc5-ff` in
`input-output-hk/lean-blaster`. Plan jobs run serially in auto mode, one job per
ticket. The coordinator publishes each ticket's validated commits directly to
that shared integration branch through the plan publishing tools. Retain one
aggregate **draft M1 PR** from `agent/feat-cvc5-ff` into
`feat/cvc5-concurrency`. There are no separate ticket PRs and no intermediate
maintainer merge gates. Final aggregate review and merging belong to the project
maintainer; this record does not claim publication, PR creation or approval.

M0/M1 remain the current milestone. Production verified reconstruction is a
separate post-merge M2 effort, not work opened or implemented by this decision.
FFM-01 implements no finite-field code (FFM-07 through FFM-18), chooses no solver
hosting (FFM-03), grants no toolchain exception (FFM-02), and selects no optional
features (FFM-22).

## Branch evidence and dispatch limitation

Observed on 2026-10-23 against the named public repository:

| Item | Exact observation |
| --- | --- |
| Reviewed base | `a69c5c266864a90064884519a5d208f5321cf379` |
| Remote `refs/heads/agent/feat-cvc5-ff` | `635d1c74375ee0ec87a53e6fec4ceff1d7a30b7e` |
| Remote `refs/heads/feat/cvc5-concurrency` | `a69c5c266864a90064884519a5d208f5321cf379` |
| Supplied checkout `HEAD` | Synthetic root `92ed7b6a4ab2909161ae65a73339253bea8da3b3` (`base`), on `master` |
| Configured remotes / required tracking ref | No configured remote; `refs/remotes/origin/agent/feat-cvc5-ff` absent |
| Reviewed base tree | `ff2ccaa64af5e6334cbf96d35e3c6e60be134f84` |
| Integration tip and supplied snapshot tree | Both `4eac1470b9a409864600ece55335679bd8835704` before this refresh |

Commands establishing the remote evidence:

```sh
git ls-remote https://github.com/input-output-hk/lean-blaster.git refs/heads/agent/feat-cvc5-ff refs/heads/feat/cvc5-concurrency
git fetch --no-tags https://github.com/input-output-hk/lean-blaster.git refs/heads/agent/feat-cvc5-ff
git rev-parse FETCH_HEAD HEAD^{tree} FETCH_HEAD^{tree} a69c5c266864a90064884519a5d208f5321cf379^{tree}
git rev-list --left-right --count a69c5c266864a90064884519a5d208f5321cf379...FETCH_HEAD
git merge-base --is-ancestor a69c5c266864a90064884519a5d208f5321cf379 FETCH_HEAD
git log --format='%H %s' a69c5c266864a90064884519a5d208f5321cf379..FETCH_HEAD
git diff --stat a69c5c266864a90064884519a5d208f5321cf379 FETCH_HEAD
git diff --stat FETCH_HEAD HEAD
git log -5 --format=fuller
```

All commands above succeeded. Fetch populated only `FETCH_HEAD`, not a fabricated
`origin` tracking ref. Left/right commit counts are `0 / 3`, and the reviewed base
is an ancestor of the remote integration tip. The added commits, oldest first:

- `9635c22f6a9ef3a40ca9373915c4de5fc38d0ff9`
  (`docs: record M1 finite-field execution contract and baseline blockers`).
- `1e1262b9d3ee346f41ed4e6882bda2067a2002f7`
  (`docs: refresh M1 execution evidence and baseline blockers`).
- `5e9bc4471bc49525c067a29ba38b79a92f197154`
  (`docs: refresh finite-field M1 validation and checkout blockers`).

Their cumulative difference from the reviewed base is only this decision
document, added with 272 lines; executable source, tests, scripts, CI and
toolchain are unchanged. The supplied snapshot has an empty tree diff against
that integration tip, but **tree identity is not Git ancestry**: its synthetic
root has no parents and does not descend from the reviewed base.

The inherited record observed the remote at `1e1262b9d3ee346f41ed4e6882bda2067a2002f7`
on 2026-10-23. This refresh observes another documentation-only advance, not a
base rewrite. No remote rewrite requiring a replacement plan was observed. The
remote head then advanced to `635d1c74375ee0ec87a53e6fec4ceff1d7a30b7e`
(`docs: refresh M1 branch evidence and ticket validation blockers`), again
documentation-only. GitHub's compare of
`a69c5c266864a90064884519a5d208f5321cf379...agent/feat-cvc5-ff` reports the
branch `ahead` by 4 and behind by 0, with only this document changed, and
`git merge-base --is-ancestor a69c5c266864a90064884519a5d208f5321cf379 FETCH_HEAD`
passes after fetching that head.

The user-created branch's existence is a dispatch precondition, satisfied on
the public remote. Branch heads and ancestry are established by the stack and
GitHub (or a `git fetch` into `FETCH_HEAD`), not by the sandbox checkout. The
sandbox checkout is a single parentless local commit with no git remote by
design; the stack clones the branch head and publishes on top of it. Its
synthetic root and missing tracking ref are therefore not a dispatch defect.
A changed or rewritten integration base still requires stopping and refreshing
the exact comparison and plan approval before further work.

Historical experimental agent branches are selective public source references,
not alternative bases or merge candidates. The historical
[FF-01 integration record](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/docs/finite-fields/ff-01-integration.md)
records divergent lineage and unrelated changes. Its subject-specific document
convention is reused here, not its old branch target, implementation, validation
claims or trust decisions. No experimental branch was merged or cherry-picked.

## Serial execution and dependency joins

1. Before dispatch, verify the owner-created integration branch, reviewed base,
   applicable green baseline and supplied worker prerequisites. Record the exact
   starting integration tip for each ticket.
2. Run one ticket job at a time. A ticket may start only after **every required
   parent is complete and all of its required outputs are present together on
   the integration branch**. Completion status alone, an unmerged branch, or a
   report without its artifacts is insufficient.
3. Validate the ticket against that cumulative branch state. Record the decision
   or change, exact commands and outcomes, and remaining limitations in the
   committed ticket report and job summary.
4. The coordinator appends validated ticket commits directly through the plan
   publishing tools; the next job uses the resulting tip. Never run parallel
   plan jobs or publish competing tips. If the tip changes unexpectedly, stop
   and reconcile the base rather than overwriting it.
5. Multiple parents join through the serial append history: after parent A and
   parent B have both been published, the shared tip contains both outputs.
   Verify neither was removed or superseded incompatibly before dispatching the
   dependent ticket. No ticket PR or intermediate maintainer merge is needed.
6. Keep the single aggregate draft M1 PR current for PR validation and eventual
   maintainer review. Only the maintainer performs final aggregate approval and
   merging into `feat/cvc5-concurrency`.

## CI contract

The reviewed base's
[ci-linux workflow](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/.github/workflows/ci-linux.yaml)
runs on pull requests and pushes to `main`/`staging`, not pushes to
`agent/feat-cvc5-ff`. Its lanes are Z3, cvc5, both solvers, and the cvc5 1.2.1
support floor; its declared Z3/cvc5 versions are 4.15.2/1.3.4. Therefore serial
integration pushes rely on the aggregate PR's validation plus the separate FF
workflow to be added later under its own approved scope. Neither this record nor
a local check is a claim that remote CI ran. No workflow is changed here.

## Supplied iog project boundary

This section records the user-supplied PROJECT/project.yaml contract, not a file
assumed to exist in this clone and not an amendment granting access.

- Writable scope is the public `input-output-hk/lean-blaster` repository only.
  Reference links do not add clones, writable repositories or publishing rights.
  Public supplemental inputs remain read/build/selective-source references;
  private material must not enter this repository or its reports.
- Existing files under `Tests/`, `scripts/` and `.github/`, plus root
  `lakefile.toml`, `lakefile.lean` and `lean-toolchain`, cannot be changed or
  deleted by a push. New files are allowed by that boundary. A protected file
  created by an earlier ticket becomes an existing protected file for subsequent
  jobs; plan initial contents accordingly.
- `Tests/FixedIssues.lean` has only an end-append exception: append imports of
  new `Tests/FixedIssues/` regressions; never remove, rewrite or reorder existing
  content. Bug regressions follow `Issue<N>.lean`, namespace `Tests.Issue<N>`.
  No existing expected result may be weakened to get a green gate.
- New-file permission is not blanket CI permission. Workflow changes require
  the separately approved owner-visible filename scope; a new workflow path
  requires the corresponding amendment. This decision neither edits CI nor
  authorizes the later FF workflow. Existing-test exceptions likewise require
  their narrowly scoped executable validator or owner gate, not this record.
- Keep the pinned [Lean toolchain](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/lean-toolchain)
  (`leanprover/lean4:v4.24.0`), solver capability pins and build declarations.
  FFM-02 owns any proposed toolchain exception. Do not edit PROJECT or install
  substitute solver/toolchain pins to hide a failed prerequisite.
- Worker contract: `agentstack-worker-iog:latest`, an **8 GiB (`8g`) memory
  envelope shared by the agent and all its commands**, not per process. Keep
  jobs serial and budget compilation/solver concurrency within that envelope.
  This is the supplied requirement, not a measured container/image assertion.
- Setup is `lake --version`. The worker image provides the Z3 4.15.2 release
  (`/usr/local/bin/z3-4.15.2`) used by the PROJECT checks, the default assurance
  `z3`, and cvc5 1.4.1 (GPL static build, CoCoA). FFM-03 separately specifies
  staging additional FF solver profiles for its consumers; those profiles do not
  replace the PROJECT checks' Z3 4.15.2 environment.
- Mandatory PROJECT checks are `make check_blaster` and `make check_tests`
  with the Z3 4.15.2 release alone on PATH; the system runs them after every
  job. A default-environment `lake test` is not a gate. The exact commands,
  selecting the preinstalled CI Z3 4.15.2 rather than the default assurance Z3:

  ```sh
  PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
  PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
  ```

  Preserve those commands and their checks. `make check_tests` runs the pure and
  Z3 tiers; it does not run the cvc5, support-floor or all-solvers CI lanes. The
  default driver alone is likewise not proof that all CI solver lanes passed.

## Stop conditions and trust boundary

Stop dependent implementation/publication on a red applicable baseline gate,
a changed or rewritten base pending refreshed comparison/approval, missing
required parent outputs, or a required new trust escape. Record the failure and
request the scoped prerequisite rather than weakening a check or silently
changing the plan. A locally unavailable ref is not evidence of a remote branch
rewrite; both observations must be recorded separately.

No `sorry`, `admit`, new axiom or widening of `blasterProven` is authorized here.
The finite-field plan's explicit distinct trusted-mode axiom remains only its
narrow human design exception, not permission to put a trusted FF axiom on the
verified reconstruction path. Production verified reconstruction remains
kernel-checked and axiom-free as specified for the separate post-merge M2 effort.
A newly required escape outside the approved exception is a stop condition.

## FFM-01 ticket report and job summary

Change: documentation only, refreshing this existing decision record's remote
head, ancestry comparison, checkout identity and validation report. The execution
topology, dependency-join rule, project boundary and stop conditions remain the
owner-supplied contract. No executable source, tests, scripts, workflow, PROJECT,
solver pin or toolchain was changed. This section is the ticket report and job
summary retained in the same artifact for the stack's owner-attributed commit.

Observed setup on 2026-10-23: `lake --version` exited 0, reporting Lake
`5.0.0-src+797c613` / Lean `4.24.0`. `z3 --version` exited 0, reporting `5.1.0`
(build `ca39e58c525c5b03c2484f118ade2b92fae31215`); `cvc5 --version` exited 0,
reporting `1.4.1`, git `2b2e844`. These are observed preinstalled binaries, not
changes to the CI pins or proof of FF-profile qualification. No solver was
replaced or downloaded.

### Inherited baseline evidence (not runs from this refresh)

The incoming decision record reports these earlier attempts against unchanged
executable sources. They remain unresolved evidence, not current passing gates:

| Exact command | Earlier reported outcomes |
| --- | --- |
| `lake build Blaster` | Exit 0; 171 jobs on both 2026-10-22 and the earlier 2026-10-23 job. |
| `LEAN_NUM_THREADS=5 lake test` (non-gating diagnostic) | Runner deadlines at 3,600 seconds (2026-10-22) and 600 seconds (earlier 2026-10-23 job), each last reporting 625/651 jobs; neither completed successfully. |
| `make check_blaster` | Exit 0; 171 jobs in both earlier jobs. These were not the explicitly PATH-selected CI commands below. |
| `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests` | `Tests/StateMachine/Counter06Z3.lean:59:0` reported a `#guard_msgs` mismatch and Lean exit 1; overall commands then hit the respective 3,600-/600-second deadlines. |
| CI-pinned `make check_blaster` / `make check_tests` (exact PATH-selected commands below) | The immediately preceding report records exit 0 for both: 171 build jobs; 200 pure-tier and 611 Z3-tier jobs. Its default-driver attempt still timed out at 600 seconds. |

The earlier reports did not establish the cause of the mismatch or timeouts.
This refresh does not change that protected test or waive its expected outcome.
The previously used Tests compilation command is historical evidence, not a
replacement for the supplied `make check_tests` repository gate.

### Current refresh validation (2026-10-23)

| Exact command | Observed outcome |
| --- | --- |
| `lake build Blaster` | Pass, exit 0; 171 jobs, 91.31 seconds. |
| `LEAN_NUM_THREADS=5 lake test` (non-gating diagnostic) | Not green: runner deadline at 600 seconds (600.06 seconds observed), last reported progress 625/651 jobs; no successful suite completion. Used the default preinstalled solver environment, not the CI PATH below. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass, exit 0; selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2; clean compilation, 171 jobs, 87.79 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass, exit 0; same Z3 4.15.2; pure tier completed 200 jobs and Z3 tier completed 611 jobs; 172.76 seconds total. |
| `git diff --check` | Pass, exit 0; checked after the evidence/report refresh. |
| `git rev-parse --verify refs/remotes/origin/agent/feat-cvc5-ff^{commit}` | Fail, exit 128: `fatal: Needed a single revision`; no remote or tracking ref is configured in this snapshot. |
| `git merge-base --is-ancestor a69c5c266864a90064884519a5d208f5321cf379 HEAD` | Fail, exit 1 after fetching the public integration head; the supplied synthetic root is not a descendant. The separate check against `FETCH_HEAD` passed. |
| `test -s docs/finite-fields/m1-execution-decision.md` | Pass, exit 0. |

The default-driver attempt used unchanged executable sources and the ordinary
preinstalled solver environment. Its 600-second command-runner deadline is a
bounded validation attempt, not a new repository timeout policy or a green gate.
The inherited longer default-environment timeout remains unresolved.

The separate CI-pinned checks passed without changing code or tests.
`Tests.StateMachine.Counter06Z3` built successfully in the Z3 4.15.2 tier; this
does not establish the cause of the earlier default-environment message mismatch
or make the incomplete default-driver gate pass. The successful test run emitted
lifecycle diagnostic warnings; no warnings or expectations were suppressed.
`Tests/Smt/SmtNat/SmtNatMod.lean:41:56` reported `Valid` in this run, unlike the
preceding report's `Undetermined` warning; no source or expected result changed.
No cvc5/support-floor/all-solvers lane or remote CI run is claimed. No solver
environment repair, test expectation change or baseline waiver is part of this
documentation job.

### Remaining work and publication status

Outcome: the mandatory PROJECT checks, the CI-pinned `make check_blaster` and
`make check_tests` with Z3 4.15.2 alone on PATH, passed. GitHub's compare of
`a69c5c266864a90064884519a5d208f5321cf379...agent/feat-cvc5-ff` shows the branch
ahead with 0 behind and only this document changed. Ancestry of the reviewed base
was verified against the fetched head via `FETCH_HEAD`. The sandbox checkout's
synthetic root is by design and is not a dispatch defect. Any prerequisite repair
outside the supplied boundary needs scoped owner approval; this record grants
none.

The coordinator still owns publication through the plan tools and retention of
the one aggregate draft PR. No push, branch rewrite, PR creation, remote CI run
or maintainer approval occurred in this job. The separate FF workflow, FFM-02
toolchain decisions and FFM-03 profile staging remain their own scoped work;
production verified reconstruction remains post-merge M2.

The inherited report records a failed historical local commit attempt because no
Git author identity was configured. The three earlier documentation commits are
now present on the public integration lineage, as established above; that
historical local failure is not evidence of absent publication. This refresh
does not invent an author identity or claim a coordinator publication.

Current local commit attempt:
`git add docs/finite-fields/m1-execution-decision.md && git commit -m "Refresh M1 execution branch evidence and validation"`
failed with exit 128, `Author identity unknown`. No author identity was invented
or configured. The updated decision and report remain staged for the stack's
owner-attributed commit; this job has not created a commit or published it.
