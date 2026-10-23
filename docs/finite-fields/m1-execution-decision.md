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

Observed on 2026-10-22 against the named public repository:

| Item | Exact observation |
| --- | --- |
| Reviewed base | `a69c5c266864a90064884519a5d208f5321cf379` |
| Remote `refs/heads/agent/feat-cvc5-ff` | `a69c5c266864a90064884519a5d208f5321cf379` |
| Remote `refs/heads/feat/cvc5-concurrency` | `a69c5c266864a90064884519a5d208f5321cf379` |
| Supplied checkout `HEAD` | Synthetic root `487f79daaf391868d0335f74fc795164ab0739bb` (`base`), on `master` |
| Configured remotes / required tracking ref | No configured remote; `refs/remotes/origin/agent/feat-cvc5-ff` absent |
| Reviewed base and supplied snapshot tree | Both `ff2ccaa64af5e6334cbf96d35e3c6e60be134f84` |

Commands establishing the remote evidence:

```sh
git ls-remote https://github.com/input-output-hk/lean-blaster.git refs/heads/agent/feat-cvc5-ff refs/heads/feat/cvc5-concurrency
git fetch --no-tags https://github.com/input-output-hk/lean-blaster.git refs/heads/agent/feat-cvc5-ff
git rev-parse FETCH_HEAD HEAD^{tree} a69c5c266864a90064884519a5d208f5321cf379^{tree}
git diff --stat a69c5c266864a90064884519a5d208f5321cf379 HEAD
git rev-list --left-right --count a69c5c266864a90064884519a5d208f5321cf379...FETCH_HEAD
git merge-base --is-ancestor a69c5c266864a90064884519a5d208f5321cf379 FETCH_HEAD
```

All six commands succeeded. Fetch populated only `FETCH_HEAD`, not a fabricated
`origin` tracking ref. The remote integration tip equals the reviewed base:
left/right commit counts are `0 / 0`, ancestry holds, and there are no source,
test, script, CI, toolchain or documentation differences at that tip. No remote
base rewrite was observed. The local snapshot also has an empty tree diff, but
**tree identity is not Git ancestry**: the supplied synthetic root does not
descend from the reviewed base.

The user-created branch's existence is a dispatch precondition, satisfied on
the public remote but not by this clone's required tracking-ref/ancestry checks.
Do not rewrite this checkout, create another integration branch, or substitute a
synthetic history to make those checks pass. Before publication or dependent
work, the coordinator must apply the validated ticket patch through the plan
publishing tools onto the actual integration lineage and verify the required
tracking ref and ancestry in the execution checkout. This job has no plan
publishing tool exposed; it records a local deliverable, not a completed dispatch
repair. A changed or rewritten integration base requires stopping and refreshing
the exact comparison and plan approval before further work. This snapshot
mismatch is an explicit unresolved execution prerequisite, not approval to
waive ancestry.

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
- Setup is `lake --version`. Before the first job the worker must already have
  the ordinary baseline solver environment required by PROJECT's default test
  driver. FFM-03 separately specifies staging additional FF solver profiles for
  its consumers; those profiles do not replace the default baseline.
- Mandatory PROJECT checks are `lake build Blaster` and
  `LEAN_NUM_THREADS=5 lake test`. Repository instructions additionally require
  `make check_blaster`, then
  `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests`.
  Preserve those commands and their checks. The current inspected CI uses its
  tiered solver commands as described above; the default driver alone is not
  proof that all CI solver lanes passed.

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

Change: documentation only, in this decision record. It fixes the execution
topology, dependency-join rule, branch evidence, project boundary and stop
conditions. No executable source, tests, scripts, workflow, PROJECT, solver pin
or toolchain was changed. The report is retained in this same committed artifact.

Observed setup: `lake --version` exited 0, reporting Lake
`5.0.0-src+797c613` / Lean `4.24.0`. `z3 --version` exited 0, reporting `5.1.0`
(build `ca39e58c525c5b03c2484f118ade2b92fae31215`); `cvc5 --version` exited 0,
reporting `1.4.1`, git `2b2e844`. These are observed preinstalled binaries, not
changes to the CI pins or proof of FF-profile qualification. No solver was
replaced or downloaded.

### Local validation outcomes

| Exact command | Observed outcome |
| --- | --- |
| `lake build Blaster` | Pass, exit 0; 171 jobs, 87.77 seconds. |
| `LEAN_NUM_THREADS=5 lake test` | Not green: the command runner terminated the run at its 3,600-second deadline (3,600.11 seconds observed). Last reported progress was 625/651 jobs; no successful completion was observed. |
| `make check_blaster` | Pass, exit 0; clean compilation check, 171 jobs, 86.69 seconds. |
| `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests` | Not green: `Tests.StateMachine.Counter06Z3` reported a `#guard_msgs` mismatch and Lean exit 1; the overall command subsequently hit the 3,600-second runner deadline (3,600.11 seconds observed), last reported progress 625/651 jobs. |
| `git diff --check` | Pass, exit 0; the final staged document is additionally checked with `git diff --cached --check`. |
| `git rev-parse --verify refs/remotes/origin/agent/feat-cvc5-ff^{commit}` | Fail, exit 128: `fatal: Needed a single revision`; the tracking ref is absent. Remote branch existence was independently established above. |
| `git merge-base --is-ancestor a69c5c266864a90064884519a5d208f5321cf379 HEAD` | Fail, exit 1 after fetching the public base object: the local synthetic root has no such ancestry. Before fetching, the same command reported an invalid commit name. |
| `test -s docs/finite-fields/m1-execution-decision.md` | Pass, exit 0. |

The executable tree was unchanged from the reviewed base during these checks.
The default test run's timeout is an unresolved baseline validation failure, not
a passing test suite. The subsequent Tests compilation gate's `build.log`
identifies `Tests/StateMachine/Counter06Z3.lean:59:0`: the `#guard_msgs` docstring
does not match the generated induction-failure/counterexample messages. The
underlying cause of that mismatch and of the overall timeouts was not established
by this documentation job. No test, expected outcome, timeout setting in the
repository or solver was altered; neither baseline gate is waived.

### Remaining work and publication status

FFM-01's decision artifact is available locally, but its full passing validation
acceptance is **blocked**. Restore the dispatch checkout on the actual integration
lineage with its required remote-tracking ref, and establish green applicable
baseline test/compilation gates in the approved solver environment before
publishing validated plan commits or starting dependent work. Any prerequisite repair
outside the supplied boundary needs scoped owner approval; this record grants
none. Do not mark this ticket as a fully validated parent on the strength of the
document alone.

The coordinator still owns publication through the plan tools and retention of
the one aggregate draft PR. No push, branch rewrite, PR creation, remote CI run
or maintainer approval occurred in this job. The separate FF workflow, FFM-02
toolchain decisions and FFM-03 profile staging remain their own scoped work;
production verified reconstruction remains post-merge M2.

Local commit attempt:
`git commit -m "Record M1 integration execution contract" -- docs/finite-fields/m1-execution-decision.md`
exited 128 because no Git author identity is configured. The decision/report is
staged for the stack's owner-attributed commit; no identity was invented or
configured and no local commit was created. The preceding `git diff --check`,
`git diff --cached --check` and document-presence checks all exited 0.
