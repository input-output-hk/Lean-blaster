# CI operation

`ci-linux` keeps the existing required `build` check. It checks the build-script
regressions, uses the repository's `lean-toolchain`, resolves Z3 master to a full commit SHA and builds that snapshot from source, and builds the library and tests. Checkouts keep
no GitHub credentials; execution jobs have `contents: read`. Actions and the elan
installer source are pinned. The workflow validation job uses a checksum-verified
actionlint 1.7.12. Its two exact schema exceptions cover `queue` and
`copilot-requests`, which that linter predates; all other schema errors fail.

`scripts/check_lean_project_compilation.sh <target> [source-dir] [excluded-subtree]`
builds the target plus every selected `.lean` module, including the barrel. New
files are therefore checked even before somebody adds their barrel import.
Cached builds are valid: the script does not parse Lake progress messages.
An excluded subtree also excludes its sibling barrel, but excludes no similarly
named siblings. An invalid/empty selection fails. A failed Lake command survives
`tee`. Logs remain in `.ci-results/build/<target>.log`; `build.log` is retained
for the existing manual conformance workflow.

Every run uploads logs and `environment.json`, including the actual source commit,
Lean/Lake/Z3 versions, architecture and resolved `lake-manifest.json` when available.
Artifacts last 14 days. CI evidence is ignored by Git. Dependency branch policies
are unchanged: these records identify the commits resolved for each run; they do
not turn moving dependency branches into a stable release baseline.

The daily nightly-Lean workflow builds both the library and tests with Z3 master. Failures leave a red build job, even if reporting succeeds. A separate reporter
executes no repository code. It creates one bot-owned issue per failure episode,
stays quiet during repeated failures, then comments once and closes that issue on
recovery. The marker `<!-- blaster-nightly-lean -->` identifies these issues;
older manually managed nightly issues are not closed automatically. A setup failure
is reported as a check failure, not assumed to be a Lean breaking change.

Local checks for the new infrastructure:

```sh
python3 scripts/ci/test_build_check.py
node scripts/ci/test_nightly_report.cjs
make check_all
```

The first two checks require Python 3 and Node.js, respectively; `make check_all`
requires this repository's Lean and Z3 master environment. CI runner timeouts bound
cost but are not performance thresholds. Preserve the existing required-check
rules until the new workflows have been observed on actual PRs.

## Result interpretation

Lean compilation, a solver's `Valid` response, an independent reference/finite
oracle and a reconstructed kernel-checked proof are distinct evidence. In
particular, passing Blaster tests do not by themselves certify proofs. Preserve
negative and unknown cases; never repair CI by weakening a specification, changing
expected results, adding `sorry`/axioms, or silently excluding a failing category.

## Next rollout stages

1. Merge and observe these CI foundations. Track missed failures, signal quality,
   run duration and artifact completeness.
2. Exercise exact-commit downstream compatibility and reproducible benchmark jobs.
   Schedule conformance only after PlutusCoreBlaster #50's separation of build/report
   privileges and generator hardening is merged. Retain a pinned corpus baseline
   alongside the rolling corpus; report generated, excluded, failed and passed cases.
3. Evaluate the Lean-blaster manual CI-advisor pilot on known failures. Record useful,
   unsupported and duplicate reports, maintainer correction time and AI cost.
4. Enable periodic advisory reporting only after that evaluation, then consider one
   bounded regression-test/specification contribution bot. Changes always go through
   reviewed PRs and the deterministic checks. Performance claims require fresh
   base/head runs on equal environments and a controlled runner.

These later stages are follow-up work, not silently enabled by this change.

## Exact-commit ecosystem check

`Blaster downstream compatibility` runs weekly and can be dispatched manually.
It uses the workflow commit as the Blaster candidate unless a full SHA is supplied.
Its two downstream baselines are deliberately fixed to PlutusCoreBlaster
`41fe7eadf460dc66bef22b85656bc36408638bdc` and CardanoLedgerApiBlaster
`9938562fd452351655fe2f6b63e583c62422687c`. A manual run can supply other full SHAs.
Update the schedule's baselines and input defaults together after validating new
ones. This compares a changing Blaster against a stable consumer baseline; it does
not claim to test every downstream branch or generated conformance case.

The check overlays only the known Git dependency declarations in disposable
checkouts, then verifies the resolved manifest uses the requested Blaster SHA in
both consumers and the requested PlutusCore SHA in the ledger consumer. It builds
all selected libraries/tests with this repository's hardened checker. Artifacts
include the dependency patch, resolution log, per-target logs and environment.
Execution is read-only, checkouts keep no credentials, and both matrix entries run
even when the other fails. No integration result changes a dependency in main.

```sh
python3 scripts/ci/test_downstream.py
# After merge: run from Actions, or dispatch an explicit candidate:
gh workflow run ci-ecosystem.yaml -f blaster_sha=<40-character-SHA> \
  -f plutus_sha=<40-character-SHA> -f ledger_sha=<40-character-SHA>
```

## Manual AI advisor pilot

`ci-advisor.md` and its compiled `ci-advisor.lock.yml` define a gh-aw Copilot
workflow. Only manual dispatch is enabled. Input selects one of the four repos
and a numeric failed-run ID. GitHub read tools are restricted to those repos and
approved content, shell tools are disabled, and outputs are staged: an issue
preview appears in the Actions summary instead of publishing an issue. It can
produce at most one preview in 15 minutes. It cannot create a PR or merge code.
The generated output handler retains gh-aw's scoped issue permission, but staged
mode skips API writes. Do not add privileged GitHub MCP token overrides.

Merge this workflow before its first normal dispatch. The organization must allow
GitHub Agentic Workflows/Copilot token authentication (`copilot-requests: write`)
and the pinned actions/containers. That entitlement and a live model run have not
been verified by compilation. Review the Actions summary and usage artifacts from
the first run; keep staged mode enabled during evaluation. No AI schedule is set.

```sh
gh workflow run ci-advisor.lock.yml \
  -f repository=input-output-hk/Lean-blaster -f run_id=<failed-run-id>
```

Edit the Markdown, then recompile with the pinned compiler:

```sh
# gh-aw v0.89.21; gh-aw-actions v0.89.21 resolves to this commit
gh aw compile ci-advisor --action-mode action \
  --action-tag 924af5fdc64061cfbf66fb584c8b07e2ac230c60 --no-check-update
```

Commit both files. The generated file is marked as generated in `.gitattributes`.
The compiler's strict mode validates the workflow; actionlint 1.7.12 needs the two
narrow compatibility exceptions documented above. See the official
[gh-aw tools](https://github.github.com/gh-aw/reference/tools/),
[staged outputs](https://github.github.com/gh-aw/reference/safe-outputs/), and
[engine authentication](https://github.github.com/gh-aw/reference/engines/) docs.

## Z3 master policy

Every run resolves Z3 master to a full commit and builds exactly that snapshot.
`.ci-results/z3-source.json` records the source ref, commit and build mode;
`z3-build.log` records compiler/configuration output. `environment.json` includes
both this source metadata and the executable's version. A moving master baseline
is identified by its commit, never only by a release-like version string.

Set `Z3_COMMIT=<full-SHA>` to replay an earlier master snapshot exactly. This is
also how the ecosystem matrix shares one solver commit across both consumers.
`Z3_BUILD_JOBS` defaults to two to limit memory pressure; a failed build fails CI.
The compiler and system libraries come from ubuntu-24.04. No built-solver cache is
restored. Manual local source builds can run `bash scripts/ci/build-z3.sh`; add the
absolute directory recorded in `.ci-results/z3-bin-path.txt` to PATH afterwards.

## Bounded execution and stalled solver diagnostics

The build checker defaults to a 1,800-second wall deadline; PR tests use
`BUILD_TIMEOUT_SECONDS=900`. Every minute it logs the processes in its own build
process group, including Lean module paths. On timeout it saves those processes,
command, elapsed time and exit status in `.ci-results/build/<target>.json`,
terminates only that build's processes and returns 124. Artifacts can therefore
upload before the outer job deadline.

CI setup installs a transparent Z3 proxy with a 120-second wall deadline per
solver session (`Z3_SOLVER_TIMEOUT_SECONDS` can override it). Original solver
options and responses remain unchanged. Each session retains the exact submitted
SMT input and timing/exit metadata under `.ci-results/solver/`. A wall timeout is
an explicit protocol error and failed compilation, never an `unknown` result
that could be accepted as a warning. Intentional `(solve-result: 2)` tests keep
their original solver timeout and expected result. Source assertions and solver
seeds are unchanged.

Replay a captured session with the Z3 commit from `environment.json`:

```sh
python3 scripts/ci/run_bounded.py --timeout 130 --report replay.json -- \
  z3 -smt2 .ci-results/solver/z3-<session-id>.smt2
python3 scripts/ci/test_bounded_z3.py
```

The captured input is exactly what Lean submitted; a hard interruption may leave
it partial. Use a wall deadline when replaying a stalled query.
