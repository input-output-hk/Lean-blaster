# FFM-21: integrated M1 interface verification

## Change and job summary

Added boundary-focused tests, a [public usage guide](native-support.md), executable
public examples and the [M1 completion handoff](m1-completion.md). The README links
the guide and explicitly identifies the retained trust boundary. No production
implementation, optimizer rule, solver pin, protected script, existing component
suite or workflow is changed. `Tests/FixedIssues.lean` receives only an import
appended at its end. New files do not replace or weaken baseline gates.

The handoff consumes the committed rule-audit bookmark, corpus and resource
measurements, and separates current native solving/model display from absent
production proof reading, checking and verified transport. The existing
`blasterProven` axiom and warning remain unchanged. M2 infrastructure, the deferred
proof-producing solver profile/full rule audit and FF optimizer rewrites remain
unfinished. This job does not mark the aggregate draft PR ready or merge it.

## Regression ownership and acceptance mapping

| Boundary | Added or reused evidence |
| --- | --- |
| Multi-modulus division-bearing SAT | `ff-tests/IntegrationSource.lean`: polynomial premises force zero in F2 and F7; nested division implications exercise polarity; exact typed zero values are associated with the producing session |
| Polynomial/field UNSAT | Same source: `(x² / x) * x = x²` in both fields, including zero; actual native `check-sat`, positive inverse graph obligations and negated source query are required |
| Optional evidence/session isolation | SAT with evidence, UNSAT, then SAT without evidence; fresh source/witness ownership, retained contexts, no stale model requests or proof requests |
| Dedicated test registration | New `ff-tests/TestsFF/Integration.lean` follows existing subprocess wrappers; `ff-tests/TestsFF.lean` imports it; nonzero executed SAT/UNSAT cases are reported |
| Malformed optional evidence | New `Tests/FiniteField/OutcomeIntegration.lean`: actual admission and polynomial translation followed by a deterministic shell SAT response and malformed field value; `Falsified` survives with bounded model diagnostics |
| Unknown/protocol/cleanup | New pure module: unknown remains `Undetermined`, invalid protocol remains an error, model requests do not precede decisive SAT, producing-session diagnostics survive and children are reaped |
| Non-FF concurrency | New pure module: `first`/`agree` unknown outcomes and hard-timeout cleanup; imports retain existing response/crash lifecycle fixtures |
| Routing and rejection before broadcast | Imported existing `Routing`/`RoutingLifecycle` coverage retains explicit/environment-selected Z3, binary-free cvc5 dry runs and native first/agree rejection; no rewritten component expectations |
| Public API examples | `ff-tests/GuideExamples.lean` mirrors the guide's checked modulus input and explicit single-cvc5 commands |

Shell fixtures are deterministic protocol peers, not qualified solvers. Live
integration independently requires the staged solver and actual SAT/UNSAT
responses; optimizer-only results cannot satisfy its assertions.

## Environment and exact pins

- Local synthetic input commit: `f7080bf229f3f3da0f52b84a541b970e5c142c32`.
  This is not an upstream ancestry claim.
- Linux/aarch64; Lean 4.24.0 commit
  `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake `5.0.0-src+797c613`.
- PROJECT Z3: `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.
  The default assurance Z3 is not used for these gates.
- Installed ordinary cvc5: 1.4.1, git `2b2e844`, GPL static build.
- Dedicated profile: separately staged cvc5 1.4.1 from the unchanged
  [manifest](solver-manifest.json). Exact source/archive/executable hashes are
  reproduced in the [handoff](m1-completion.md#pins-and-lane-ownership).
- No floor solver, non-CoCoA replacement or proof profile was downloaded.

Observed `cvc5 --show-config`:

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

CoCoA presence in the image is recorded, not treated as an ordinary-lane failure.
The ordinary baseline uses `Fin` rejection/bounded arithmetic, not native FF.

## PR #412 CI evidence

Observed through GitHub's public PR, workflow-run and job APIs on 2026-10-28.
The latest completed ci-linux and finite-fields workflow runs at final collection
were both successful on PR head
**`f726b4f7faecc625e83cfea7bd25a8f6e30fbe4a`**:

| Lane | Completed result | Evidence |
| --- | --- | --- |
| Ordinary non-CoCoA cvc5, x86_64 | success | [job 123013106894](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079941/job/123013106894) |
| cvc5 1.2.1 support floor, x86_64 | success | [job 123013106913](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079941/job/123013106913) |
| Z3, x86_64 | success | [job 123013106671](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079941/job/123013106671) |
| All-solvers, x86_64 | success | [job 123013107113](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079941/job/123013107113) |
| Dedicated finite-fields, arm64 | success | [job 123013106063](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079736/job/123013106063) |
| Dedicated finite-fields, x86_64 | success | [job 123013106492](https://github.com/input-output-hk/Lean-blaster/actions/runs/40744079736/job/123013106492) |

The completed head's `ci-linux.yaml` was checked: ordinary cvc5 was **1.3.4**,
floor **1.2.1**, and Z3 **4.15.2**; the ordinary archive is the non-GPL static
asset. These results are not relabeled as ordinary 1.4.1 results. The worker runs
ordinary 1.4.1; Riley's post-M1 ordinary-CI pin update and its resulting non-CoCoA
1.4.1 evidence remain **pending**. CI on this ticket's eventual publication head
is also **pending**, not inferred from an older green head. No CI run was requested
or awaited. CI is evidence rather than a gate under the ticket's explicit note.

## Worker validation

Commands run from the repository root; clearing builds are serialized. A returned
zero exit status, rather than a tool deadline or partial log, is the pass criterion.

### Completed setup, dedicated and documentation checks

```sh
make ff-stage
make test-pure
lake build Tests.FiniteField.OutcomeIntegration
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/OutcomeIntegration.lean
make test-cvc5-fin-baseline
```

All passed. Staging fetched the pinned arm64 solving profile once, then passed
all four offline protocol cases and required setup/solving/model capabilities.
`make test-pure` freshly compiled **18/18** discovered finite-field modules,
including the six new deterministic outcome scenarios, and then passed the
unchanged `Tests.Pure` recipe. Its latter recipe clears generated `Tests` outputs,
so the explicit module build above restores imports before direct Lean execution.
The standalone ordinary-cvc5 baseline passed separately, with image cvc5 1.4.1.

```sh
export BLASTER_FF_CVC5="$PWD/.artifacts/finite-fields/solving/bin/cvc5"
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean ff-tests/IntegrationSource.lean
lake build Blaster Tests.FiniteField.LargePrime
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean ff-tests/GuideExamples.lean
make test-cvc5-ff
```

All passed on the final sources. Direct live integration returned the forced
typed zero values in F2 and F7, then UNSAT, then SAT without model requests.
The public guide returned `Valid`, expected `Falsified` with root 4 modulo 7,
`Valid` for zero division, expected translation-only `Undetermined`, and
`Curve25519: Valid (solver verdict, not a reconstructed proof)`.

The final dedicated gate's offline qualification and full source coverage passed
(255 Lake jobs). Executed live cases: Capability **4**; Polynomial **5 SAT /
10 UNSAT**; Division **9 SAT / 13 UNSAT**; Model **5 SAT**; Integration **2 SAT /
1 UNSAT**. No empty or skipped native tier is counted as a pass.

The first dedicated run caught a parser error in this ticket's new source:
`variable` had been used as a lambda binder, but is a Lean keyword. It was renamed
to `source`; direct integration and the full dedicated target then passed.
No existing test or expected outcome was changed.

```sh
python3 scripts/finite_fields/check_benchmark_results.py --config benchmarks/finite-fields/config.json --results benchmarks/finite-fields/results.json --self-test
```

Passed: **54 cases / 216 runs**, with identities, offline setup, statuses, coverage
and summaries agreeing; all **15** evidence-corruption rejection scenarios passed.
This checks the committed parent measurements; it does not rerun benchmarks or
invent a production proof-stage measurement.

### PROJECT library gate

Executed exactly:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

Passed: release Z3 4.15.2 selected, clean Blaster build and complete library source
coverage, **246 jobs**, 113.20 seconds. This lane excludes the image's default
assurance solver and ordinary cvc5 from PATH.

### PROJECT tests gate and Z3 lane

Executed exactly:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Passed, exit 0, **240.29 seconds**. This runs `make test-pure` followed by
`make test-z3` with release Z3 4.15.2 alone on the solver PATH. Dynamic pure
coverage was again **18/18**, the ordinary pure target passed (275 jobs), and
`Tests.Z3` passed (**770 jobs**), including the new integrated module through
the append-only registry. No default-environment `lake test` was run.

Existing negative axiom-audit fixtures emit their expected `sorryAx` warnings;
existing response/crash fixtures emit unavailable-model/timeout diagnostics.
These are preserved baseline checks, not new axioms or suppressed failures.

### Ordinary cvc5 lane

```sh
env BLASTER_SOLVER=cvc5 make check_blaster
make BLASTER_TIMEOUT=120 test-cvc5
```

Both passed, exit 0, **778.20 seconds combined**. The clean library gate covered
all Blaster sources (246 jobs); the standalone ordinary-cvc5 prerequisite and
strict `Tests.Cvc5` target passed (773 jobs), using the installed 1.4.1 GPL/CoCoA
binary. Existing explicitly allowed cvc5 `Undetermined` outcomes remain unchanged.
No expectation was relaxed to obtain this result.

The guide's complete algebra block was additionally passed verbatim through
`lake env lean --stdin`, using only `import Blaster.FiniteField` plus
`open Blaster.FiniteField`, without the command umbrella or large-prime test
fixture. It exited 0 with no diagnostics. This reads library outputs only and
does not clear or build shared test outputs.

### Detached all-solvers lane

Ran `nohup make test-all-solvers` in a new session with stdin closed and both
output streams directed to `.artifacts/ffm-21/all-solvers.log`. The launcher
selected this PATH:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"
```

It removed `BLASTER_SOLVER`, `BLASTER_TIMEOUT` and
`BLASTER_STRICT_CVC5_RESULTS` from the inherited environment before launching;
the unchanged recipe sets its own strictness. The executed validation command
was **`make test-all-solvers`**, with no timeout override. Z3 4.15.2 and installed
cvc5 1.4.1 were checked before launch.

A Python supervisor launched `["nohup", "make", "test-all-solvers"]` with
`start_new_session=True`, polled the actual process and log size every five
seconds, and retained its real exit status. It was configured to capture
`ps -eo pid,ppid,pgid,stat,etime,args` and kill the descendant tree after 20 minutes
without log growth; that condition did not occur.

**Passed: exit 0, 195.91 seconds, 800 jobs, complete root Tests source coverage.**
The standalone ordinary-cvc5 prerequisite passed. Fresh output includes
`Tests.FiniteField.OutcomeIntegration`, `Tests.Smt.ResponseLifecycle`,
`Tests.Smt.CrashLifecycle` and `Tests.AllSolvers`. No hang or unchanged-test flake
required a retry. The monitor retained
`.artifacts/ffm-21/all-solvers-result.json` with `hung: false`. These ignored local
logs are worker evidence, not new benchmark measurements or publication inputs.

### Final hygiene

`git diff --check` and `git diff --cached --check` both passed (exit 0, no
diagnostics) for the complete patch, including newly added files. No protected baseline file
other than the permitted end-appended registry is modified; no setup, check,
workflow, toolchain or expected-outcome exception is requested.

## Remaining work and completion decision

The worker's applicable ordinary and dedicated matrix passes, including dynamic
pure discovery, standalone baseline, direct deterministic outcomes, public guide,
actual native SAT/UNSAT cases and full all-solvers coverage. The current completed
PR CI evidence is green on the exact earlier head recorded above; this ticket's
publication-head CI and the maintainer's ordinary non-CoCoA 1.4.1 pin transition
remain pending, not worker blockers.

M1 is still **trusted solver integration**, not a production proof stage.
M2 reconstruction/reification/transport, proof-profile qualification, the full
rule audit, FF optimizer rewrites and the corpus's documented scale/source gaps
remain as described in the handoff. No old lifecycle hang, stale strict-result
mismatch or inherited validation blocker is carried forward without a fresh
failure: none reproduced in this job. Final completion signoff and PR readiness
remain with Riley.

Publication uses the job stack's owner-attributed commit. The optional local
`git commit -m "Verify integrated M1 finite-field boundaries"` attempt returned
exit 128 because the sandbox has no configured Git author identity. No author
identity was fabricated or configured; the validated changes are staged for the
stack. This is not a test failure or a claim that a local commit was created.
