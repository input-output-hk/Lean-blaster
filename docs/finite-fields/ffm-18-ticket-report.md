# FFM-18: Scoped inverse and division graph witnesses

## Current job summary

The supplied clean checkout already contains the FFM-18 translator, typed
witness metadata, six scoped correspondence lemmas, optimizer preservation,
`Tests/FiniteField/DivisionEncoding.lean`, its `Tests/FixedIssues.lean` import,
and the automatically discovered live division suite. This job preserves that
implementation; it does not re-add or rewrite existing protected files.
The only source-controlled change in this job is this report's validation
update. The implementation and earlier investigation described below are
inherited history, not changes or command executions performed by this job.

The earlier validation sessions below are historical evidence, not current
blockers. The supplied base includes the later solver-lifecycle and strict
transcript fixes. This job revalidates the inherited implementation from fresh
runs; its final validation section supersedes earlier incomplete outcomes.
No protected fixture, strict diagnostic, expected result, or trust boundary is
changed to obtain a passing result.

The fresh worker validation is green, including both exact PROJECT gates and
the detached all-solvers run (exit 0, 797 jobs). See the current validation
session at the end for exact commands, timings, CI evidence, and M1 limits.

## Changes and invariants

- `Blaster/Smt/Translate/FiniteField.lean` adds `translateInverseGraph`, encoding
  `R_p(b,y) = (b = 0 AND y = 0) OR b*y = 1`. A fresh `declare-const` at sort
  `@FFp` supplies the inverse witness; division multiplies the numerator by the
  denominator's witness. No native inverse/division operator is emitted.
- The per-translation witness cache uses normalized modulus and exact denominator
  expression. Its lifetime is one opened theorem telescope; translation never
  opens residual binders. Distinct calls receive distinct scope identities and
  fresh symbols. Equal-looking expressions at different moduli cannot collide.
  All graph assertions are emitted after successful term translation, outside
  negation, implication, disjunction, and conditional branches. Separate SMT
  assertions are conjunctive, giving graphs AND NOT(assumptions imply goal).
- `Blaster/Smt/FiniteFieldMetadata.lean` adds optional `InverseGraphWitness`
  provenance. The association retains the witness symbol, typed inverse source,
  normalized modulus, local context/instances, and negated query polarity. The
  auxiliary metadata retains the denominator, fresh query scope, and positive
  graph polarity. Auxiliary symbols are not registered as source model variables.
- `Blaster/Optimize/Opaque.lean` recognizes only canonical `Inv.inv`, `Div.div`,
  and `HDiv.hDiv` dictionaries. `Basic.lean`, `Env.lean`, and
  `Rewriting/Utils.lean` perform dictionary recognition in the optimizer's saved
  local context: inverse dictionaries can contain opened `PrimeModulus` evidence.
  This preserves the operations without adding any optimizer rewrite rule.
- `Blaster/FiniteField/DivisionEncoding.lean` proves `inverseGraph_residual`,
  `inverseGraph_negated`, `inverseGraph_assumptions`, `divisionGraph_residual`,
  `inverseGraph_scoped`, and `inverseGraph_nested`. Totality and functionality
  justify existential witness introduction in arbitrary residual predicates,
  including witness-dependent assumptions and nested inverses. Modulus remains
  in each witness's type; local parameters remain inside counterexample scope.
  `Blaster/FiniteField.lean` imports this module for production source coverage.
- New `Tests/FiniteField/DivisionEncoding.lean` inspects exact graph and residual
  assertions, numerator/denominator ordering, sharing, modulus aliases, distinct
  fields/scopes, retained kernel-checkable metadata, nested Boolean polarity,
  assumptions, optimizer preservation, and rejection of unsupported syntax.
  Raw `Fin.div` retains its existing interpretation and does not enter this route.
  Executable transitive axiom guards cover every new correspondence proof and
  regression proof, including missing-target and transitive forbidden-dependency
  controls. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
- New `ff-tests/TestsFF/Division.lean` runs `ff-tests/DivisionSource.lean` using the
  existing root-source harness convention. Cases exercise zero inverse, division
  by zero, zero/zero, guarded and unguarded self-division, characteristic two,
  multiple moduli, nested inverses, operand ordering, and Boolean/ite/implication
  contexts. SAT cases require actual concrete counterexample responses. Source
  semantic proofs use the executable field operations and have axiom guards.
- Protected test-tree changes are only the new DivisionEncoding module and its
  appended import in `Tests/FixedIssues.lean`. Existing tests, `AxiomAudit`,
  scripts, workflows, Lake files, toolchain pins, expected results, and routing
  configuration are unchanged.

## Validation commands and outcomes

The following table records the supplied implementation's earlier validation
history. Fresh investigation and validation results are recorded separately
below; historical passes are not a claim that the independent failure vanished.
Solver artifacts were fetched only by `make ff-stage`; subsequent solver
execution uses the established offline path.

| Command | Observed outcome |
| --- | --- |
| `make ff-stage` | Exit 0. Hash-verified linux-arm64 solving profile staged; offline setup, solving, and model probes passed. Proof export remains the manifest's M2 deferral. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Final exit 0, 282 jobs. New scope/polarity/ordering/axiom guards and unchanged earlier audit pass. |
| `env BLASTER_FF_CVC5=/workspace/lean-blaster/.artifacts/finite-fields/solving/bin/cvc5 lake env lean ff-tests/DivisionSource.lean` | Exit 0. Actual solver execution: 9 SAT and 13 UNSAT cases; expected typed counterexamples observed. |
| `lake env lean DivisionSmoke.lean` | Final exit 0. Temporary reproducer confirmed actionable variable-exponent rejection through `Translate.main`; removed afterward. |
| `cvc5 --show-config` | Image cvc5 1.4.1, commit `2b2e844`, `cocoa: yes`, `poly: yes`. Fresh inspection corrects the earlier `gmp: yes` report: this image reports `gmp: no` and `cln: yes`. |
| `python3 scripts/finite_fields/run_pure_tests.py` | Exit 0, 298 jobs; 17/17 modules freshly compiled. Repeated successfully by the final PROJECT test gate. |
| `make test-cvc5-ff` | Exit 0, 254 jobs; offline probe passed and all child-package sources compiled. Capability: 4 live cases; model: 5 SAT; polynomial: 5 SAT/10 UNSAT; division: 9 SAT/13 UNSAT. |
| Exact PROJECT `make check_blaster` command below | Exit 0, 246 jobs; clean production compilation and complete source coverage, 109.64 seconds. |
| Exact PROJECT `make check_tests` command below | Final exit 0, 235.00 seconds; FF discovery 17/17 (298 jobs), Tests.Pure (275 jobs), and Tests.Z3 (767 jobs). |
| `make test-z3` | Executed by `make check_tests` with Z3 4.15.2 alone on PATH; exit 0, 767 jobs. Not a separate default-assurance-Z3 run. |
| `env BLASTER_STRICT_CVC5_RESULTS=1 lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Exit 0, 282 jobs, after explicitly declaring the new transcript harness's already-asserted Undetermined outcome. |
| `make test-all-solvers` with the PATH below | First attempt exit 2 after 191.04 seconds: strict dry-run errors in existing Translation and initially in new DivisionEncoding. Second attempt interrupted at 2400 seconds in existing CrashLifecycle; no successful full-suite/source-coverage result is claimed. |

The exact PROJECT commands were:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both resolved `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.
The ordinary all-solvers attempts additionally exposed the image's cvc5:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"; command -v z3 && z3 --version && command -v cvc5 && make test-all-solvers
```

The ordinary cvc5 prerequisite `ff-tests/OrdinaryCvc5Baseline.lean` passed in
the first all-solvers run. The required PROJECT test gate passed again after the
final new-test harness change. Expected lifecycle negative controls emitted
model-unavailable/timeout/malformed-response warnings; the Z3 gate also emitted
an Undetermined warning at `Tests/Smt/SmtNat/SmtNatMod.lean:37`. Neither gate
failed on those warnings.

Initial integrated compilation caught new test-harness indexing and concrete
proof elaboration errors, corrected without changing expected behavior. It also
exposed a genuine opacity-context bug: an inverse depending on local primality
evidence produced `unknown free variable` before translation. The temporary
reproducer showed that failure before the saved-context correction and the
bounded-fragment diagnostic afterward. The permanent regression exercises that
same unsupported variable-power path through `Translate.main`.

The axiom audits intentionally emit `declaration uses 'sorryAx'` while creating
scoped negative-control wrappers. The guards reject those dependencies, and the
wrappers do not escape the restored environment. No production axiom or admitted
proof was added.

### Remaining full-suite validation blocker

The existing Translation regression sets `onlySmtLib := true` and explicitly
checks `isUndeterminedResult`, but leaves `solveResult` unspecified. In the
all-solvers target's `BLASTER_STRICT_CVC5_RESULTS=1` environment,
`Translate.main ... false` still logs `Unexpected Undetermined`. This failure
was observed twice in that module's first full-run output. Its code and expected
result were not edited. The new DivisionEncoding module now explicitly declares
`.ExpectedUndetermined` for its transcript-only options, preserving its original
result assertion; its separate strict build passes.

The second full all-solvers attempt did not finish: after 2400 seconds the
remaining process was compiling the existing `Tests/Smt/CrashLifecycle.lean`,
with its synthetic `/bin/sh` solver waiting in its input loop. The timed-out
attempt's remaining make/Lake/Lean/fixture processes were terminated. No cause
for that unrelated hang is asserted; the final exact PROJECT test gate
subsequently completed, including CrashLifecycle.

A green all-solvers signoff still requires repair of the existing protected
Translation transcript expectation and completion of the full lane. Modifying
that file requires the specified executable semantic validator or narrow owner
gate binding the immutable approved base, exact patch, named test and old/new
outcomes, with the required risk/G6 evidence. This ticket has no such grant.
The alternative is not to suppress strict diagnostics, skip the module, change
the target, or weaken expected solver results. These remain explicit incomplete
validation items, not a passing ticket signoff.

## Scope and external lanes

Trusted M1 closure is unchanged: these are kernel-checked source correspondence
lemmas, not verified SMT reconstruction or transport of an arbitrary original
goal. `blasterProven` is unchanged. No Fermat optimizer rewrite, residual quantifier
support, integer/variable-exponent translation, mixed representation encoding,
new model reconstruction, or concurrent native-FF route is introduced.

CI-only lanes for this ticket's pushed head remain pending on
[PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412): ordinary cvc5
without CoCoA, cvc5 1.2.1 floor, x86_64, and the finite-fields workflow. This worker
has cvc5 1.4.1 with CoCoA on arm64; no replacement backend was downloaded. The PR
API observed head `c37f90930f00c4085c08cdddd464cdac99669945`, before publication of
these local edits; results for that earlier head are not claimed for this ticket.
Publication, external lane completion, and maintainer signoff are not claimed.

## Independent-check investigation

The independent tests check failed at unchanged
`Tests/Smt/CrashLifecycle.lean:597` with an already-exited solver diagnostic
containing `stage=check submission` and `broken pipe`. This is retained as a
failure, not dismissed because an earlier worker run passed.

The fixture starts a shell that writes stderr and exits immediately, without
reading stdin (`spawnDeadChild`, lines 75–83). It does not synchronize exit
against command submission. If submission wins, the stdout read reaches EOF;
if exit wins, the command flush encounters EPIPE. Production preserves the
actual failing stage, reports a process failure without a solver verdict,
retires the session, and captures stderr on both paths. The assertion at lines
268–269 accepts only the EOF wording.

No production-only correction is justified by that evidence. EPIPE proves the
stdin reader closed, not that stdout closed; replacing the diagnostic would
misrepresent the operation. Reading stdout after EPIPE could block, and killing
the child first would manufacture EOF. Correcting the fixture would require
permission to accept both contextual failures or to synchronize its intended
schedule. Existing protected tests and strict policy remain unchanged.

### Immutable-base reproduction

Created an isolated checkout with
`git worktree add --detach .artifacts/ffm18-ticket-base HEAD`, at immutable
ticket base `24efabc`, without the FFM-18 working-tree changes. No protected
source in that checkout was edited.

From that directory:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && LEAN_NUM_THREADS=5 lake build Tests.Smt.CrashLifecycle
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; lake env lean ExitedChildProbe.lean
```

The unchanged lifecycle module passed once (245 jobs, 164.91 seconds).
The throwaway probe forced the other schedule: spawn the same shell
(`echo 'FAKE_DEAD_CHILD: deliberate stderr' >&2; exit 17`), await
`child.wait`, require exit code 17, then invoke `checkSat` in the same single-Z3
session configuration and catch its diagnostic. Session retirement and retained
stderr passed; the protected fixture's `closed stdout` requirement failed.
After correcting an initial syntax error in the probe's record literal, the
probe exited 1 in 1.11 seconds with:

```text
z3 solver failure: solver=z3; stage=check submission; command=(check-sat); response=IO error while executing (check-sat): resource vanished (error code: 32, broken pipe); elapsed=1ms
Solver stderr:
FAKE_DEAD_CHILD: deliberate stderr
ExitedChildProbe.lean:6:0: error: baseline reproduces the protected already-exited diagnostic mismatch
```

**Baseline reproduces: yes, with exit-before-submission synchronized.** The
unmodified fixture's single pass and the deterministic failure are consistent
with a scheduling race. This is not a claim that the unsynchronized fixture
failed in that baseline invocation. The probe and isolated checkout are
validation scaffolding, not committed regression changes.

### Fresh validation

The staged artifacts were already present. `make ff-stage` was not repeated;
fresh validation used only the provisioned offline profile.

| Command | Observed outcome |
| --- | --- |
| `python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --offline --check` | Exit 0; setup, solving, model, and all four capability cases pass. Proof export remains deferred to M2. |
| Exact PROJECT `make check_blaster` command above | Exit 0; 246 jobs, complete production source coverage, 136.62 seconds. |
| `cvc5 --show-config` | Exit 0; 1.4.1, `cocoa: yes`, `cln: yes`, `gmp: no`, `poly: yes`. |
| `env BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 lake build Tests.FiniteField.Translation` (isolated immutable base) | Exit 1, 29.44 seconds; unchanged `Translation.lean:222` emits two `Unexpected Undetermined` errors. This independently establishes the all-solvers strict-transcript blocker on the ticket base. |
| Exact PROJECT `make check_tests` command above | Exit 0, 241.71 seconds. FF discovery freshly compiled 17/17 modules (298 jobs), Tests.Pure passed (275 jobs), and Tests.Z3 passed (767 jobs). This local pass does not resolve the independently observed lifecycle race. |
| `python3 scripts/finite_fields/run_pure_tests.py` | Executed unchanged by the exact PROJECT test gate; exit 0, all 17 discovered modules freshly compiled, including DivisionEncoding and AxiomAudit. |
| `make test-z3` | Executed unchanged by the exact PROJECT test gate with only Z3 4.15.2 on PATH; exit 0, 767 jobs. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Exit 0, 282 jobs; reuses modules freshly compiled by the preceding PROJECT test gate. |
| `make test-cvc5-ff` | Exit 0, 254 jobs; complete child-package coverage and offline probe pass. Fresh live division execution: 9 SAT / 13 UNSAT. Earlier capability (4 cases), model (5 SAT), and polynomial (5 SAT / 10 UNSAT) modules also pass. Combined with the preceding targeted build: 28.27 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"; command -v z3 && z3 --version && command -v cvc5 && make test-all-solvers` | Exit 2, 178.43 seconds. Ordinary cvc5 baseline passed; full target failed on unchanged `Tests.FiniteField.Translation`. It completed rather than hanging in this attempt. No complete Tests source-coverage pass is claimed. |

The temporary probe and isolated baseline worktree were removed after the
baseline investigation. No solver was downloaded or provisioned during these
fresh checks. PR #412's API still reports head
`c37f90930f00c4085c08cdddd464cdac99669945`; this predates the local ticket patch
and cannot supply CI evidence for it.
The optional local commit attempt failed because Git author identity is unset.
No identity was invented or configured. Ticket files are staged for the stack's
owner-authored publication commit; no local commit or push is claimed.

## Acceptance accounting

Every ticket criterion is listed below. **Not every criterion is fully signed
off:** criterion 6's complete non-FF regression validation is blocked, despite
its implementation and targeted raw-Fin/axiom checks being satisfied. Criterion
8's report is ready, but publication is pending. No green overall ticket
acceptance is claimed.

| # | Criterion | Status and evidence |
| --- | --- | --- |
| 1 | Fresh typed inverse graph; numerator times denominator witness | Met. Exact declarations, graph assertions, denominator metadata, and ordered multiplication are checked in DivisionEncoding. |
| 2 | Positive graph obligations with negated query; scoped correspondence preserving assumptions, modulus and polarity | Met. Six kernel-checked correspondence lemmas; exact query/assumption assertions and positive graph metadata checks. |
| 3 | Context/scope/modulus-aware witness reuse; no binder-dependent global hoisting | Met. Per-call cache, fresh scope identities, retained local contexts, normalized modulus keys, alias/distinct-field/distinct-call and nested-witness regressions. |
| 4 | Actionable rejection of residual binders, unsupported powers and representation operations | Met. Direct and full-translation rejection cases check diagnostics and absence of unsupported commands/assertions. |
| 5 | Live source semantics for zero, self-division, characteristic two, distinct fields, nesting and Boolean occurrences | Met in the staged offline live suite: 9 SAT and 13 UNSAT cases, with source proofs and actual solver-response checks. |
| 6 | Raw Fin/non-FF unchanged; transitive axiom boundary; no prior-audit edit, new rewrite or production axiom | Partially validated. Raw Fin semantics and executable new/prior axiom guards pass; trusted closure is unchanged. Complete non-FF validation remains blocked by the independent lifecycle failure and baseline strict transcript mismatch. |
| 7 | Only permitted protected test writes | Met. New DivisionEncoding module and one appended FixedIssues import only; earlier protected files remain unchanged. |
| 8 | Ticket report and job summary include changes, exact commands/outcomes and limitations | Report and final job summary complete; publication pending. Historical passes, independent failure, baseline reproduction, fresh checks and pending external lanes are distinguished. Files are staged, but the optional local commit failed for missing Git identity. |

The prerequisite for unblocking the protected fixtures is a narrowly scoped
owner gate or executable semantic validator binding the immutable approved
base, exact patch, named tests, old/new outcomes, and required risk/G6 evidence.
There is no permission here to change either existing test, weaken strict
policy, or treat their failures as passing. CI-only lanes remain pending for
ordinary cvc5 without CoCoA, cvc5 1.2.1, x86_64, and the finite-fields workflow
at this ticket's eventual published head.

## Inherited checkout validation — 2026-10-28

This run started with a clean worktree containing all the implementation and
regression files listed above. No production code, tests, scripts, workflows,
Lake configuration, toolchain pins, or aggregate imports were changed. In
particular, DivisionEncoding is already a protected existing test in this
checkout, not a newly writable file. The historical staging and commit remarks
above describe previous work only.

Inspection confirmed the scoped cache is allocated inside `withNativeFieldQuery`
and discarded when its telescope closes. Graphs are asserted only after the
residual and its premises have translated successfully. Their positive
assertion polarity is separate from the source query's negated polarity.
The six correspondence proofs use the public totality/functionality laws;
the current production import includes their module. The pure suite checks
the exact denominator, ordered multiplication, graph placement, normalized
moduli, independent calls, retained local contexts, unsupported syntax, raw
Fin behavior, and transitive axiom boundaries. The child package's existing
`.andSubmodules` glob includes the live Division module without aggregate edits.

### Commands executed in the inherited run

The required PROJECT commands were executed verbatim:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both select `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.
The toolchain reports Lake `5.0.0-src+797c613`, Lean `4.24.0`.

| Command | Current observed outcome |
| --- | --- |
| `make ff-stage` | Passed, exit 0, 3.80 seconds. Staged the hash-verified linux-arm64 solving profile; offline setup, solving, model, and all four capability cases passed. Proof export remains deferred to M2. This was the only artifact staging command. |
| `cvc5 --show-config` | Passed, exit 0. Image cvc5 1.4.1, commit `2b2e844`; `cocoa: yes`, `poly: yes`, `cln: yes`, `gmp: no`. No additional ordinary cvc5 was provisioned. |
| Exact PROJECT `make check_blaster` command above | Passed, exit 0, 110.52 seconds, 246 jobs. Clean production build and complete source coverage, including the translator and correspondence module. |
| Exact PROJECT `make check_tests` command above | Passed, exit 0, 255.37 seconds. Fresh FF discovery passed (17/17 modules, 298 jobs), followed by Tests.Pure (275 jobs) and Tests.Z3 (767 jobs). This pass does not establish that the historically observed lifecycle race is repaired. |
| `python3 scripts/finite_fields/run_pure_tests.py` | Executed by the unchanged PROJECT test target; passed with all 17 discovered modules freshly compiled, including DivisionEncoding and AxiomAudit. |
| `make test-z3` | Executed by the unchanged PROJECT test target with Z3 4.15.2 alone on PATH; passed, 767 jobs. No default-assurance-Z3 test run is claimed. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Passed, exit 0, 282 jobs; reused modules freshly compiled during the PROJECT test gate. |
| `make test-cvc5-ff` | Passed, exit 0, 254 jobs with complete child-package source coverage. Offline capability probe passed. Fresh live execution: Division 9 SAT / 13 UNSAT; Polynomial 5 SAT / 10 UNSAT; Model 5 SAT; Capability 4 cases. The targeted build and this target were run sequentially with `&&`, taking 28.23 seconds combined. |

The ordinary all-solvers command uses release Z3 and the image's ordinary cvc5,
not the staged FF executable:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"; command -v z3 && z3 --version && command -v cvc5 && make test-all-solvers
```

The live division run exercised the actual translation/solver/model path.
In particular, unguarded self-division returned the zero counterexample in
characteristics 7 and 2, and the nested implication case returned zero rather
than becoming spuriously valid through incorrect graph polarity. Pure command
checks and source proofs also passed. The axiom-audit warnings about `sorryAx`
come from the existing scoped forbidden-dependency negative controls, not
from an admitted production correspondence theorem.

**All-solvers outcome:** failed, exit 2, 184.43 seconds. The ordinary cvc5
baseline passed. The only failed Lean target was
`Tests.FiniteField.Translation`, with two
`Tests/FiniteField/Translation.lean:222:0: Unexpected Undetermined` errors.
Its existing transcript options set `onlySmtLib := true` without declaring
an expected Undetermined result; the run at line 222 explicitly requires
Undetermined, but the lane's strict result policy rejects the unspecified
expectation. DivisionEncoding and AxiomAudit both freshly compiled successfully
under the same strict lane. CrashLifecycle also completed in this invocation;
no fix for its inherited race is claimed.

### Remaining limitations and signoff

- Full all-solvers/source-coverage acceptance remains blocked by the protected
  Translation fixture. A narrowly scoped owner gate or executable semantic
  validator must bind the immutable approved base, exact proposed test patch,
  named tests, old/new outcomes, and required risk/G6 evidence before changing
  it. This job neither changes that fixture nor suppresses strict diagnostics.
- The inherited lifecycle race remains a known risk despite this run's passing
  PROJECT checks. No isolated re-reproduction or unrelated production change
  was made in this job.
- CI-only lanes for this job's eventual published head are **pending**:
  ordinary cvc5 without CoCoA, cvc5 1.2.1 floor, x86_64, and the finite-fields
  workflow on [PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412).
  No current-head CI result is claimed. Running the Cvc5Floor module with image
  cvc5 1.4.1 during all-solvers is not a substitute for the 1.2.1 version lane.
- Trusted M1 closure, preflight/routing, `blasterProven`, and all existing
  operation semantics are unchanged. These checks do not establish verified
  SMT reconstruction or residual-quantifier support.
- The report is updated for the stack's publication commit. No local commit,
  push, remote CI completion, or maintainer signoff is claimed.

**Job result:** the already-present FFM-18 implementation passes the targeted
pure/axiom and staged live checks, and both required PROJECT checks pass.
Only this report changed. Overall ticket signoff is not green because the
required all-solvers lane still fails in the existing protected fixture.

## Prior validation session — 2026-10-28

### Change scope and job summary

The supplied checkout already contains all FFM-18 production code, six
correspondence lemmas, pure DivisionEncoding regressions, their FixedIssues
import, and live Division regressions. This session inspected those existing
files rather than recreating or modifying them. Only this ticket report changes;
there are no protected test-tree writes, production changes, or changes to
scripts, workflows, Lake files, toolchain pins, expected results, routing, or
the trusted M1 closure.

Inspection confirmed positive graph assertions are emitted after successful
translation of the residual and its assumptions. The inverse cache is local
to one opened query, keyed by normalized modulus and exact denominator.
Metadata retains the query scope, local context/instances, denominator, typed
inverse source, and distinct graph/query polarities. Division multiplies the
numerator by the denominator witness. The existing regressions inspect these
properties, residual-syntax rejection, raw Fin behavior, and transitive axioms.
The pure runner discovers DivisionEncoding, and the child package's existing
`.andSubmodules` glob discovers Division without aggregate changes.

### Commands and observed results

The PROJECT commands used in this session are exactly:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

| Command | Observed result in this session |
| --- | --- |
| `make ff-stage` | Exit 0, 3.88 seconds. Staged the pinned linux-arm64 solving profile. Offline setup, solving, model, and four capability probes passed; proof export remains deferred to M2. This was the only staging command. |
| `cvc5 --show-config` | Exit 0. Image cvc5 1.4.1, commit `2b2e844`, `cocoa: yes`, `poly: yes`, `cln: yes`, `gmp: no`. No additional ordinary cvc5 was provisioned. |
| Exact PROJECT `make check_blaster` command above | Exit 0, 113.16 seconds, 246 jobs. Clean production build and full source coverage passed, including scoped correspondence and translation. Selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2. |
| Exact PROJECT `make check_tests` command above | Exit 0, 245.89 seconds. FF discovery freshly compiled all 17 modules (298 jobs), Tests.Pure passed (275 jobs), and Tests.Z3 passed (767 jobs), with release Z3 4.15.2 alone on PATH. |
| `python3 scripts/finite_fields/run_pure_tests.py` | Executed by the unchanged PROJECT test target; exit 0, 17/17 modules freshly compiled, including DivisionEncoding and AxiomAudit. |
| `make test-z3` | Executed by the unchanged PROJECT test target; exit 0, 767 jobs. No default-assurance-Z3 run is claimed. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Exit 0, 282 jobs; reused modules freshly compiled by the PROJECT test target. |
| `make test-cvc5-ff` | Exit 0, 254 jobs, complete child-package coverage. Offline capability probe passed. Fresh live Division execution: 9 SAT / 13 UNSAT; Polynomial: 5 SAT / 10 UNSAT; Model: 5 SAT; Capability: 4 cases. Run sequentially with the targeted build using `&&`; combined time 26.74 seconds. |

The live division execution returned zero counterexamples for unguarded
self-division in characteristics 7 and 2 and for the nested implication case.
The pure checks exercised command shape, witness reuse, scope, polarity,
unsupported syntax, and proof axioms. Audit warnings about `sorryAx` arise from
the existing scoped forbidden-dependency negative controls; no admitted
production proof was added. Lifecycle negative-control warnings and the
existing `SmtNatMod.lean:37` Undetermined warning did not fail the PROJECT gate.

The ordinary all-solvers command uses release Z3 and the image's cvc5, not the
staged finite-field executable:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"; command -v z3 && z3 --version && command -v cvc5 && make test-all-solvers
```

**All-solvers outcome in this session:** incomplete; the command was terminated
at its 600-second deadline (600.08 seconds observed). The ordinary cvc5 baseline
passed before the full Tests build began. The captured output reached
727/797 jobs and showed successful ConcurrentSolvers and ConcurrentDump modules,
but no successful full build or source-coverage result. No completed strict
Translation result is claimed for this invocation. The strict transcript
mismatch documented in the inherited runs remains unresolved.

After timeout, process inspection found one orphaned synthetic `/bin/sh` solver
and its `sleep 10` child. The fixture exited before an explicit termination
attempt could find its process group; a subsequent process listing confirmed
no make, Lake, Lean, solver, or synthetic-fixture processes remained.
The timeout alone does not establish a new root cause or repair the inherited
lifecycle race. No test or production diagnostic was changed to conceal it.

### Remaining limitations and acceptance

- Required PROJECT checks and targeted pure/axiom/live FF checks passed in this
  session. The requested all-solvers lane did not complete, so full non-FF
  source-coverage acceptance and overall ticket signoff remain incomplete.
- The protected `Tests/FiniteField/Translation.lean` strict-transcript mismatch
  and `Tests/Smt/CrashLifecycle.lean` race remain inherited blockers/risks.
  Repairing an existing protected fixture requires the narrowly scoped owner
  gate or executable semantic validator described above, binding the immutable
  approved base, exact patch, named tests, old/new outcomes, and required risk/G6
  evidence. This job has no such authorization and does not weaken strict policy.
- CI-only lanes for this job's eventual published head remain **pending**:
  ordinary cvc5 without CoCoA, cvc5 1.2.1 floor, x86_64, and the finite-fields
  workflow on [PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412).
  No current-head CI result is claimed. Image cvc5 1.4.1 executing the Cvc5Floor
  module is not evidence for the 1.2.1-version lane.
- This report is ready for the stack's owner-authored publication commit.
  No local commit, push, remote CI completion, or maintainer signoff is claimed.

**Prior job result:** existing FFM-18 implementation preserved; only this report
updated. All targeted division checks and both required PROJECT checks passed.
All-solvers validation remains incomplete; no green overall acceptance is claimed.

## Prior validation session — 2026-10-28, staging at 14:37 UTC

### Change scope and job summary

This session changes only this report. The supplied checkout already implements
FFM-18, including scoped typed witnesses, positive graph assertions alongside
the negated residual, six kernel-checked correspondence lemmas, canonical
Inv/Div opacity, and both pure and live regression modules. Inspection and fresh
execution found no division-specific change necessary. No protected test,
script, workflow, Lake file, toolchain pin, production axiom, optimizer rewrite,
or expected result was changed. No additional FixedIssues import was needed.

The implementation retains normalized modulus and exact denominator identity
in a query-local cache, with saved local context/instances and scope identity
in typed metadata. Graph polarity is positive; source-query polarity is negated.
The pure regressions check operand ordering, assumptions, nested Boolean
contexts, scope isolation, unsupported syntax, raw Fin.div separation, and the
transitive axiom boundary. The live suite exercises the actual translation and
staged solver, rather than substituting source evaluation for solver execution.

### Exact commands and observed outcomes

The required PROJECT commands were run exactly:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.

| Command | Observed outcome in this session |
| --- | --- |
| `make ff-stage` | Exit 0, 3.64 seconds. Pinned linux-arm64 solving profile staged; offline setup, solving, model, and four capability probes passed. Only staging could download artifacts. |
| `cvc5 --show-config` | Exit 0. Image cvc5 1.4.1, commit `2b2e844`; `cocoa: yes`, `poly: yes`, `cln: yes`, `gmp: no`. No replacement ordinary solver provisioned. |
| Exact PROJECT `make check_blaster` above | Exit 0, 118.97 seconds, 246 jobs; clean production compilation and complete source coverage. |
| Exact PROJECT `make check_tests` above | Exit 0, 253.82 seconds; all 17 pure FF modules freshly compiled (298 jobs), Tests.Pure passed (275 jobs), Tests.Z3 passed (767 jobs). |
| `python3 scripts/finite_fields/run_pure_tests.py` | Executed by the unchanged PROJECT test target; exit 0, 17/17 modules freshly compiled, including DivisionEncoding and AxiomAudit. |
| `make test-z3` | Executed by the unchanged PROJECT test target with release Z3 4.15.2; exit 0, 767 jobs. No default-assurance-Z3 run claimed. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Exit 0, 282 jobs; reused the modules freshly compiled by the PROJECT test target. |
| `make test-cvc5-ff` | Exit 0, 254 jobs; offline probe and complete child-package source coverage passed. Fresh Division execution: 9 SAT / 13 UNSAT. Capability: 4 cases; Model: 5 SAT; Polynomial: 5 SAT / 10 UNSAT. |

The targeted build and live target were run sequentially as
`lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit && make test-cvc5-ff`;
combined elapsed time was 26.40 seconds. Live counterexamples included zero for
unguarded self-division in characteristics 7 and 2, and for the nested
implication case. The audit's scoped forbidden-dependency controls emitted
their existing `sorryAx` warnings; no production proof was admitted. Existing
lifecycle negative-control warnings and Undetermined warnings at
`Tests/Smt/SmtNat/SmtNatMod.lean:35` and `:37` did not fail the PROJECT gate.

The ordinary all-solvers command was:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin"; command -v z3 && z3 --version && command -v cvc5 && make test-all-solvers
```

**Outcome: incomplete**, terminated at the 600-second deadline (600.07 seconds
observed). The ordinary cvc5 baseline passed. Output reached 727/797 jobs,
including successful ConcurrentSolvers and ConcurrentDump modules, but no
complete Tests build or source-coverage result. No completed strict Translation
result is claimed for this invocation. After timeout, process inspection found
an orphaned synthetic shell solver and its sleep child; they exited before
explicit termination could find their process group. A subsequent process
listing confirmed no remaining make, Lake, Lean, solver, or fixture processes.

### Remaining limitations and prerequisite

Overall acceptance remains incomplete because all-solvers did not finish.
The inherited protected Translation strict-transcript mismatch and
CrashLifecycle race remain unresolved; the timeout alone does not establish
a new cause. They were not separately rerun to reconfirm known failures.
Any protected-fixture correction requires the scoped owner gate or executable
semantic validator binding the immutable base, exact patch, named tests,
old/new outcomes, and required risk/G6 evidence. No such grant is present.
Production diagnostics and strict policy were not weakened to avoid that gate.

CI-only lanes for this job's eventual published head remain **pending** on
[PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412):
ordinary cvc5 without CoCoA, cvc5 1.2.1 floor, x86_64, and the finite-fields
workflow. No current-head CI result, local commit, push, or maintainer signoff
is claimed. The report is supplied for the stack's owner-authored publication
commit. Trusted M1 closure remains unchanged; these results do not establish
verified SMT reconstruction, residual-quantifier support, or M2 proof export.

**Prior job result:** inherited implementation preserved; report updated.
Both required PROJECT gates and targeted pure/axiom/live division checks pass.
All-solvers validation and overall ticket signoff remain incomplete.

## Current validation session — 2026-10-28, staging at 16:54 UTC

### Change scope and acceptance review

This job preserves the already-present FFM-18 implementation and changes only
this report. No production code, protected test, script, workflow, Lake file,
toolchain pin, expected outcome, or aggregate import was changed.

Source review found no acceptance gap in:

- Typed inverse witnesses and numerator-times-denominator-witness lowering.
- Per-query cache lifetime, exact denominator identity, normalized modulus,
  retained local context/instances, and distinct scope identities.
- Positive graph assertions alongside the negated residual implication,
  including witness-dependent assumptions and nested Boolean occurrences.
- Canonical Inv/Div opacity, raw Fin division separation, bounded-fragment
  diagnostics, and unchanged routing/preflight and trusted M1 closure.
- All six kernel-checked correspondence lemmas and their executable transitive
  axiom guards in DivisionEncoding, without modifying the earlier AxiomAudit.
- Automatic discovery of the pure module and live child-package division module.

### Fresh worker commands and outcomes

Validation targets were serialized because they clear shared build outputs.
`make ff-stage` was the only artifact-download step. Subsequent finite-field
solver runs used the staged profile through the existing offline target.

| Command | Observed outcome |
| --- | --- |
| `make ff-stage` | Exit 0, 3.82 seconds. Hash-verified linux-arm64 solving profile staged; offline setup, solving, model, configuration, and all four capability cases passed. |
| `cvc5 --show-config` | Exit 0. Image cvc5 1.4.1, commit `2b2e844`; `cocoa: yes`, `poly: yes`, `cln: yes`, `gmp: no`. No other ordinary cvc5 was provisioned. |
| `lake build Tests.FiniteField.DivisionEncoding Tests.FiniteField.AxiomAudit` | Exit 0, 149.59 seconds, 282 jobs. Both regression modules freshly compiled. |
| `python3 scripts/finite_fields/run_pure_tests.py` | Exit 0, 298 jobs; all 17 discovered modules freshly compiled, including DivisionEncoding and the unchanged AxiomAudit. |
| `make test-cvc5-ff` | Exit 0, 254 jobs; offline probe and complete child-package coverage passed. Division executed 9 SAT / 13 UNSAT cases; Polynomial 5 SAT / 10 UNSAT; Model 5 SAT; Capability 4 cases. |

The pure and live commands ran as
`python3 scripts/finite_fields/run_pure_tests.py && make test-cvc5-ff`
in 48.20 seconds combined. The live division harness exercised the actual
translator and staged solver. Counterexamples included zero for unguarded
self-division in characteristics 7 and 2, and distinct numerator/denominator
values in asymmetric division cases.

The axiom audits emitted their existing scoped negative-control `sorryAx`
warnings; their guards passed. No production admitted proof or axiom was added.

### Latest completed public CI evidence

Observed through the public GitHub API during this job, for
[PR #412](https://github.com/input-output-hk/Lean-blaster/pull/412).
Every result below ran on head
`2b140a7c3bde1f52534605bc628ebdf52dfb13d4`; these are completed results for that
head, not claims about CI on this report's eventual publication commit.

| Lane | Latest completed result | Evidence |
| --- | --- | --- |
| Ordinary non-CoCoA cvc5 1.3.4, Linux x86_64 | Success | [solver tests (cvc5)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726797938/job/122952125046) |
| cvc5 1.2.1 support floor, Linux x86_64 | Success | [solver tests (cvc5-1.2.1)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726797938/job/122952125682) |
| Z3, Linux x86_64 | Success | [solver tests (z3)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726797938/job/122952125583) |
| All-solvers, Linux x86_64 | Success | [solver tests (all-solvers)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726797938/job/122952125659) |
| Finite-fields workflow, Linux x86_64 | Success | [finite-field solving (linux-x86_64)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726798068/job/122952124888) |
| Finite-fields workflow, Linux arm64 | Success | [finite-field solving (linux-arm64)](https://github.com/input-output-hk/Lean-blaster/actions/runs/40726798068/job/122952125596) |

The ordinary workflow installs the non-GPL static cvc5 distribution at 1.3.4
and the separate 1.2.1 floor. Those binaries/platforms were not downloaded or
substituted for the worker's image cvc5 1.4.1. All listed lanes are green; there
is no red-lane failing test to report. CI was neither rerun nor awaited.

### Required PROJECT checks

Run exactly as configured:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.

| Command | Observed outcome |
| --- | --- |
| Exact PROJECT `make check_blaster` above | Exit 0, 115.22 seconds, 246 jobs; clean production build and complete source coverage. |
| Exact PROJECT `make check_tests` above | Exit 0, 252.46 seconds; FF discovery 17/17 freshly compiled (298 jobs), Tests.Pure (275 jobs), and Tests.Z3 (767 jobs). |
| `make test-z3` | Executed successfully by the unchanged `make check_tests` recipe, with release Z3 4.15.2 alone on PATH. No separate default-assurance-Z3 run is claimed. |

Existing lifecycle negative controls emitted model-response warnings.
`Tests/Smt/SmtNat/SmtNatMod.lean:41` emitted an Undetermined warning;
the configured PROJECT gate passed without changing that expected behavior.

### Detached all-solvers completion

The process was launched with `subprocess.Popen`, `start_new_session=True`,
stdin disconnected, and stdout/stderr directed to
`.artifacts/ffm18-validation/all-solvers.log`. The executed argv was
`["nohup", "make", "test-all-solvers"]`, working directory the repository root.
Its PATH was:

```text
/opt/z3-4.15.2-arm64-glibc-2.34/bin:/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin
```

Equivalent shell launch:

```sh
PATH="/opt/z3-4.15.2-arm64-glibc-2.34/bin:/home/agent/.elan/bin:/usr/local/bin:/usr/bin:/bin" nohup make test-all-solvers > .artifacts/ffm18-validation/all-solvers.log 2>&1 &
```

An independent supervisor waited for the real child exit status, checked log
progress every 60 seconds, and enforced the requested 20-minute no-output hang
threshold. There was no command deadline and no hang. **Exit 0, 182.75 seconds,
797 jobs**, including the ordinary cvc5 baseline and complete Tests source
coverage. DivisionEncoding, AxiomAudit, Translation, CrashLifecycle,
ConcurrentSolvers, and ConcurrentDump all freshly compiled in this strict run.
The log ends with `Build completed successfully (797 jobs).`

The earlier strict Translation mismatch and CrashLifecycle hang did not recur.
They are not current blockers; this run supersedes the historical incomplete
all-solvers claims above. No retry, test weakening, protected-file edit, or
replacement solver was used.

### Current job result and remaining limits

All requested worker validation completed successfully. The inherited FFM-18
implementation meets the scoped encoding acceptance criteria; no further code
change was necessary. The only committed deliverable from this job is the
updated ticket report, including this job summary and fresh validation evidence.
Protected test-tree writes in this job: none.

No worker check remains incomplete. Non-CoCoA cvc5 1.3.4, cvc5 1.2.1, and x86_64
were not reproduced locally; their latest completed public CI results are
recorded above with the exact head SHA. CI for the eventual publication commit
is not claimed, and maintainer completion signoff remains with Riley.

Trusted M1 closure is unchanged. The correspondence lemmas are kernel-checked
source semantics, not verified solver-proof reconstruction or original-goal
transport. Residual quantifiers, variable/integer exponent translation, and
representation-level/mixed encodings remain intentionally unsupported.
Proof export remains the staged manifest's M2 deferral, not a failed required
probe. No new optimizer rewrite, production axiom, or widening of
`blasterProven` was introduced.
