# FFM-18: Scoped inverse and division graph witnesses

## Job summary

Implemented total inverse/division lowering in the bounded native polynomial
translator. Graph obligations are positive query-level assertions; the existing
caller separately asserts the negated residual implication, retaining its
assumptions. Six source-level correspondence lemmas kernel-check. The new live
source run executed 9 SAT and 13 UNSAT cases with the staged backend.
The implementation is present, but this ticket is **not fully validated**.
The independent PROJECT tests check failed in unchanged
`Tests/Smt/CrashLifecycle.lean:597`: the already-exited child produced
`stage=check submission` / `broken pipe` rather than the fixture's required
`closed stdout` wording. Earlier local passes below do not supersede that
independent failure. Full `test-all-solvers` validation also remains blocked by
the unchanged strict transcript expectation in
`Tests/FiniteField/Translation.lean:222`. No protected baseline file or strict
production policy was altered to conceal either failure.
Fresh PROJECT build and tests checks both pass locally, but deterministic
exit-before-submission on the immutable base reproduces the independent
lifecycle diagnostic mismatch. The baseline strict transcript check also
fails. These remain unresolved validation blockers, not FFM-18 production
changes or permission to weaken tests.

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
