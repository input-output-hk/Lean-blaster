# FFM-14 — Route finite-field queries safely after optimization

## Implemented boundary

`Translate.main` invokes finite-field preflight only for the optimized,
undetermined residual, after the existing `only-optimize` return and before
single-solver startup or translation. Queries settled by optimization retain
the existing result and cleanup path. Concurrent startup remains before
optimization; no pre-optimization field scan was introduced.

`Blaster/Smt/FiniteFieldPreflight.lean` provides:

- Scoped residual classification, including instantiated result types, nominal
  carriers inside container types, and operands from different moduli.
- Top-level theorem-parameter opening through the existing optimizer telescope.
  Each exact carrier/modulus is admitted with `admitNativeField` in that local
  context. The continuation receives the checked admissions while their local
  evidence is still valid; no admission cache or cross-query evidence is stored.
- Rejection of symbolic/open native moduli and residual nested quantified or
  higher-order field requirements.
- Backend policy using `resolveSolverConfig`: explicit options take precedence
  over `BLASTER_SOLVER`, then the ordinary Z3 default. Rejection names Z3 and the
  selection source and recommends `solver: cvc5`. No alternate encoding or
  backend override is introduced.
- Concurrent rejection through `exitSmt` before throwing. The existing
  `withSmtSessionOwner` still owns exception and interruption cleanup.

`Blaster/Smt/FiniteFieldCapability.lean` consumes the existing manifest and
`probe_solver.py` offline contract. Its Python adapter loads and validates the
manifest, prohibits network access, invokes `offline_check`, and returns the
exact executable and argv from the same checked inventory. Qualification
requires affirmative version/configuration checks and setup, solving, and model
capabilities. Missing or failed observations fail closed. Proof export and
checked proof-rule coverage are separate properties, not M1 prerequisites.

`Env.lean` accepts the resulting candidate through existing startup functions.
Its exact executable and argv are used without PATH rediscovery or a second
version probe. Ordinary callers retain default discovery. Candidate selection
is restricted to single-cvc5 startup. Existing session retirement now also
clears deferred replay state; no second ownership mechanism was added.

Eligible `only-smt-lib` preflight returns without capability IO. The existing
`setBlasterProcess` dry-run branch records normal setup commands without binary
discovery. Existing option-combination checks, including concurrent dry-run
rejection, remain in force.

## Regression coverage

New `Tests/FiniteField/Routing.lean` and
`Tests/FiniteField/RoutingLifecycle.lean` each import `Tests.Pure`. Their individual
imports were appended at the end of `Tests/FixedIssues.lean`; no existing test
content or protected scripts, CI files, toolchain pins, or lakefiles were edited.

Coverage includes:

- Field occurrences removed or introduced by optimization, scoped evidence
  before/after optimization, and the actual `Translate.main` rejection path.
- Exact carrier/evidence retention, expired-scope rejection, a different-modulus
  operand requiring its own evidence, and opaque container result types.
- Explicit/default/environment backend selection and explicit-option precedence.
- Missing and failed solving capabilities, failed configuration/version checks,
  malformed probe output, successful mocked qualification, and absent/failed
  proof export not obstructing solving.
- cvc5 dry-run setup with a failing injected probe, plus a real Lean subprocess
  with `BLASTER_SOLVER=cvc5` and a PATH containing neither solvers nor Python.
- Both `first` and `agree` with already-started shell-only fake sessions. The
  exception handler checks retirement before the owner finalizer: no sessions,
  emission handle, or deferred replay state; children stopped/reaped; diagnostic
  records retained. Actual per-solver input transcripts contain exit and no
  declaration, assertion, check, or finite-field syntax.
- Admission failure cleanup through the existing owner.

No production axiom, proof closure path, or change to `blasterProven` was added.
Non-FF solver outcomes, first-decisive selection, and verdict/evidence separation
were not changed.

## Runtime scope and limitations

- This is routing/preflight, not native polynomial translation. A qualified or
  dry-run field query can still reach the existing unsupported translation
  boundary (including `PrimeModulus` predicate translation). Native encoding and
  successful end-to-end field solving remain FFM-15 work.
- Live qualification requires the separately staged
  `.artifacts/finite-fields/solving` inventory, the consumed repository manifest,
  fixtures and probe scripts, and Python. Paths follow the existing repository-
  relative staging convention. There is no acquisition or ordinary-cvc5 fallback.
- This checkout has no staged `solving/metadata.json`. The actual CLI smoke
  exercised that failure before production solver startup. Successful live
  qualification against the pinned inventory was not run; affirmative routing
  and startup are exercised with injected capability results, without claiming
  mathematical solving evidence.
- The consumed staged inventory currently supports Linux. Residual quantified
  FF, capability-filtered concurrency, alternate encodings, typed counterexample
  display, and verified proof reconstruction remain outside this ticket.
- No solver-version, manifest, probe-contract, CI, or test-expectation change was
  needed. No downloads were performed.

## Validation history

During implementation, compilation caught an IO-versus-Lean exception type in
preflight and test elaboration issues (reserved identifier and unavailable
`BEq`/`Inhabited` instances); these were corrected. An initial project-test run
passed its pure tiers but failed the new opaque-result regression while it was
using the earlier built classifier. The type-aware collector was then built;
both new files passed directly. No existing test expectation was changed.

A temporary `RoutingSmoke.lean` was run with:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean RoutingSmoke.lean
```

Its expected exit status was 1. Four actual `#blaster` commands observed:

1. Explicit Z3: native-field routing diagnostic recommending `solver: cvc5`.
2. Explicit cvc5: offline capability failure naming the missing staged metadata,
   with no fallback or download.
3. cvc5 `only-smt-lib`: preflight succeeded without discovery/probing and reached
   the existing unsupported `PrimeModulus` translation diagnostic.
4. Reflexive field query with Z3: optimized to `Valid`, without native routing.

The temporary source was removed.

A second temporary source exercised the real startup/retirement functions with
an injected affirmative probe returning an absolute `/bin/sh` fake solver and
its exact argv:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean RoutingLaunchSmoke.lean
```

Exit 0. Observed `offline capability-qualified; backend=cvc5`, the ordinary
cvc5 setup through `(set-logic ALL)`, and successful retirement/reaping with
empty active and deferred state. No discovery of an installed cvc5 was needed.
This exercises the real process path, not live FF solving. The temporary source
was removed.

### Final project build

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

Exit 0; Z3 4.15.2 resolved to
`/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`. Clean build completed successfully:
225 jobs, 102.25 seconds.

### Final project tests

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Exit 0, 241.58 seconds. The finite-field pure runner freshly compiled all 12
discovered modules, `Tests.Pure` passed, and the Z3 tier completed successfully
with 731 jobs. Both new modules were reached through `Tests.FixedIssues`.

The existing lifecycle fault-injection tests emitted their model-unavailable,
timeout, malformed-response, and agreement-artifact warnings. The Z3 tier also
reported `Undetermined` at `Tests/Smt/SmtNat/SmtNatMod.lean:41:56`; the project's
existing policy treats it as a warning, so the gate exited successfully. This
result is recorded, not promoted to `Valid`, suppressed, or hidden by changing
an expected result. No test or check configuration was weakened.

### Direct ticket validation

Each command below exited 0 on the final implementation:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Routing.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/RoutingLifecycle.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/Smt/SolverOutcomePolicy.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/Smt/ResponseLifecycle.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/Smt/CrashLifecycle.lean
```

| File | Observed result | Wall time |
| --- | --- | --- |
| `Routing.lean` | Policy/admission/capability and binary-free subprocess checks passed; two optimizer-settled `Valid` messages. | 3.47 s |
| `RoutingLifecycle.lean` | Both concurrent modes and admission-failure cleanup passed without installed solvers. | 1.14 s |
| `SolverOutcomePolicy.lean` | Passed, no output. | 1.14 s |
| `ResponseLifecycle.lean` | Passed with the intentional model/protocol failure warnings. | 25.04 s |
| `CrashLifecycle.lean` | Passed with the intentional model-unavailable/agreement-artifact warnings. | 12.44 s |

The requested standalone pure gate was also run:

```sh
make test-pure
```

Exit 0, 36.16 seconds: all 12 finite-field pure modules freshly compiled, followed
by a clean successful `Tests.Pure` build (254 jobs). Existing fault-injection
warnings remained visible.

All requested validation commands completed successfully. The unexecuted live
pinned-inventory qualification, FFM-15 end-to-end solving boundary, and the
observed Z3 `Undetermined` warning remain explicitly recorded above. No broader
cvc5 floor/all-solvers tier or proof-reconstruction validation is claimed.

## Delivery

A local commit was attempted with `git commit -m "Route finite-field queries
after optimization"` after staging the eight ticket files. Git refused it
because this checkout has no author identity configured. No identity was
invented or global configuration changed. The ticket files and this report are
staged for the stack's owner-authored commit; no push was attempted.
