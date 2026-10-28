# Finite-field review follow-ups

Open items from the 2026-10-28 review of PR #412 (`agent/feat-cvc5-ff` into
`feat/cvc5-concurrency`). They are not fixed on this branch. Items the review
fixed directly are listed at the end for reference.

## Before merge

1. **Native solving only works inside a Linux checkout of this repository.**
   Every native query runs `python3` on `docs/finite-fields/solver-manifest.json`,
   located by walking up from the working directory
   (`Blaster/Smt/FiniteFieldCapability.lean:67-99`), and the staged inventory
   supports Linux only. A project that depends on Blaster through Lake, or an
   editor rooted in such a project, fails preflight. The probe also reruns on
   every query. `native-support.md` says downstream clients can use the route,
   and the README does not mention the limits. Either make the solver
   location configurable and cache the probe, or document the limitation
   plainly in both places.

2. **Committed benchmark data is stale and not reproducible.**
   `benchmarks/finite-fields/` is about 21 MB; `results.json` alone is 19.7 MB.
   `config.json` hashes no longer match HEAD, so `benchmark.py` refuses to run.
   It also pins tools under `/home/agent/.elan` and records container
   hostnames, cpuinfo and a PATH containing the staged cvc5. Keep the summaries
   (`m1-measurements.md`, case definitions) and move raw runs to a CI or
   release artifact.

3. **Documentation is mostly process log.** About 7,200 lines across
   `docs/finite-fields/`. Proposed reduction to about 1,300 lines:
   - Drop the 14 `ffm-NN-ticket-report.md` files and the superseded
     `m1-execution-decision.md`, `m1-toolchain-decision.md`,
     `m1-test-layout-decision.md` and `m1-solver-distribution-decision.md`
     (keep its GPL distribution paragraph somewhere).
   - Fold `m1-large-prime-decision.md` into `large-prime-fixture.md`, and the
     rationale in `m1-public-api-decision.md` and `baseline-fin.md` into
     `native-support.md` and `test-matrix.md`.
   - Keep, trimmed: `native-support.md`, `m1-completion.md` (trust boundary
     only), `solver-protocol.md`, `test-matrix.md`, `large-prime-fixture.md`,
     `m1-rule-audit.md`, `m1-measurements.md`, `ff-04-reconstruction.md`.
   - Remove machine paths (`/home/agent`, `/workspace`, `/opt/z3-...`) and
     internal names (`agentstack-worker-iog`, "PROJECT gates"). The manifest
     owner `"Riley"` is hard-coded in `solver-manifest.json` and enforced by
     `scripts/finite_fields/check_manifest.py:473`.

4. **Documents contradict each other or the code.**
   - `test-matrix.md` calls the workflow a proposal (line 6), says FF CI is
     pending (98-99), says `ci-linux.yaml` is unchanged (94), and lists
     ordinary cvc5 as 1.4.1 although `ci-linux.yaml` pins 1.3.4.
   - `ffm-10-ticket-report.md` still says the workflow awaits installation.
   - The manifest and `native-support.md:270-272` say x86_64 was never
     qualified; the x86_64 FF CI lane passes.
   - `native-support.md` sets `BLASTER_FF_CVC5`, which only
     `ff-tests/DivisionSource.lean` reads; it has no effect on Blaster.
   - `native-support.md:305` presents `ff-field-polys=false` and `ff-solver=gb`
     as profile settings; they are cvc5 defaults Blaster never sets.
   - `native-support.md:89-97` and `m1-completion.md:28-29` describe
     `PrimeModulus` evidence as always verified. A hypothesis such as
     `(_ : PrimeModulus 9)` is accepted as-is. `Valid` stays sound because the
     goal is then vacuous, but a `Falsified` model under a false hypothesis is
     meaningless. Say so.

5. **`make test-pure` fails on Python 3.9** (macOS `/usr/bin/python3`).
   `run_pure_tests.py:179`, `check_manifest.py`, `benchmark.py` and
   `check_benchmark_results.py` use `str | None` annotations without
   `from __future__ import annotations`. CI uses 3.12 and is unaffected.

6. **Safety checks that never run in CI.** Nothing runs
   `probe_solver.py --negative-fixtures` (34 cases: archive traversal, size
   limits, checksums, malformed responses), `check_manifest.py`,
   `check_benchmark_results.py`, `fixtures/finite-fields/audit/run_corpus.py`
   or `ff-tests/GuideExamples.lean`. The negative fixtures also fail on macOS
   because `safe_path` (`probe_solver.py:52`) rejects any symlinked ancestor
   and `/var` is a symlink; the same rule breaks staging from a symlinked
   checkout path.

## Lower priority

- **Power exponents are not reduced.** `x ^ (2^(2^20))` builds a
  million-bit exponent and about two million nested `let`s
  (`Smt/Translate/FiniteField.lean:121-149`). Reduce a positive exponent `n`
  to `((n - 1) % (p - 1)) + 1`.
- **`Tests/FiniteField/*` is registered through `Tests/FixedIssues.lean`**,
  which every solver lane imports, not through `Tests/Pure.lean`. The modules
  rerun in every lane, and their solver independence is only enforced by the
  FF workflow's PATH check.
- **Live counterexample values are weakly checked.** Exact values are asserted
  only for p = 2, 3 and 7 (`ModelSource.lean`, `IntegrationSource.lean`).
  Large-prime and division cases only assert a value was returned.
- **`ff-tests/OrdinaryCvc5Baseline.lean`**, now a prerequisite of `test-cvc5`
  and `test-all-solvers`, mostly pins the "unsupported `Fin`" error with
  `#guard_msgs` and duplicates `Tests/FiniteField/FinBaseline.lean`. It also
  runs with `BLASTER_TIMEOUT=30` inside `test-all-solvers`, which otherwise
  runs unlimited.
- **`TestsFF` wrappers can replay a stale pass.** They shell out to
  `ff-tests/*Source.lean`, which Lake does not track; only `make test-cvc5-ff`
  clears the outputs first.
- **`make ff-stage` cannot be rerun**; `acquire()` stops on "destination
  already exists" (`probe_solver.py:413`) and there is no clean target.
- **"Offline" covers the Python probe only.** The cvc5 child and Lean
  processes in `test-cvc5-ff` have no network sandbox; the workflow step name
  claims more.
- **`Tests/Smt/CrashLifecycle.lean` `testExitBeforeSubmissionIsHandled`**
  assumes `/bin/sh` exits within a fixed 500 ms sleep and could flake on a
  loaded runner.
- **`associate` calls `constName!`** on a non-variable source head
  (`Smt/Translate/FiniteField.lean:28-29`) and would panic on an unreduced
  head. Unlikely after optimization.
- **Global optimizer change.** `structEq?` (`Optimize/Rewriting/OptimizeEq.lean`)
  now skips proof arguments and rewrites structurally equal constructor
  applications to `True`, for every solver. It looks sound but has no
  dedicated test.
- **The optimizer hot path checks every application** with
  `isOpaqueResidueOperation` (`Optimize/Basic.lean`). Cheap for non-arithmetic
  heads; worth a before/after benchmark on the ordinary suite.
- **Global `.NOTPARALLEL:`** in the Makefile serializes every target, not only
  the FF ones. Low practical impact.

## Fixed during the review

- **Preflight walked shared subterms once per path.** `collectNativeFields`
  ran on every query reaching a solver, for every solver; a 12-level nested
  `Nat` goal took 10 s against 0.88 s on the base branch. It now caches each
  subtree's fields. Regression test in `Tests/FiniteField/Routing.lean`.
- **Admission accepted a theorem's own auxiliary declaration as evidence.**
  Inside `theorem t : PrimeModulus 15 := by ...` the query was emitted with
  `(_ FiniteField 15)`; only cvc5's parse-time primality check stopped it.
  Implementation-detail locals are now skipped. Regression test in
  `Tests/FiniteField/Primality.lean`.
- **`Blaster.lean` imported the experimental `Blaster.FF04` port**, building
  its test corpus and `#print axioms` output into the library and adding an
  `ff04_replay` tactic to every `import Blaster`. The modules moved to
  `Tests/FF04/` (module names `Tests.FF04.*`; namespaces unchanged), and
  tests, benchmarks and fixtures import them from there.
