# FFM-08: Checked finite-field experiment port

## Completed changes

Ported the four checked FF-04 modules from the frozen public source
[`724e32c377b5c6bfdecaf200984203b21c75355b`](https://github.com/input-output-hk/lean-blaster/tree/724e32c377b5c6bfdecaf200984203b21c75355b/Blaster/FF04)
onto the selected Lean 4.24.0 base. The required
[execution](m1-execution-decision.md) and
[toolchain](m1-toolchain-decision.md) parent artifacts are present and were read.
This is a selective source port, not an upstream checkout/build or merge.

- Added `Blaster/FF04/Nominal.lean`, `Polynorm.lean`, `Corpus.lean` and
  `Replay.lean` with no changes to the pinned definitions, proofs, normalization
  algorithm, replay isolation or namespace conventions. The source already
  targets Lean 4.24.0; no compatibility proof repair was needed.
- Added `Tests/FiniteField/Prototype.lean`, `PolynormDecide.lean` and
  `PolynormGrind.lean` from the corresponding pinned `TestsSolver/FiniteField*`
  files. Each adds `import Tests.Pure`; the inherited contents are retained.
- Appended exactly those three individual test imports to
  `Tests/FixedIssues.lean`. Added the corpus and replay imports to `Blaster.lean`
  so the existing library coverage gate reaches all four modules.
- Added the current [architecture/reproduction report](ff-04-reconstruction.md),
  preserving the settled local-port/text-CPC design and distinguishing current
  reproduction from the pinned report's historical solver smoke and benchmarks.

No existing test, expected outcome, script, workflow, toolchain pin, package
configuration, manifest or Makefile was edited. An in-memory byte comparison
against the pre-edit snapshot covered 180 existing files in total: files under
`Tests`, `scripts` and `.github`, plus `lakefile.lean` and `lean-toolchain`.
Every byte was preserved except the exact three-import end append to
`Tests/FixedIssues.lean`.

## Proof-boundary evidence

The nominal `Residue p` wraps `Fin p` and retains ring/characteristic instances
under `NeZero p`, without inversion or division. The package manifest remains
empty; only bundled Lean libraries supply the experiment's algebra.

The fixed CPC fixture proves `x = 2 → x*x = 4` over `Residue 7`. It preserves
declaration-to-original-local matching, assumption discharge against the original
context/negated goal, and a fresh empty local context for each closed step
implication. Only referenced premises are supplied to that step. Every explicit
conclusion, including the solver's trust-labelled identity, is checked by
`grind (ematch := 0)`; labels are not axioms. The executable transitive
`Lean.collectAxioms` allowlist passes and the theorem reports exactly
`[propext, Classical.choice, Quot.sound]`.

The five inherited rejection cases pass: changed assumption, false trust-labelled
identity, wrong modulus, unknown premise reference and unrelated original `False`
leaking into a premise-free step. These are unchanged negative cases, not relaxed
expectations or solver-status checks. No installed solver, proof producer or
external checker is needed for the fixture.

All four reflected identities pass via ordinary `decide` and
`Expr.denote_eq_from_toPolynomial_eq`, each reporting only
`[propext, Quot.sound]`. All four matching grind comparisons pass with
`[propext, Classical.choice, Quot.sound]`. The shared corpus retains and checks
`rejectsFalseCertificate`, `acceptsTrueCertificate`, `zeroProductNotCanonical`
and `zeroProductSemanticallyZero`. No `sorry`, `admit`, new axiom,
`native_decide` or `nativeEqTrue` proof path was introduced; `blasterProven`
is unchanged and is not a dependency of the checked fixture.

## Commands and measured outcomes

Commands ran from the repository root on 2026-10-27. The direct Lean commands
execute the actual replay/normalization path, not merely a cached test import.
Builds and measurements were sequential, within the supplied shared memory
constraint. No default-environment `lake test` was run.

| Exact command | Outcome |
| --- | --- |
| `lake --version && lake env lean --version && lake env lean --githash` | Exit 0: Lake `5.0.0-src+797c613`; Lean `4.24.0`, release `aarch64-unknown-linux-gnu`; compiler commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. |
| `lake build Blaster` | Exit 0; 183 jobs; 90.19 s. All four FF04 modules compile, including the semantic soundness proof and shared corpus. |
| `make test-pure` | Exit 0; 212 jobs; 26.89 s. Existing solver-independent suite passes. This target alone does not discover the new finite-field test files. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Prototype.lean` | Exit 0 on both direct and measured invocations; measured 0.7093 s. Original goal, five negative cases and executable axiom allowlist pass. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/PolynormDecide.lean` | Exit 0 on both invocations; measured 0.5823 s. Four ordinary kernel-evaluated certificates pass. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/PolynormGrind.lean` | Exit 0 on both invocations; measured 0.5981 s. Four matching bounded grind comparisons pass. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Exit 0; clean coverage build completed, 183 jobs, 91.94 s. Selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Final run: exit 0, 196.68 s; pure tier 212 jobs, Z3 tier 668 jobs, including all three new finite-field modules. Selected the same Z3 4.15.2 binary. Two earlier runs exited 2; diagnostics below. |

The direct-file times are single warm whole-process measurements using Python
`time.perf_counter` around each exact command, including imports, elaboration,
kernel checking and axiom printing. No concurrent build/check workload ran.
They are not isolated tactic timings, a scaling study or a claimed speedup.

The pure lifecycle suite emitted model-unavailable, timeout, closed-output and
malformed-response warnings while preserving Falsified verdicts. These did not
fail the suite and were not silenced or used to change expected results.

Source acquisition initially failed through Python HTTPS with a DNS resolution
error; the web reader then retrieved all pinned files successfully. This was an
input-fetch failure, not a Lean or solver check failure. No dependency download,
solver installation or pin change was performed.

### Earlier gate failures and diagnostic runs

The first two exact `make check_tests` invocations exited 2 after 192.22 s and
191.21 s respectively. Both passed the 212-job pure tier and failed on the
unchanged `Tests.Smt.CrashLifecycle` module during the Z3 tier. The first
tool-delivered log elided the specific error; retaining the complete second
run's output captured:

```text
error: Tests/Smt/CrashLifecycle.lean:608:0: malformed response was not classified as protocol failure
```

This is `testProtocolFailureDoesNotBeatHealthySolver`, which races a malformed
fake Z3 response against a fake cvc5 `unsat` delayed by 50 ms and checks that the
Z3 record has stage `check protocol`. The test imports `Blaster.Smt.Env`, whose
implementation was not changed by this port. A scheduling-sensitive failure is
an inference from this fixture and the differing outcomes, not a diagnosed or
fixed root cause.

Diagnostic commands and results:

| Exact command | Outcome |
| --- | --- |
| `env BLASTER_SOLVER=z3 BLASTER_TIMEOUT=30 BLASTER_STRICT_CVC5_RESULTS=0 LEAN_NUM_THREADS=5 lake env lean Tests/Smt/CrashLifecycle.lean` | Exit 0, 10.92 s; direct isolated execution after the first gate failure. |
| `git worktree add --detach .ffm08-baseline HEAD` | Exit 0; detached starting snapshot `d0e3a10` (`base`). The sandbox's worktree-copy helper warned about recursive cloning and fell back to a plain checkout; the baseline root had the original library imports. |
| The exact PATH-selected `make check_tests` command above, with working directory `.ffm08-baseline` | Exit 0, 273.47 s; 200 pure-tier and 647 Z3-tier jobs on the unchanged starting snapshot. This is not evidence of an inherited red baseline. |
| `git worktree remove .ffm08-baseline` | Exit 0; removed the diagnostic worktree and its build outputs. |
| The exact PATH-selected `make check_tests` command above, again from the project root | Exit 0, 196.68 s; 212 pure-tier and 668 Z3-tier jobs on the final port. |

No source, test, expected result, timeout, concurrency setting, check command or
configuration was changed between failed and successful port runs. The final
green gate does not erase the earlier intermittent lifecycle failure; it remains
a reproducibility risk, not a claimed FFM-08 fix. The Z3 suite also emitted an
`Undetermined` warning at `Tests/Smt/SmtNat/SmtNatMod.lean:37` without failing
that module; no expected outcome was weakened.

## Remaining limitations and unrun checks

- This remains a ring experiment, not a production nominal field API or checked
  primality implementation. `NeZero` does not establish primality. No `Inv`,
  `Div`, symbolic-modulus or extension-field support is supplied.
- The normalizer deliberately retains the composite-ring zero-coefficient
  representation limitation. Equality of normal forms is sufficient, not a
  complete decision procedure; the corpus explicitly exposes the limitation.
- The replay is a narrow explicit-conclusion semantic rechecker using grind,
  not a general FF-rule checker, CPC rule-shape auditor or normalizer-first
  dispatcher. No automatic atom reifier, production proof transport through
  optimizations, ProofStep infrastructure, proof acquisition or verified closure
  is implemented. The fixed original-goal fixture does not establish any of
  those production capabilities.
- General CPC syntax, omitted conclusions, scoped subproofs, arbitrary n-ary
  terms, quoted symbols, includes, multiple proof responses, parser hardening,
  resource policy and protocol negotiation remain outside this ticket.
- No new protocol probe, live finite-field proof production, external checker,
  lean-smt/lean-cvc5/Logos package build or Mathlib bridge was run. The pinned
  report's historical measurements and live smoke were read, not rerun.
- The small reflected corpus and single warm timings do not establish realistic
  comparative performance. This is not an optimization, so no before/after
  Blaster performance claim is made.
- cvc5, cvc5 support-floor, all-solvers and native-FF profile lanes are not run
  by this ticket. The mandatory PROJECT gates cover the library and pure/Z3
  tiers, not those additional lanes.
- Remote CI, branch ancestry, publication and maintainer approval are not claimed.
  The supplied checkout is synthetic; the stack/GitHub establish integration
  ancestry and publication. Final review and merging remain with the maintainer.

This file is the ticket report retained for the stack's owner-attributed commit;
local reproduction is not publication or completion signoff.

The optional local command
`git commit -m "Port checked finite-field reconstruction experiment"` exited 128
because the sandbox has no configured Git author identity (`Author identity
unknown`). No identity was invented or configured. The changed sources, tests
and reports are staged for the stack's owner-attributed commit; no local commit
or push is claimed.

## Job summary

All FFM-08 implementation and direct proof-boundary checks are complete. The
exact project build and test gates have passing final runs; the earlier
unchanged-lifecycle failures and all diagnostic commands are recorded above.
No required local check remains unrun. The three new tests are registered only
by end-appended individual imports, with all earlier test content preserved.
The architecture remains the isolated local-port/text-CPC experiment: replay
uses bounded grind and supplies no production proof transport or normalizer-first
dispatcher. The inherited composite-ring limitation, broader production gaps,
unrun additional solver lanes and intermittent lifecycle risk remain explicit.
