# FFM-07: Ticket report and job summary

## Current scope and retained implementation

The supplied snapshot already implements the current-base modulus interface,
successful-result cache, full applied-type opaque dispatch, and selective
Fin/interface regressions. This job preserves those executable files and updates
the baseline evidence and ticket report. The fresh validation record below is
separate from the inherited implementation history.

The owner's 2026-10-27 clarification accepts the worker's **cvc5 1.4.1
GPL/CoCoA** binary for FFM-07. Non-CoCoA execution is owned by the ci-linux
cvc5 lane through FFM-10; it is neither a prerequisite nor an acquisition task
for this job. Earlier statements below calling it an FFM-07 blocker describe
the superseded scope, not the current acceptance status.

## Inherited implementation and validation history

Everything in this history, through “Retained-implementation verification,”
was present in the supplied snapshot. Failures, fixes, timings, source/base
identities and solver runs in those sections are imported evidence, not fresh
work or executions in this job. The historical constructor-equality correction
preserved the original Valid/Falsified expectations.

Parent inputs consumed:
[m1-execution-decision.md](m1-execution-decision.md) and
[m1-toolchain-decision.md](m1-toolchain-decision.md). The exact supplied root,
public integration tip, matching input trees, historical source links and solver
identities are recorded in [baseline-fin.md](baseline-fin.md). Historical
sources were read only; no historical branch was merged, built or rerun.

## Changes

- `Blaster/Optimize/Basic.lean`: `getNatModulus?` rejects open syntax before
  lookup/normalization, recognizes raw Nat literals without insertion, checks
  Nat type, uses `optimizeExpr` in an already initialized environment, recognizes
  the supported residual `OfNat` projection, and caches only successful
  nonliteral results. Errors propagate; numeric results are not proof evidence.
- `Blaster/Optimize/Env.lean`: `optEnv.modulusCache : Std.HashMap Lean.Expr Nat`
  uses the original structural input as key and existing default initialization.
  Updated the affected positional environment pattern. The recursive-cache
  pattern's existing trailing wildcards already cover the extended structure.
  No split environment, PtrExpr or hashcons infrastructure was imported.
- `Blaster/Optimize/OptimizeStack.lean`: updated both positional patterns for
  hypothesis/match stack context handling. Record updates preserve the cache.
- `Blaster/Smt/Translate/Quantifier.lean`: `translateTypeAux` passes the full
  applied type; `translateOpaqueType` derives the bare head internally for the
  six existing non-indexed sort implementations and their existing cache keys.
- `Blaster/Optimize/Rewriting/OptimizeEq.lean`: constructor comparison respects
  proof irrelevance using existing parameter metadata; `optimizeEq` consumes
  both `some true` and `some false`. This is the narrow compatibility fix
  required by the failing closed Fin examples, not a historical optimizer port.
  All non-proof fields still contribute to the existing comparison lattice.
- New `Tests/FiniteField/Interfaces.lean`: raw/elaborated numerals, aliases,
  projections, large values, successful-only caching, distinct/repeated keys,
  rejected types/open expressions, explicitly instantiated assignments,
  environment updates, optimizer-error propagation and opaque sort behavior.
  Uncomputable closed Nat coverage uses a defined `opaque`, not a new axiom.
- New `Tests/FiniteField/FinBaseline.lean`: three pure translation rejections,
  quantified optimizer-only Undetermined, four closed Valid cases and the false
  field-division interpretation. Original Fin goals and outcomes are retained.
- `Tests/FixedIssues.lean`: only two end-appended individual imports for those
  new modules. Both new modules import `Tests.Pure`; no existing import changed.
- New `ff-tests/OrdinaryCvc5Baseline.lean`: imports only `Blaster`; two Fin
  rejections, closed division, and bounded-Nat distributivity modulo 7. It is
  not registered in the ordinary Tests tree and has no child-package dependency.
- New `baseline-fin.md`: current observations, exact revisions, historical/new
  evidence separation, test ownership, semantics and reproduction commands.

No existing protected test, script, workflow, Lake declaration or toolchain was
rewritten. No expected result was weakened, and no new axiom, admission, solver
fallback or change to `blasterProven` was introduced.

## Direct validation and initial failures

Commands ran from the repository root on 2026-10-27.

```sh
lake --version && lake env lean --version && z3 --version && cvc5 --version
command -v cvc5 && readlink -f /usr/local/bin/cvc5 && cvc5 --show-config
lake build Blaster
make test-pure
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean
BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean
```

- Version/configuration commands exited 0. cvc5 resolves to the installed GPL
  static binary and explicitly reports `cocoa: yes`.
- Initial `lake build Blaster` passed, 171 jobs, 89.25 seconds.
- `make test-pure` passed, 200 jobs, with existing lifecycle diagnostic warnings.
- The initial interface run failed its raw-literal cache expectation. Inspection
  demonstrated that Lean's `mkNatLit 0` is an `OfNat.ofNat` application, whereas
  `mkRawNatLit 0` is `Expr.lit`. Corrected the new test's literal construction;
  retained a separate elaborated-numeral caching assertion. The helper's cache
  policy did not change to accommodate the test.
- The first direct Fin baseline run failed four positive guards: arithmetic
  reduced, but distinct constructor proof terms left the equalities
  Undetermined. The run exited 1 in 1.41 seconds. The existing comparator neither
  skipped proof parameters nor consumed `some true` in `optimizeEq`. Skipping
  proof parameters alone still failed; the completed correction addresses both.
  The false `1 / 2 = 4` guard and quantified rejections already passed.
- After the correction, `lake build Tests.Pure` followed by the three direct
  commands above passed as one `&&` chain, exit 0, 51.78 seconds total including
  rebuilding affected modules and lifecycle tests. The direct guarded files
  emitted no unexpected messages. Every numeric/cache/open-input guard, every
  pure Fin guard and every standalone cvc5 guard passed.

### Live smoke scenarios

Ran `lake env lean --stdin` with an input importing only `Blaster`. A private
`modulus : Nat := 7 * 11` was looked up twice after one `Optimize.main`
initialization; opaque dispatch was called on the applied `Fin 77`; the original
closed `(1 : Fin 7) / 2 = 0` was executed with `only-optimize`. Final output:

```text
modulus=some (77); repeat=some (77); cached=1; Fin dispatch=true
Valid
```

Exit 0. The Boolean `Fin dispatch=true` means the opaque recognizer returned
`none`, not that Fin is supported. Before the constructor correction, the same
closed goal printed Undetermined; afterward it printed Valid.

A second `lake env lean --stdin`, with
`BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1`, ran:

```lean
import Blaster
#blaster (solver: cvc5) (dump-smt-lib: 1)
  [∀ (a b c : Nat), a < 7 → b < 7 → c < 7 →
     (a * ((b + c) % 7)) % 7 = ((a * b) % 7 + (a * c) % 7) % 7]
```

Exit 0, Valid. The emitted query defined `Nat` as `Int`, used integer arithmetic
and `mod`, and issued `check-sat`; it contained neither `FiniteField` nor field
literals. This verifies ordinary arithmetic execution on the available binary,
not execution on a binary built without CoCoA. Stdin smoke inputs left no
throwaway source files in the repository.

### Protected content verification

An inline Python check read `git archive HEAD Tests scripts .github lakefile.lean
lean-toolchain`, compared each archived file's bytes with the working file, and
required the aggregate's bytes to equal the original plus exactly:

```lean
import Tests.FiniteField.Interfaces
import Tests.FiniteField.FinBaseline
```

Passed: 178 protected baseline files; only those two appended imports differ.
New test files are additions, not modifications of prior test content.

## Required PROJECT checks

Both exact commands passed with Z3 4.15.2 alone on the prescribed PATH:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

| Check | Outcome |
| --- | --- |
| `make check_blaster` | Exit 0; clean build, 171 jobs; 88.55 seconds. |
| `make check_tests` | Exit 0; pure tier 200 jobs and Z3 tier 647 jobs; 192.69 seconds total. |
| `make test-pure` / `make test-z3` | Both executed and passed as the exact subcommands of `make check_tests`. |

The Z3 tier built both new finite-field test modules through the appended
imports. Existing lifecycle tests emitted their model-response diagnostics.
`Tests/Smt/SmtNat/SmtNatMod.lean:37:27` emitted an Undetermined warning;
line 41:56 reported Valid. No warning, test or expected result was suppressed.

An additional stdin smoke defined a structure with a `True` proof field
**before** its Nat data field and two distinct theorem proofs. Equal data
reported Valid, unequal data Expected Falsified, and independently quantified
data Expected Undetermined, all in optimizer-only mode. All three guards
passed, exit 0. This checks that skipping a proof does not skip subsequent
data or collapse unknown data comparisons.

Direct Fin-file wall time was 1.41 seconds before the fix (four failed positive
guards) and 1.33 seconds after it (all guards pass), including Lean startup.
These single runs are correctness observations, not a performance benchmark.
The final timing used Python `time.monotonic` around the exact direct
`env -u ... lake env lean Tests/FiniteField/FinBaseline.lean` command.
An attempted `/usr/bin/time -f 'FinBaseline elapsed: %e s'` wrapper exited 127
because `/usr/bin/time` is absent; it did not execute Lean.

## Outstanding checks and scope limits

- **Required non-CoCoA baseline:** not run. Directory inspection and
  hidden/ignored-inclusive executable searches under `/opt`, `/usr/local/bin`,
  `/usr/bin`, `/workspace`, `/cache`, `/home/agent`, `/tmp` and `.artifacts` found
  only the installed GPL/CoCoA executable (no staged `.artifacts` tree).
  Required prerequisite: provision a non-CoCoA ordinary cvc5 executable, or
  grant scoped acquisition approval for the base ordinary cvc5 version/platform.
  Then put that binary first on PATH, record `--version` and `--show-config`
  with `cocoa: no`, and rerun the standalone command above. The protected CI
  ordinary pin remains 1.3.4; this job does not silently substitute a new pin.
- No cvc5 support-floor, full cvc5/all-solvers lane or remote CI run is claimed.
  No default-environment `lake test` was run.
- No native FF sort/operation translation, prime checking, field admission,
  nominal Residue API, FF proof reconstruction, child Lake package, dedicated
  target or new workflow is implemented; those remain their named later tickets.
- Normalization is an interface result, not a kernel proof or primality witness.
  The constructor fix relies on Lean proof irrelevance within the existing
  optimizer; it does not introduce a new trust mode or broaden `blasterProven`.
- This report and code are repository deliverables for the stack's
  owner-attributed commit. No push, aggregate PR change or maintainer signoff is
  claimed. Acceptance remains incomplete until the non-CoCoA run is supplied.

## Job summary

Delivered the selective helper/cache/dispatch adaptation, preserved Fin baseline
outcomes with the necessary proof-irrelevant constructor comparison correction,
added the three requested regression files, and retained all existing protected
content except the two permitted end-appended imports. Both exact PROJECT checks,
the two direct pure files, live smoke scenarios and the standalone baseline on
the installed cvc5 passed. Documentation local links, fenced-block pairing and
trailing-whitespace validation also passed.

One acceptance prerequisite remains: execution of the standalone file with an
ordinary non-CoCoA binary. The available binary reports CoCoA enabled. Provision
that executable or approve its scoped acquisition before claiming full FFM-07
completion; the available-binary result is supplementary evidence only.

## Final validation refresh

The implementation and regression files were already present in the working
tree when this validation refresh began. They were preserved, not replaced.
The pinned historical helper and test cases were compared with the adaptation;
no additional executable change was needed. Earlier failure observations and
timings above belong to the initial implementation run, not this refresh.

Fresh executions on the same supplied root:

| Exact command | Outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; Z3 4.15.2, 171 jobs, 95.65 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; `make test-pure` (200 jobs) and `make test-z3` (647 jobs), 177.46 seconds total. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean` | Pass, no unexpected messages. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean` | Pass, no unexpected messages; the two direct pure commands took 2.82 seconds together. |
| `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean` | Pass on installed GPL/CoCoA cvc5 only, 1.67 seconds. |
| `cvc5 --version && cvc5 --show-config` | Exit 0; 1.4.1, revision `2b2e844`, `cocoa: yes`. |

The lifecycle diagnostic warnings remained visible. In this refresh,
`Tests/Smt/SmtNat/SmtNatMod.lean:37:27` reported Valid rather than the earlier
Undetermined warning; no source or expectation was changed between these runs.

Fresh `lake env lean --stdin` smoke execution returned `some (77)` twice with
one cache entry and rejected applied `Fin 77` at opaque dispatch. Optimizer-only
`1 / 2 = 0` and `3 / 0 = 0` over `Fin 7` reported Valid; `1 / 2 = 4` reported
Expected Falsified. A second stdin execution, under the standalone command's
cvc5 environment, returned Valid for bounded-Nat distributivity and emitted an
integer/modulo query with `check-sat` and no finite-field sort. Both exited 0.

The byte comparison against `git archive HEAD Tests scripts .github
lakefile.lean lean-toolchain` again passed for all 178 protected base files,
allowing exactly the two end-appended imports. No smoke files were created.
Installation/staging searches again found no non-CoCoA executable. The sole
remaining acceptance prerequisite is unchanged: provision ordinary non-CoCoA
cvc5, or approve its scoped acquisition, then run the standalone baseline.
These successful checks do not close that prerequisite or claim full acceptance.

## Validation of supplied snapshot efe012c6

This job received synthetic root
`efe012c60a7b628b3e94a7d5620634d2794e5aca`, tree
`3c821aff3798d4d2303da1a57d4b45e9a80c7206`, as reported by
`git rev-parse HEAD HEAD^{tree}`. All executable FFM-07 changes and regression
registrations described above were already present. This job changes only this
report and `baseline-fin.md`; no Lean source, existing test, script, workflow,
solver manifest or toolchain pin is changed.

The parent decisions remain present. Inspection confirmed the structural
`Expr` success cache, pre-normalization open-input rejection, one-time optimizer
initialization in the interface tests, and full applied-type opaque dispatch.
The three historical regression sources at `724e32c3` were read, not executed.
The initial failures and before/after measurements above are inherited records,
not failures reproduced or fixes introduced in this job.

### Fresh commands and outcomes

| Exact command | Outcome |
| --- | --- |
| `lake --version && lean --version && cvc5 --version && cvc5 --show-config` | Exit 0; Lake `5.0.0-src+797c613`, Lean 4.24.0 / `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, cvc5 1.4.1 / `2b2e844`, `cocoa: yes`. |
| `readlink -f /usr/local/bin/cvc5` | Exit 0; `/opt/cvc5-Linux-arm64-static-gpl/bin/cvc5`. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; Z3 4.15.2, 171 jobs, 93.03 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; 191.64 seconds. Its exact `make test-pure` and `make test-z3` subcommands passed, 200 and 647 jobs respectively. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean` | Pass; no unexpected messages. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean` | Pass; no unexpected messages. The two direct pure commands ran in an `&&` chain, 2.65 seconds total. |
| `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean` | Pass; 1.66 seconds, on the installed GPL/CoCoA binary only. |

The test gate retained the lifecycle model-response warnings. In this run,
`Tests/Smt/SmtNat/SmtNatMod.lean:37:27` reported Valid. Both finite-field
regression modules were built by the Z3 aggregate. No default-environment
`lake test` was run.

Two fresh `lake env lean --stdin` smoke executions also exited 0:

- With the three `BLASTER_*` variables unset, a private `Nat := 7 * 11`
  definition was looked up twice after one `Optimize.main` initialization.
  Output was `modulus=some (77); repeat=some (77); cached=1; Fin rejected=true`.
  Applied `Fin 77` returned `none` from opaque dispatch. The optimizer-only
  goals `(1 : Fin 7) / 2 = 0` and `(3 : Fin 7) / 0 = 0` reported Valid;
  `(1 : Fin 7) / 2 = 4` reported Expected Falsified.
- With `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1`,
  the bounded-Nat distributivity goal from the standalone file ran with
  `(dump-smt-lib: 1)` and reported Valid. Its emitted query defined Nat as Int,
  used integer multiplication and `mod`, and issued `check-sat`; no native
  finite-field sort appeared.

Both smoke inputs were passed through stdin; no throwaway source files remain.

### Remaining prerequisite and job summary

**FFM-07 acceptance remains incomplete solely on the required non-CoCoA
execution.** Hidden/ignored-inclusive artifact searches under `/opt`,
`/usr/local`, `/usr/bin`, `/workspace`, `/cache`, `/home/agent` and `/tmp`
found only the installed GPL distribution and its launcher. Inspection of the
FFM-03 distribution decision and FFM-09 manifest found GPL/CoCoA profiles, not
an ordinary non-CoCoA executable or a scoped approval to acquire one here.

Required owner action: provision ordinary non-CoCoA cvc5 for Linux arm64
(preserving the ordinary 1.3.4 pin), or approve its scoped acquisition.
Then verify `--version` and `--show-config` (`cocoa: no`) and run the exact
standalone baseline command with that binary's directory first on PATH.
The available CoCoA result cannot substitute for this check.

This job preserved the supplied implementation and protected test content,
refreshed actual snapshot identity and validation evidence, and passed every
locally runnable requested command. It adds no native-field support and claims
no cvc5 support-floor/all-solvers lane, remote CI, publication or maintainer
signoff. The remaining prerequisite is not waived by the successful PROJECT
checks.

## Retained-implementation verification

The supplied `efe012c6` checkout already contained the executable adaptation and
all three regression files, plus working-tree edits to this report and
`baseline-fin.md`. This verification preserves that work. No executable or
protected file was edited; the only additions are these documentation notes.
The historical helper and three regression sources at `724e32c3`, and both
pinned historical baseline documents, were read rather than executed.

Fresh executions from the repository root:

| Exact command | Outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; Z3 4.15.2, 171 jobs, 91.18 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; 195.74 seconds; its `make test-pure` and `make test-z3` subcommands passed, 200 and 647 jobs respectively. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean` | Pass; no unexpected messages. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean` | Pass; no unexpected messages. The two direct pure commands took 3.06 seconds in an `&&` chain. |
| `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean` | Pass on GPL/CoCoA cvc5 only; 1.69 seconds. |
| `lake --version && lean --version && command -v cvc5 && readlink -f /usr/local/bin/cvc5 && cvc5 --version && cvc5 --show-config` | Pass; Lean 4.24.0, Lake `5.0.0-src+797c613`, cvc5 1.4.1 / `2b2e844`, installed GPL path, `cocoa: yes`. |

The project tests retained the lifecycle model-response warnings;
`SmtNatMod.lean:37:27` reported Valid. Two `lake env lean --stdin` smoke runs
also passed: the first returned modulus 77 twice with one cache entry, rejected
applied `Fin 77` in opaque dispatch, and reported Valid/Valid/Expected Falsified
for the three division cases described above. The second, using the standalone
cvc5 environment, reported Valid and emitted integer/modulo SMT with `check-sat`
for bounded-Nat distributivity. No smoke source files were created.

**Job summary:** the retained implementation passes every locally available
requested check. Non-CoCoA execution remains blocked: renewed hidden/ignored-
inclusive searches in the locations listed above found only the installed GPL
distribution and launcher. No acquisition permission was found in the consumed
decisions or solver distribution artifacts. Provision ordinary non-CoCoA cvc5
1.3.4 for Linux arm64, or approve scoped acquisition, before claiming full
acceptance. No native-field support, remote CI run or publication is claimed.

## Current validation: cbce4b6c

### Completed changes and input identity

This job received synthetic root
`cbce4b6cd82c648ec3419a8e05070bcdb307b082`, tree
`dc1304fc2c935ded7b7c3913cc0167af2065a832`, as observed with
`git rev-parse HEAD HEAD^{tree}`. Stack/GitHub establish branch ancestry; this
record does not infer a new remote integration revision from the local root.
The reviewed concurrency base and pinned historical source revisions remain
listed in [baseline-fin.md](baseline-fin.md#scope-and-revisions).

Both required parent decisions were present and read. The pinned historical
helper at `724e32c3`, cache at `075fc923`, three historical regression files at
`724e32c3`, and baseline documents at `d95b6bd0` and `724e32c3` were read only.
The two historical baseline documents agree on behavior and differ in test
ownership/layout. None was executed or merged.

The implementation was already complete in this supplied snapshot:

- `getNatModulus?` rejects open syntax before normalization/cache access,
  recognizes literals, reducible aliases and the supported OfNat projection,
  and caches only successful nonliteral results. It calls `optimizeExpr` in
  the initialized environment and propagates optimizer errors.
- `OptimizeEnv.modulusCache` uses `Std.HashMap Lean.Expr Nat`; defaults and
  positional patterns in `Env.lean` and `OptimizeStack.lean` account for it.
  No PtrExpr/hashcons infrastructure is imported or `mkExpr` misused.
- Full applied types reach `translateOpaqueType`; the six existing sorts
  still use bare-head keys internally.
- The two pure regression files and standalone cvc5 file retain all their
  guards, imports and registration boundaries. The supplied constructor-proof
  comparison correction is retained, not introduced or broadened here.

**This job changes only the baseline document and this ticket report.** It
records the current source identity, actual solver configuration, the complete
solver-reaching SMT dump, fresh check results and the corrected CoCoA scope.
No executable source, existing protected test, script, workflow, toolchain,
solver pin or expected outcome changes.

### Exact validation commands and outcomes

All commands ran from the repository root on 2026-10-27.

| Exact command | Outcome |
| --- | --- |
| `lake --version && lake env lean --version && lake env lean --githash && command -v cvc5 && readlink -f /usr/local/bin/cvc5 && cvc5 --version && cvc5 --show-config && git rev-parse HEAD HEAD^{tree}` | Exit 0. Lean 4.24.0 / `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake `5.0.0-src+797c613`, cvc5 1.4.1 / `2b2e844`, GPL static path, `cocoa: yes`; root/tree as above. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Exit 0; Z3 4.15.2; clean build, 171 jobs, 85.72 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Exit 0; Z3 4.15.2; 194.58 seconds. Its exact `make test-pure` and `make test-z3` subcommands both passed, 200 and 647 jobs respectively. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean` | Exit 0; all numeric/cache/open-input, error-propagation and sort guards pass; no unexpected messages. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean` | Exit 0; all Fin guards pass; no unexpected messages. Both direct pure commands ran in an `&&` chain, 2.57 seconds total. |
| `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean` | Exit 0; all standalone guards pass on installed cvc5 1.4.1, 5.46 seconds. |
| `BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean --stdin` | Exit 0, 1.52 seconds; ran all four standalone cases with `dump-smt-lib`. Input and complete query are in the baseline document. Exactly one `check-sat`; no `FiniteField` sort or `#f` field literal. |

The project tests retained lifecycle model-response warnings, including the
deliberate model-error/timeout/framing diagnostics. The unchanged
`Tests/Smt/SmtNat/SmtNatMod.lean:37:27` reported Undetermined in this execution;
line 41:56 reported Valid. The project gate passed; no warning was suppressed,
test weakened or result changed. Both finite-field modules were built by the
Z3 aggregate.

A second `lake env lean --stdin` smoke, with `BLASTER_SOLVER`,
`BLASTER_TIMEOUT` and `BLASTER_STRICT_CVC5_RESULTS` unset, imported only
`Blaster`. After one `Optimize.main` initialization it looked up a private
`Nat := 7 * 11` twice and called opaque dispatch on applied `Fin 77`. It
asserted both results were 77, the cache size was one, and dispatch returned
none. Output:

```text
modulus=some (77); repeat=some (77); cached=1; Fin rejected=true
```

The same smoke executed optimizer-only `1 / 2 = 0`, `3 / 0 = 0`, and
`1 / 2 = 4` over `Fin 7`: Valid, Valid, Expected Falsified. Exit 0.
All smoke inputs were passed through stdin; no throwaway source files remain.

A Python byte comparison read
`git archive HEAD Tests scripts .github lakefile.lean lean-toolchain` and
compared every archived file with its working-tree bytes. **All 180 protected
files were unchanged**, including both existing FiniteField modules and
`Tests/FixedIssues.lean`. Its two final individual imports were already present;
this job did not append duplicates or alter any earlier import.

### Remaining limitations and current job summary

**FFM-07's revised worker acceptance is satisfied.** The supplied implementation
passes both prescribed PROJECT checks, both direct pure files, the standalone
cvc5 baseline and live interface/dump smoke scenarios. The baseline records
the actual binary's version/configuration and the complete query for its only
solver-reaching case. Historical and fresh results are explicitly separated.

- The worker run uses cvc5 1.4.1 with CoCoA enabled. Non-CoCoA execution was
  not performed or provisioned; it belongs to ci-linux through FFM-10 under
  the owner's clarified scope, not an outstanding FFM-07 prerequisite.
- The full cvc5, 1.2.1 support-floor and all-solvers lanes, remote CI and
  maintainer signoff were not executed here. No default-environment `lake test`
  was run and no publication or aggregate PR change is claimed.
- No native finite-field support, Residue API, primality/admission check,
  reconstruction, child package, dedicated target or workflow is added.
  Normalization remains numeric recognition, not proof or primality evidence.
- There is no new optimization in this job; the old before/after observations
  above are inherited correctness timings, not a fresh performance claim.

Final review, aggregate publication and completion signoff remain with Riley.
