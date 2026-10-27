# FFM-04: Additive finite-field test and CI layout

## Decision and implementation boundary

Record three separate M1 gates: solver-independent finite-field regressions,
an ordinary-cvc5 baseline, and native live finite-field tests. Implement them in
FFM-10 using new files, append-only test registration, and additive Makefile
rules. This ticket changes only this document; the layout below is an
implementation contract, not a claim that these new gates already exist or pass.

Keep the root Lake package, Lean `4.24.0` pin, existing test content, runners,
workflow files, and Makefile recipe text unchanged. Do not introduce
`LEAN_PROJECT_EXCLUDE_MODULES` or another exclusion mechanism. Reserve
`test-ff-verified` in documentation for M2: M1 must not define an empty target,
skip-success job, or alias that presents solving as verified reconstruction.

## Inspected constraints

The local checkout agrees with the relevant declarations in these public base
references; the observations below come from reading the local files:

- [Root Lake declarations](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/lakefile.lean):
  package `Blaster`, default library `Blaster`, one `@[test_driver]` library
  `Tests`, and executables rooted at `Z3Check` and `SolverCheck`. There is no
  separately declared pure or native-live library in the root package.
- [Coverage runner](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/scripts/check_lean_project_compilation.sh):
  recursively enumerates every `.lean` file in its source-tree argument, builds
  the optional target argument, and requires a `Built <module> (` log entry for
  every source module except executable roots. It has no module-exclusion
  interface. Its evidence depends on clean build output, not cached success.
- [Makefile](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/Makefile):
  `test-all-solvers` clears the root Tests outputs and invokes
  `./scripts/check_lean_project_compilation.sh Tests Tests.AllSolvers`.
  `test-pure` clears those outputs and builds only `Tests.Pure`.
  `check_tests` runs `test-pure` then `test-z3`; it is not an FF-live gate.
- `Tests.Pure` imports nine solver-independent SMT modules, not `FixedIssues`.
  The default route is `Tests -> Tests.Basic -> Tests.Z3 -> Tests.Backend ->
  Tests.FixedIssues`. `Tests.AllSolvers` imports `Tests` and `Tests.Cvc5`;
  `Tests.Cvc5` also imports `Tests.Backend`. Therefore appending pure imports to
  `FixedIssues` makes them reachable in backend/all-solvers builds but does
  **not** make them reachable from `Tests.Pure`.
- The existing Linux workflow separates ordinary cvc5 `1.3.4`, support-floor
  cvc5 `1.2.1`, Z3 `4.15.2`, and all-solvers lanes. Its ordinary cvc5 asset is
  non-GPL. These lanes and their acquisition remain intact.

## Source ownership and registration

| Source or entry point | Ownership and registration | Solver requirement |
| --- | --- | --- |
| `Tests/FiniteField/*.lean` (including future nested modules) | Root `Tests` library; each new module gets its own import line appended at the end of `Tests/FixedIssues.lean` | None |
| `ff-tests/OrdinaryCvc5Baseline.lean` | Standalone source, invoked by its own Make target; outside both the root Tests tree and the native live tree | Ordinary cvc5, not the FF executable |
| `ff-tests/lakefile.lean` | New child Lake package with a local dependency on parent `Blaster` | No solver needed merely to configure the package |
| `ff-tests/TestsFF.lean` and `ff-tests/TestsFF/**/*.lean` | Native live library and its root/import closure, owned by the child package | FFM-03 selected `solve` profile |

Pure modules contain actual deterministic checks of solver-independent
finite-field behavior. They must not invoke an external solver, import live
modules, depend on solver installation or environment selection, or pull in the
backend test suite through `Tests.FixedIssues`. Append direct individual lines
of the form `import Tests.FiniteField.<Module>` to `Tests/FixedIssues.lean`;
do not insert a single mutable umbrella into that protected file instead.
Each future pure module needs a new file and a new final import line, not an
edit to a previous regression or protected aggregator. No content in
`Tests.Pure`, `Tests.Basic`, `Tests.Cvc5`, `Tests.AllSolvers`, or predecessor
tests is rewritten, reordered, or removed.

The standalone ordinary baseline must contain real assertions exercising the
ordinary solver path with native FF mode disabled. It must retain ordinary
result expectations rather than accept an unsupported/unknown result as success.
It is never imported by `FixedIssues`, any pure module, or `TestsFF`. Its location
outside `Tests/` prevents the all-solvers source enumeration from requiring a
live-only standalone module in the protected root import graph.

### Child package and inherited toolchain

FFM-10 creates `ff-tests/lakefile.lean` with the following package shape:

```lean
import Lake
open Lake DSL

package «BlasterFFTests»

require «Blaster» from ".."

@[default_target]
lean_lib TestsFF
```

`ff-tests/TestsFF.lean` imports the native live modules under
`ff-tests/TestsFF/`. Tests import the parent `Blaster` implementation; do not
copy its source or add a Git/registry dependency. Invoke child Lake commands
with `ff-tests` as the working directory. Do not add a child `lean-toolchain`:
elan resolves the existing parent `lean-toolchain`,
`leanprover/lean4:v4.24.0`. The root lakefile and toolchain pin remain untouched.
FFM-10 must check the child command's actual Lean version and local dependency
resolution, not merely assume the proposed package compiles. Child package
build state is separate from the root Tests outputs; any child manifest records
only the local parent dependency, not a new external package.

Run the standalone baseline from the root package environment after building
`Blaster`, using `lake env lean ff-tests/OrdinaryCvc5Baseline.lean`. This compiles
and executes its Lean commands on each invocation without registering another
root library or importing it into `TestsFF`.

## Additive Make gates and coverage contracts

FFM-10 appends new targets and prerequisite-only declarations to the Makefile.
Existing recipe text remains byte-for-byte unchanged. In particular, use
ordinary single-colon prerequisite merging, not a replacement recipe:

```make
.PHONY: test-ff-pure test-cvc5-ordinary-baseline test-cvc5-ff

test-pure: test-ff-pure
test-cvc5: test-cvc5-ordinary-baseline
```

The new target recipes are required implementation, not empty gates. No new
prerequisite is attached to `test-cvc5-floor`. The ordinary lane is extended
through `test-cvc5`; the floor retains its existing version probe and smoke
checks. Native FF execution is never made a prerequisite of `check_tests`,
`test-pure`, `test-z3`, `test-cvc5`, or `test-all-solvers`.

### Pure discovery and coverage

Add `scripts/check_finite_field_pure.sh`, called by `test-ff-pure`. It must:

1. Discover all `.lean` files recursively under `Tests/FiniteField`, deriving
   their module names deterministically. Fail on a missing/empty tree, invalid
   module path, or discovery failure; no silent no-op success.
2. Check a one-to-one match between discovered modules and their individual
   `Tests.FiniteField.*` import lines in `Tests/FixedIssues.lean`. Fail on missing,
   duplicate, or stale registrations. Registration is also needed for the
   existing all-solvers source-coverage gate; standalone builds are not a
   substitute for those imports.
3. Clear the relevant root Tests build outputs before compiling the discovered
   modules, so commands and assertions execute rather than reuse cached tests.
   Build the explicit discovered module targets with solver-selection, timeout,
   and strict-cvc5 environment overrides unset, following the existing pure
   lane's convention. Do not build `Tests.FixedIssues` as a pure entry point.
4. Propagate compiler/assertion failures and account for every discovered module
   in this invocation's build evidence. Verify solver independence in FFM-10
   with neither solver executable available to the pure run; merely unsetting
   `BLASTER_SOLVER` is not proof that tests do not launch a solver.

The appended prerequisite runs before the unchanged `test-pure` recipe. That
recipe may clear the outputs again before building `Tests.Pure`; this does not
undo the prerequisite's executed assertions or coverage result. There is no
need to modify the protected pure aggregator or the old coverage script.

### Ordinary baseline

`test-cvc5-ordinary-baseline` builds the parent library and executes the standalone
baseline with `BLASTER_SOLVER=cvc5`, the ordinary timeout convention, and strict
cvc5 result checking. Native-FF selection must be disabled explicitly according
to the implemented configuration interface. Select ordinary cvc5 through the
ordinary lane's environment; never put the GPL/CoCoA FF profile on its PATH as a
replacement. Fail if the required ordinary solver is missing or an assertion
fails. The existing `test-cvc5` recipe runs after this prerequisite, unchanged.
The target is also independently runnable for diagnosis. It is not the cvc5
`1.2.1` floor test and must not require native FF capability.

### Native live gate and independent coverage

Add `scripts/check_finite_field_live.sh`, called by the real, nonempty
`test-cvc5-ff` target. It must:

1. Validate the FFM-09 manifest and prestaged FFM-03 `solve` profile for the host
   platform, including executable/archive identities and capability evidence.
   Use its explicit executable path; never discover the FF solver through PATH
   or fall back to the default worker cvc5. Missing inputs are failures, not
   successful skips. M1 requires no proof-production profile.
2. Discover `ff-tests/TestsFF.lean` and every `.lean` file recursively under
   `ff-tests/TestsFF/`. Require the root and at least one substantive live test
   module; an empty library or imports-only suite is not an acceptance gate.
3. Clean the child live-test outputs and build `TestsFF` from the child package
   with the selected FF profile. Compare the complete discovered source set
   against actual fresh compilation evidence for the root's import closure.
   Fail for an unimported live source, missing build evidence, solver failure,
   or failed expected result. Do not independently build orphan modules to mask
   incomplete root registration. Do not count the ordinary baseline as live
   coverage or include the child lakefile as a test module.
4. Exercise real FF SAT/model and UNSAT assertions with independently known
   answers. Validate model semantics, not one incidental model spelling or
   choice. Native solve success is not evidence of Lean proof reconstruction.

This runner has its own live-tree coverage; the old root runner continues to
cover all of `Tests/` without exclusions. New pure/live modules are discovered
without editing a runner. Native additions may extend the unprotected child
`TestsFF.lean` import root; pure additions use append-only `FixedIssues` imports.
A runner created under `scripts/` becomes protected in subsequent jobs, so its
initial implementation must discover future modules rather than hard-code a
list requiring later edits.

Clean-output gates sharing a build tree must run serially. FFM-10 must serialize
such targets or use isolated workspaces, including validation under parallel
Make invocation; root pure/Z3/cvc5/all-solvers clean recipes must not race each
other. Keep pure, ordinary and native evidence distinct even when one CI job
runs more than one gate.

## CI ownership and solver separation

FFM-10 supplies only the new `.github/workflows/finite-fields.yaml`, within its
owner-approved filename scope. Existing `.github/` files and scripts are not
edited. The named path is the proposal for that ticket, not a grant to edit CI
in this decision job or add other workflow paths without an amendment.

The new workflow must run on aggregate pull requests and pushes to
`agent/feat-cvc5-ff`, so serial integration does not rely on the existing
workflow's `main`/`staging` push filters. Use a workflow-specific concurrency
group so it cannot cancel the existing workflow's jobs. Its gate contract is:

- A solver-independent job runs `make test-pure`, including the new discovery
  prerequisite, without external solvers. This supplements, not replaces,
  PROJECT's existing pure/Z3 checks.
- A dedicated native-live job runs `make test-cvc5-ff` in the approved immutable
  iog image with the FFM-03 tree and FFM-09 manifest startup handoff. Verify
  inputs offline. Do not fetch an alternate solver or build missing native
  dependencies in the consumer job. Exercise each approved Linux platform with
  a matching execution environment; do not label cross-architecture inspection
  as execution.
- The existing ordinary cvc5 job still invokes `make ... test-cvc5`, now reaching
  the standalone ordinary baseline through the appended prerequisite. Its
  non-GPL cvc5 `1.3.4` identity and acquisition remain unchanged. The new workflow
  does not stand in for that job or the existing all-solvers job.
- The existing `test-cvc5-floor` lane remains separate at `1.2.1`. Neither the
  baseline nor native-live target is attached to it. The FF profile's GPL cvc5
  `1.3.4` identity is separate even though its version matches ordinary cvc5.

Provisioning follows [FFM-03](m1-solver-distribution-decision.md): one approved
M1 solving profile, Linux arm64 and x86_64 artifacts, image-build acquisition,
manifest-relative paths, and no M1 proof-profile requirement. The future
immutable image digest and reviewed manifests are prerequisites for consuming
jobs, not supplied by this layout decision. Preserve all existing CI coverage;
no gate may convert unavailable inputs or unsupported results into success.

## FFM-10 acceptance evidence required

Before claiming the implementation complete, record exact commands and outcomes
for the pure, ordinary, native, floor and all-solvers lanes in their required
solver environments, plus the mandatory PROJECT checks. Include evidence that:

- A new pure module is discovered and executed with no solver installed; omission
  of its final `FixedIssues` import is rejected by coverage.
- An orphan live module, empty live tree, missing profile, and failing live
  assertion fail the native gate rather than silently pass. Use temporary
  negative fixtures and restore them; never weaken a permanent expected result.
- The ordinary standalone baseline runs with ordinary cvc5 and native FF mode
  disabled, while native tests execute the manifest-selected FF binary.
- Child Lean is `4.24.0`, the parent dependency resolves locally, and clean and
  repeated invocations do not hide test execution behind cached outputs.
- Later additive tests require no edit to an existing protected runner or
  workflow; existing test content, recipes, pins, and coverage remain intact.

These are future implementation checks. None is reported as passed by this
documentation-only job. Verified proof reconstruction and the reserved
`test-ff-verified` gate remain M2 work.

## FFM-04 ticket report and job summary

Change: add this decision record only. It fixes test ownership, append-only
registration, the local child package, the three real gate contracts, separate
coverage, and additive CI/Makefile ownership for FFM-10. No executable source,
test, script, Makefile, workflow, expected outcome, dependency declaration or
toolchain pin is changed. This section retains the ticket report and job summary
with the decision artifact; publication and maintainer signoff are not claimed.

### Validation performed

Repository inspection used the read/search tools. The ticket's searches were
performed with the same patterns and paths rather than shell `rg`:

| Requested command / equivalent inspection | Observed outcome |
| --- | --- |
| `rg -n 'lean_lib\|test_driver' lakefile.lean` | Search matched `lean_lib` declarations at lines 9 and 14 and `@[test_driver]` at line 13; inspected without editing. |
| `rg -n 'Tests\.AllSolvers\|check_lean_project_compilation' Makefile` | Search/read confirmed core coverage at line 32 and `Tests Tests.AllSolvers` coverage at line 60, with output cleaning at lines 58–59. |

Commands run from the repository root on 2026-10-27:

| Exact command | Observed outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 `4.15.2`; clean build and source coverage completed successfully, 171 jobs, 92.93 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; same Z3 `4.15.2`; pure tier completed 200 jobs and Z3 tier completed 611 jobs, 173.68 seconds total. Lifecycle tests emitted model-response warnings; `Tests/Smt/SmtNat/SmtNatMod.lean:37` emitted an Undetermined warning. Both tiers completed successfully without changing tests or expected results. |
| `git add --intent-to-add docs/finite-fields/m1-test-layout-decision.md && git diff --check && test -s docs/finite-fields/m1-test-layout-decision.md` | Pass, exit 0, no diagnostics; intent-to-add includes this new document in the whitespace check. |
| `git diff --check && test -s docs/finite-fields/m1-test-layout-decision.md` | Pass, exit 0, no diagnostics after the final validation-report update. |

### Remaining work and limitations

- FFM-10 implements and exercises the new package, tests, runners, targets and
  workflow. This record does not install those components or prove their runtime
  behavior. Its example Lake/Make declarations are design, not compiled code.
- Consuming native jobs require the approved image digest, staged artifacts and
  reviewed FFM-09 manifests; this job neither stages nor qualifies them. The
  default worker cvc5 `1.4.1` is not a substitute for ordinary or FF lane pins.
- Existing PROJECT gates cover the core and existing pure/Z3 tests only, not
  ordinary cvc5, the floor, all-solvers, native FF, or M2 reconstruction.
- No default-environment `lake test`, remote CI run, branch ancestry verification,
  push, or maintainer signoff is claimed. Stack/GitHub establish integration
  ancestry and publication; final review and merging remain with the maintainer.
