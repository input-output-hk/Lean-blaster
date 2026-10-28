# FFM-02: Protected M1 toolchain baseline

## Decision and confirmation status

**Settled baseline:** M1 retains `leanprover/lean4:v4.24.0`, whose Lean
source commit is `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, and a
Mathlib-free Blaster core. The supplied PROJECT requirement to preserve existing
toolchain pins resolves the earlier freeze-confirmation input. This is a
confirmed constraint, not a proposal awaiting a toolchain choice.

The source commit above identifies **Lean**, not a lean-blaster integration tip
or the sandbox's synthetic Git root. The local `lean-toolchain` contains exactly
the selected pin. The installed compiler independently reports the same version
and full source commit; see the validation report below.

This decision authorizes no protected-file edit, dependency upgrade, solver
replacement or toolchain installation. Any change to the Lean pin requires a
**separate authorized scope/policy revision**, including explicit permission for
the affected protected files and a newly validated compatibility baseline. The
[FFM-01 execution contract](m1-execution-decision.md) remains applicable; its
reference to FFM-02 owning a proposed toolchain exception is not such an
exception. FFM-02 selects preservation, not an upgrade.

## Dependency review and core contract

Reviewed local declarations:

- [`lean-toolchain`](../../lean-toolchain): `leanprover/lean4:v4.24.0`.
- [`lakefile.lean`](../../lakefile.lean): imports Lake and declares the Blaster
  package/library, Tests library, `z3check` and `solvercheck` executables. It has
  no external `require` declarations.
- [`lake-manifest.json`](../../lake-manifest.json): manifest format `1.1.0`,
  `packages: []`. There are no locked external Lake packages, including Mathlib.

Lean's bundled libraries are part of the selected toolchain, not an implicit
Mathlib dependency. M1 core algebra, proof infrastructure and core examples must
compile on this baseline without a direct or transitive Mathlib dependency.
Neither the root package declarations nor its manifest are changed by this
record. Empty Lake dependencies do not mean that solver executables are
unnecessary; existing solver/check requirements remain separate and unchanged.

### Optional Mathlib bridge boundary

If later authorized, a Mathlib bridge must be a **separate Lake package** with
its own dependency declarations, lock manifest, compatible toolchain selection,
examples and validation. Dependency direction is bridge to core and Mathlib;
core must never depend on or import the bridge or Mathlib. Core build and test
targets must remain usable without fetching or building either optional package.
Mathlib-specific adapters, instances, theorem wrappers and examples belong on
the bridge side of this boundary, not behind optional imports in the core.

Separate packaging is not cross-version binary interoperability. A bridge that
imports the core must establish a common supported Lean version and compatible
Mathlib revision and rebuild the relevant sources there; Lean 4.32.0 artifacts
cannot be treated as Lean 4.24.0 inputs. No compatible Mathlib revision or bridge
implementation has been selected or validated by this ticket. If the proposed
bridge cannot coexist with the protected baseline, leave it optional and outside
the core rather than silently upgrading the core. Any additional toolchain or
dependency setup requires its own authorization. This record creates no bridge
package and grants no new dependency-download permission.

## Selective-port implications

The pinned public lean-smt reference at
`9b314968f6405395ecbc030c4d3f9b35e4974aa1` declares
[`leanprover/lean4:v4.32.0`](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lean-toolchain).
Its [manifest](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lake-manifest.json)
locks Mathlib input tag `v4.32.0` at
`81a5d257c8e410db227a6665ed08f64fea08e997`, lean-cvc5 at
`4733baf0722c870a5a449f132afa690947e00e2a`, lean-auto and inherited packages.
These files were inspected, not built. They are reference evidence, not
permission to import their dependency graph, copy their build configuration or
replace this project's toolchain.

Later algebra and example work must therefore be selective source ports:

1. Inventory each candidate definition, theorem and example's imports, APIs,
   syntax and proof dependencies before adopting it. A Lean 4.32.0 source example
   is not evidence that it elaborates on Lean 4.24.0.
2. Keep core-facing algebra interfaces and proofs within Lean 4.24.0 and its
   bundled libraries. Rework any needed Mathlib-dependent argument into an
   ordinary source proof on that baseline, or explicitly assign the
   Mathlib-specific result to the separately authorized bridge. Do not pretend a
   required core result is complete merely because it works only in the bridge.
3. Re-elaborate and kernel-check ported source proofs on the protected toolchain;
   exercise examples against the actual core APIs and the applicable solver
   profile. Keep Mathlib-only examples in the separate bridge package. Neither
   reference compilation nor solver success alone establishes core compatibility.
4. If a required port cannot satisfy these constraints, report the concrete
   missing API/proof/prerequisite and seek separately scoped authorization; do
   not change the pin or broaden the trusted base as a compatibility workaround.

This is a compatibility contract, not an implementation of FF-04/FFM-08 algebra
or FFM-12 primality evidence, and not a claim that those ports already work.

## Proof and policy boundary

Ordinary kernel-checked source proofs remain required. This record authorizes
**no substitution of `nativeEqTrue` or compiler trust** for those proofs (including
native-evaluation shortcuts whose justification relies on that trust). A
successful native build or solver answer is not a replacement proof. No `sorry`,
`admit`, new axiom or widening of `blasterProven` is authorized. Any separately
approved, distinct trusted-mode finite-field exception is not permission to use
it on the verified reconstruction path or to bypass this compatibility contract.

The supplied PROJECT is a user-provided policy, not a `project.yaml` assumed to
exist in this checkout. Existing files under `Tests/`, `scripts/` and `.github/`,
and root `lakefile.toml`, `lakefile.lean` and `lean-toolchain` remain protected;
`Tests/FixedIssues.lean` retains only its existing end-append exception. This
decision changes none of those files and makes no amendment to that policy.

## FFM-02 ticket report and job summary

Change: add this decision record only. It fixes the confirmed Lean 4.24.0/source
commit baseline, records the empty core package graph, and defines the selective
port, optional bridge and proof-trust boundaries. No executable source, tests,
protected files, dependency declarations, manifest, solver pins or toolchain
pins are changed. This section serves as both the ticket report and the job
summary retained with the decision artifact for the stack's commit.

### Validation

Commands run from the repository root on 2026-10-23. Both PROJECT checks used
the exact prescribed PATH and selected
`/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting Z3 `4.15.2`.

| Exact command | Observed outcome |
| --- | --- |
| `lake --version && lake env lean --version && lake env lean --githash` | Pass, exit 0. Lake `5.0.0-src+797c613`; Lean `4.24.0`, `aarch64-unknown-linux-gnu`, Release; full source commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; clean build completed successfully, 171 jobs, 86.42 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; pure tier completed 200 jobs, Z3 tier completed 611 jobs, 177.43 seconds total. Lifecycle tests emitted model-response warnings; both tiers completed successfully without changing checks or expected results. |
| `test -s docs/finite-fields/m1-toolchain-decision.md` | Pass, exit 0. |
| `git add --intent-to-add docs/finite-fields/m1-toolchain-decision.md && git diff --check` | Pass, exit 0; includes the new document in the whitespace check. |
| `git diff --check` | Pass, exit 0; also rerun after the validation report update. |

The requested exact-pin search was performed with the repository search tool:
pattern `^leanprover/lean4:v4\.24\.0$`, path `lean-toolchain`. It matched line 1,
`leanprover/lean4:v4.24.0` (the same predicate as the ticket's `rg -n` command).
The toolchain version/hash commands above also exercised the installed baseline.

Before intent-to-add, the supplemental command
`git diff --check && git diff --no-index --check /dev/null docs/finite-fields/m1-toolchain-decision.md`
returned 1 with no whitespace diagnostics. That comparison included a new file
against `/dev/null`; the subsequent ordinary diff check with intent-to-add
returned 0 and is the whitespace gate recorded above.

The local toolchain pin also matches the
[inspected lean-blaster source pin](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/lean-toolchain).
Public reference files were read over HTTPS at the exact revisions linked above;
no reference repository was cloned, built or added as a dependency.

### Remaining work and limitations

- FFM-08 owns the algebra implementation/selective port; FFM-12 owns primality
  evidence. This decision provides their compatibility boundary, not their
  proof artifacts. Production verified reconstruction remains the separately
  scoped post-merge M2 work described in FFM-01.
- No optional bridge or Mathlib compatibility matrix has been built or tested.
  Those need separate scope and dependency approval if pursued.
- PROJECT checks cover the existing core build and pure/Z3 tiers, not reference
  Lean 4.32.0 compatibility, finite-field profile qualification or cvc5,
  support-floor and all-solvers lanes. FFM-03 owns additional FF profiles.
- No default-environment `lake test` is run. No remote CI run, publication,
  integration ancestry or maintainer signoff is claimed; stack/GitHub establish
  branch ancestry and publication, not the synthetic local checkout.
