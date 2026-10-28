# FFM-09: Pinned finite-field solving protocol

## Authority and scope

Riley's **2026-10-27 solving-profile amendment** selects upstream cvc5 **1.4.1
static GPL/CoCoA**, source `2b2e84419f70817ec919a784a48806e79f677240`, for
Linux arm64 and Linux x86_64. The machine-readable inventory is
[solver-manifest.json](solver-manifest.json). The public interface calls this
profile `solving` (not the earlier `solve` bootstrap layout).

This amendment supersedes the 1.3.4 selection and `/opt/finite-fields` image
handoff in [FFM-03](m1-solver-distribution-decision.md), and resolves the previous
FFM-09 report's provisioning blocker. Those rows and observations remain
**historical evidence**, not current identities or instructions. This job may
acquire both approved archives through its new `--fetch-only` interface in the
network-enabled worker. No image change or image digest is required. PROJECT
setup remains `lake --version`; it does not provision these archives. Ordinary
and FF cvc5 lanes now expect 1.4.1 under the amendment; the maintainer's later
`ci-linux.yaml` update is outside this job. No workflow is modified here.

FFM-03's GPL policy, platform scope and ownership remain unchanged: Riley owns
the distribution inventory and qualification. Separate-process GPL execution is
approved; linking into Blaster is not. Public hosting/image redistribution still
requires license and corresponding-source review. Retaining upstream archives
and their license payloads is not a claim that this review has occurred.

**Proof production is deferred to M2.** The clean-wip executable in FFM-03 is
only a bookmark: no proof artifact is acquired, staged or executed. M1 has only
the `solving` profile. Accepting `produce-proofs` during setup does not establish
finite-field proof export, completeness or Lean reconstruction. No M1 input
contains `get-proof`. Unsat cores, if collected in future diagnostic work, are
not proof evidence; this probe suite does not request them.

## Immutable artifact identities

Release [cvc5-1.4.1](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.4.1), API
release **396904860**, is mutable. Neither that name nor an asset ID is a content
pin. Both SHA-256 values below are mandatory before use. The source identity is
[2b2e84419f70817ec919a784a48806e79f677240](https://github.com/cvc5/cvc5/tree/2b2e84419f70817ec919a784a48806e79f677240);
release provenance plus the binary's short revision is not an independently
reproduced source-to-binary correspondence.

| Platform | Asset ID / archive | Archive SHA-256 | Executable SHA-256 |
| --- | --- | --- | --- |
| Linux arm64 | 589210773 / `cvc5-Linux-arm64-static-gpl.zip` | `e6cac10f5b80177b21ef56660ea580120fb8b614ceacc8ba8907c0fcfd9a1e7c` | `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86` |
| Linux x86_64 | 589228193 / `cvc5-Linux-x86_64-static-gpl.zip` | `d0b54324ec2129697975da8753767fd255309947b87832917d32a78da7d16666` | `b265759b80da81b51df0eac26f6289630860617ed7cdce86f93352e4ce84e59f` |

Archive executable member: `<archive basename without .zip>/bin/cvc5`.
Download URLs are the corresponding names beneath
`https://github.com/cvc5/cvc5/releases/download/cvc5-1.4.1/`.

## First-job acquisition and stable consumer interface

Run from the repository root. Acquisition is **only** for an explicitly
network-enabled setup/CI phase; it is not an offline fallback. The following
commands stage the native arm64 tree and retain the approved x86_64 inventory
in a separate root without attempting cross-architecture execution:

```sh
python3 scripts/finite_fields/check_manifest.py docs/finite-fields/solver-manifest.json
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --fetch-only
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields-x86_64 --profile solving --platform linux-x86_64 --fetch-only
```

On a native x86_64 worker the first acquisition command selects x86_64; the
explicit alternate-platform inventory can instead use `--platform linux-arm64`
and a different root. `--platform` is acquisition-only. It does not authorize
running a mismatched executable. Existing staged profile destinations are not
overwritten: select a fresh root for a new acquisition. Nothing is selected
from PATH and no image's installed executable substitutes for an archive.

Layout beneath each `ROOT/<profile>/`:

- `archive.zip`: original downloaded bytes, retained after extraction.
- `payload/`: complete safe archive payload, including upstream license files.
- `bin/cvc5`: verified selected executable, the stable consumer entry point.
- `metadata.json`: platform, profile and manifest-bound provenance/configuration.
- `evidence/`: retained version/configuration and per-case execution records.

Acquisition validates the manifest, profile and platform, permits HTTPS GitHub
release acquisition only, bounds download/archive sizes, verifies the archive
hash **before extraction**, rejects unsafe paths/links/special entries and
verifies the executable hash before publishing the profile directory. A failed
acquisition cannot expose a partially accepted profile. Hashes are approvals,
not values to refresh after a mismatch.

Later offline workers require the **whole profile tree**, not just `bin/cvc5`.
The intended stable command is:

```sh
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --offline --check
```

Offline checking revalidates archive, payload executable, staged executable,
profile/platform metadata, version and configuration before protocol runs.
Absent bytes, different bytes, a wrong platform, zero cases, failed setup,
missing CoCoA or a wrong result fail closed. It never downloads or repairs a
profile. The Python offline process denies socket/DNS operations; only pinned
local solver bytes are executed. This application-level guard is not a claim
of an OS network namespace around child processes; CI can additionally run in
a network-disabled worker. FFM-10 owns live Lake/CI wiring.

Profiles, identities, approved argv, bounds, capabilities and protocol cases
are manifest data, not a hardcoded `solving` dispatch. A later approved profile
can add artifacts and structured expected responses without changing these
new protected scripts. Such extensibility does **not** approve an M2 profile.

## Protocol and independently checked capabilities

Every solving invocation uses the production cvc5 argv from
`Blaster/Smt/Env.lean`:

```text
--lang smt2 --incremental --parsing-mode=lenient --dt-nested-rec
```

Every committed `.smt2` fixture contains the full production setup in order:

```smt2
(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :mbqi true)
(set-option :macros-quant true)
(set-logic ALL)
```

No special probe-only handshake is used. Subsequent `get-option` queries
independently check that `:ff-field-polys` is **false** and `:ff-solver` is
**gb**; the fixtures do not enable field polynomials. A binary needing different
setup would require a matching approved runtime change, not a probe workaround.
`--version` and `--show-config` separately require version 1.4.1, revision
2b2e844, `cocoa: yes`, `poly: yes`, `cln: yes`, `glpk: yes`, `gmp: no`, and
`assertions: no`. Build timestamps and compiler-banner formatting are not
protocol assertions.

| Case | Expected result | Independent reason |
| --- | --- | --- |
| F7 `x*y = 0`, `x != 0`, `y != 0` | UNSAT | A field has no zero divisors. |
| F3 `x*x + 1 = 0` | UNSAT | Squares modulo 3 are 0 and 1, never 2. |
| F7 `x + 1 = 0`, canonical literals | SAT; `get-value (x)` gives residue 6, modulus 7 | 6 is the unique additive inverse of 1 modulo 7. |
| Same F7 equation, typed literals | Same SAT/model obligation | Checks `(as ffN (_ FiniteField 7))` independently of canonical `#fNmP` input. |

The parser checks complete ordered S-expression responses and expected success
acknowledgements, results and model term structure. Whitespace is incidental;
missing/trailing responses, errors, wrong residues or wrong moduli are not.
Finite-field values are compared semantically at the required modulus, including
typed/canonical presentations. Solving, setup/model capability and deferred
proof-export status are separate manifest entries. SAT alone cannot pass a
model obligation or establish a proof capability.

Per-invocation resource bounds: 20 seconds wall time, 15 seconds CPU, 1 GiB
address space, 1 MiB response output; archives are limited to 256 MiB compressed,
1 GiB expanded and 10,000 members; response nesting is capped at 128. Complete
inputs, stdout, stderr, command argv and shell rendering, exit status and
resource-failure details are retained in evidence. Output stopped at a resource
bound is marked as incomplete and fails; it is never accepted as a response.

## Local invalid-input checks

```sh
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --negative-fixtures
```

This mode needs neither an installed solver nor an artifact root. Declarative
negative fixtures exercise the production validators and must be rejected for
the expected reason, not merely raise an arbitrary exception. The fixture
inventory covers identity/schema/profile/platform mismatches, `cocoa: no`,
unsafe archives and malformed/truncated/oversized or semantically wrong
responses, including processes reporting exit 0.

## Pinned source references and unexecuted build recipe

Read these exact public files; no additional repository is cloned:

- [FF options, b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/options/ff_options.toml):
  documents false `ff-field-polys` and `gb`/`split`. A fork's source defaults
  alone do not establish upstream executable behavior. `split` is not rerun.
- [SMT2 term parser, b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/parser/smt2/smt2_term_parser.cpp):
  `FIELD_LITERAL` splits the value/modulus in `#fNmP`, constructs the field sort
  and then the element. Canonical parsing is also exercised by live fixtures.
- [INSTALL.rst, b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/INSTALL.rst):
  requires GCC/G++ >= 7 or Clang >= 5, CMake >= 3.16, Make or Ninja, Python >=
  3.7 with pyparsing (tomli below Python 3.11), GMP 6.3, CaDiCaL >= 2.1.0 and
  SymFPU. FF support uses **patched CoCoA** with `--cocoa --gpl`. Optional CLN
  >= 1.3, LibPoly >= 0.2.0 and glpk-cut-log are relevant to GPL static builds.
- [Historical lean-cvc5 lakefile, 4733baf](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean):
  selects mutable clean-wip assets. This is historical package-selection
  evidence only; the package and its candidate executable are not built/run.

The reference files are provisioned locally beneath
`.artifacts/finite-fields-reference/` before offline validation. Their SHA-256
identities are recorded with the job evidence. They are not needed for a normal
consumer's offline solver check; fixtures and the approved staged archive tree
are sufficient. No external source file is substituted into Blaster.

Reference recipe, **not executed** on either platform:

```sh
# Only in a separately approved source tree at the selected source commit,
# with independently pinned and already provisioned toolchain/dependencies:
./configure.sh --static --cocoa --gpl
make -C build
make -C build check
```

This is dependency/configuration guidance, not a bit-reproducible build recipe
or a substitute artifact. Before a source-build distribution could be approved,
its owner must lock source archive and dependency URLs/hashes/patches, compiler,
linker, CMake, host/target, base OS, all configure/packaging flags, license notices
and build/test logs. In particular the reference's `--auto-download` convenience
is not permission for unpinned dependency acquisition. No fresh source build,
dependency repair or source-to-binary reproduction is claimed here.

### Reference acquisition evidence (2026-10-27)

The HTTPS reader read all four pinned references. Their exact bytes were then
retained locally with these commands, each exiting 0:

```sh
curl --fail --location --proto '=https' --proto-redir '=https' https://raw.githubusercontent.com/psaccomani15/cvc5/b1f8abb80021d687df7547fedc41882c4416d981/INSTALL.rst --output .artifacts/finite-fields-reference/INSTALL.rst
curl --fail --location --proto '=https' --proto-redir '=https' https://raw.githubusercontent.com/psaccomani15/cvc5/b1f8abb80021d687df7547fedc41882c4416d981/src/parser/smt2/smt2_term_parser.cpp --output .artifacts/finite-fields-reference/smt2_term_parser.cpp
curl --fail --location --proto '=https' --proto-redir '=https' https://raw.githubusercontent.com/psaccomani15/cvc5/b1f8abb80021d687df7547fedc41882c4416d981/src/options/ff_options.toml --output .artifacts/finite-fields-reference/ff_options.toml
curl --fail --location --proto '=https' --proto-redir '=https' https://raw.githubusercontent.com/abdoo8080/lean-cvc5/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean --output .artifacts/finite-fields-reference/lakefile.lean
```

An earlier Python-urllib attempt through the tool's evaluation subprocess
failed DNS resolution before saving a reference. The shell acquisitions above
succeeded; no source URL or pin was substituted.

| File | SHA-256 of retained bytes |
| --- | --- |
| `ff_options.toml` | `12bc3c5556d1402683ed2426291fec81a2436f71471fd71393610db028ad195b` |
| `smt2_term_parser.cpp` | `e89559403f564830c679cb1e08d34ae80725288ae4af9d21489dff27bd6aa284` |
| `INSTALL.rst` | `8616cd7c65ad6a2d9960473ffada0ae8897ae94666aa1bb10126cb63bf76e0e6` |
| `lakefile.lean` | `4441873f5d2c2791dbb04528385d5775fb30c046df974e24a93d99269dd3d246` |

## Fresh acquisition and offline qualification (2026-10-27)

The first-job acquisition commands above were **executed in this job**, not
copied from FFM-03's historical runs:

| Command / scope | Observed outcome |
| --- | --- |
| Native-root `--profile solving --fetch-only` | Exit 0; 5.79 seconds; both approved arm64 hashes matched before publication of `.artifacts/finite-fields/solving`. Returned `qualified: false`, correctly separating acquisition from live capability checks. |
| Alternate-root `--profile solving --platform linux-x86_64 --fetch-only` | Exit 0; 5.90 seconds; both approved x86_64 hashes matched before publication of `.artifacts/finite-fields-x86_64/solving`. No executable was run. |
| `sha256sum /opt/cvc5-Linux-arm64-static-gpl/bin/cvc5` | Exit 0; matched `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`, an additional byte-identity check, not a provisioning substitute. |
| `check_manifest.py docs/finite-fields/solver-manifest.json` | Exit 0; one selected profile, both immutable artifact pairs and all fixture/evidence references valid. |
| Native-root `--profile solving --offline --check` | Exit 0; version/configuration and all four cases passed. CoCoA present; `ff-field-polys=false`, `ff-solver=gb`; both SAT cases returned `((x #f6m7))`. |
| `--negative-fixtures` | Exit 0; all 34 invalid inputs rejected for their named categories without invoking a solver or network acquisition. |
| Offline check using the x86_64 root on this arm64 host | Expected exit 1: `platform: staged metadata does not match the host platform`; no cross-platform execution. |
| Offline check using absent `.artifacts/absent-ffm09` | Expected exit 1: missing staged `metadata.json`; no acquisition or PATH fallback. |

The first offline attempt failed the version parser because it required the
incidental word `version`; the pinned binary prints
`cvc5 1.4.1 [git 2b2e844 on branch HEAD]`. No solving cases ran in that failed
attempt. The parser was corrected to accept the banner forms while retaining
the exact version/revision requirements. The subsequent full run and final
acceptance rerun each executed all four solving/model cases successfully. No
solver byte, approved hash, runtime handshake or expected solving result changed.

Complete successful inputs, stdout, stderr, argv, shell command lines, exit
statuses and measured durations are committed in
[observed-linux-arm64.json](../../fixtures/finite-fields/protocol/observed-linux-arm64.json).
These are observations, not byte-for-byte golden outputs: checks compare
protocol structure and semantic field values. Local `evidence/run-*` directories
also retain the initial failed attempt and both successful runs without
overwriting them. The final accepted run is
`run-20261027T192825Z-dbe77128d6f64237b7ad9e3b99edd062`; the committed full
transcript is the preceding successful run
`run-20261027T192546Z-8d758a78d28e4a0d8fa5ba67d1a1667f`.

Additional local smoke checks exercised the actual helpers: canonical, typed
and negative representative (`#f-1m7`) model terms with whitespace/comments;
current/future version token syntax; an additional manifest-defined profile;
blocked socket creation and DNS; bounded child timeout/output with retained
failure evidence; and a corrupted staged executable rejected before process
execution. Temporary smoke inventories were removed. None staged or probed a
proof-producing artifact.

### Qualification limits

- **Linux arm64 / gb only:** native setup, CoCoA configuration, two UNSAT cases
  and two SAT/model cases qualified. This is small-probe evidence, not general
  completeness, performance or rule-audit evidence.
- **Linux x86_64:** archive/executable identities acquired and verified only.
  Native version/configuration, setup, solving and models remain `not run`;
  the manifest records each capability separately. The host-mismatch rejection
  is intentional, not a skipped case reported as passed.
- **split:** source-described but not executed. **Proof export:** deferred to
  M2, not tested by accepting `produce-proofs`. **Source build:** not run.
- No image build/redistribution, external package build, Lake/CI integration,
  cvc5-floor/all-solvers tier or remote CI run is claimed. FFM-10 and later
  native x86_64 qualification consume the same stable interfaces.
