# FFM-03: Finite-field solver distribution and ownership

## Decision status: proposed; consuming artifact/CI work blocked

Select **separate profiles**, not a replacement ordinary solver:

- **`solve` (proposed):** upstream cvc5 **1.3.4 static GPL**, Linux x86_64
  and Linux arm64, with the archive and executable identities below. The
  existing-version GPL asset demonstrably solves the small FF examples below;
  a newer solving pin is not needed on that evidence.
- **`proof` (proposed):** the independently pinned Linux x86_64 fork executable
  reporting **`1.3.3.dev+clean_WIP@b1f8abb`**, using CPC output. Select its
  content hashes, not the mutable `clean-wip` tag, as artifact identity. Its
  observed source identifier resolves to
  `b1f8abb80021d687df7547fedc41882c4416d981`. This is a proof-production candidate,
  not a verified Lean proof backend or evidence of complete CPC coverage.
- **Provisioning route:** propose the user-specified **worker-image route**.
  The image owner stages both approved profiles before the first protocol job
  starts. `lake --version` is setup, **not provisioning**. No protocol script
  exists yet; initial acquisition must use the independent commands below.

**No artifact is approved for consuming jobs by this record.** The supplied
PROJECT grants repository work, not GPL-linked CI consent, platform commitments
or distribution ownership. No maintainer answer to those decisions is present
in the supplied inputs or the preceding local decisions. The selections above
remain proposed until the maintainer records the approvals below. FFM-09 live
validation and FFM-10 acquisition/CI work must not treat this document as a green
parent output. Missing profiles are a setup failure, never a skipped test.

### Maintainer policy and ownership decision required

| Decision | Proposed choice / responsibility | Approval status |
| --- | --- | --- |
| GPL-linked CI executable policy | Permit separate-process execution of the hash-pinned GPLv3/CoCoA binaries in the dedicated FF lane; do not link them into Blaster. Require license notices and corresponding-source/build availability review before hosting or image redistribution. This is not legal advice or distribution consent. | **Unanswered; blocking.** Maintainer must explicitly accept or reject, with scope and decision reference/date. Preinstallation of GPL cvc5 1.4.1 does not answer it. |
| Accountable distribution owner | Riley/project maintainer approves immutable identities, replacements and platform scope, and names the operational owner. | **Proposed, not an accepted assignment.** |
| Acquisition, hosting and image operations | Named iog worker-image operator fetches/verifies hosted assets, retains archives, licenses, source/build evidence, publishes an image by digest and makes profiles available at job start. Upstream `cvc5/cvc5` and `psaccomani15/cvc5` currently host the candidate assets; neither is assigned project support obligations. | **Operator not named/accepted; blocking.** No new project hosting URL or image digest is approved. |
| External builds | A named distribution build owner supplies the recipe, dependency locks, build logs and hashed archive/executable pair for any unavailable platform. Builds happen outside this checkout under separately authorized source/dependency access. | **Owner not named/accepted; blocking where a new build is needed.** |
| Platforms | Linux x86_64 for both profiles; Linux arm64 for solving only until proof execution is qualified as described below. macOS and Windows are not selected despite release assets existing. | **Proposed; maintainer must accept platform scope and ARM proof route.** |
| CI acquisition | A separately network-enabled, owner-approved FF acquisition stage executes the same hash checks and provides the profile tree to offline consumers. An image-based CI runner may instead supply the same approved tree. | **Proposed; FFM-10 owns implementation and filename approval.** |

Required policy response: approve/reject GPL execution and redistribution scope;
name accepting operational/build owners; approve platforms and ARM proof route;
approve exact artifact rows and immutable image digest/acquisition-stage scope.
A rejection requires a revised distribution decision, not silently using another
binary. This job neither contacts maintainers nor publishes artifacts.

Approval must be recorded here with the maintainer's decision reference/date,
accepted operator and build-owner names, exact approved artifact rows, supported
execution platforms, and provisioning route/image digest. A successful check,
publication of this document, or serial integration-branch append is not that
approval. Until then the approved artifact set and approved provisioning routes
are **empty**; the commands below are a concrete proposal, not authorization.
FFM-09/FFM-10 must remain blocked even if this documentation's PROJECT checks pass.

## Evidence and comparison

The incoming record reports the following observations on 2026-10-23 from
public references and downloaded release archives; **no external repository
was cloned or built**. Binary execution and executable hashes below are inherited
evidence, not fresh runs in this refresh. Current metadata checks and repository
validation are recorded separately in the ticket report.

- The [ordinary workflow](../../.github/workflows/ci-linux.yaml) retains
  cvc5 **1.3.4**, support floor **1.2.1**, and Z3 **4.15.2**, including the
  all-solvers lane. It downloads the ordinary non-`-gpl` cvc5 asset. Selecting
  the GPL asset for `solve` does not change that lane's binary, PATH or checks.
  All ordinary lanes remain required. No workflow or protected file is edited.
- The pinned [lean-cvc5 lakefile](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean)
  selects `clean-wip` and platform-dependent assets without a content pin.
  Do not reuse that mutable selection as a reproducible source identity.
- The [upstream tag API](https://api.github.com/repos/cvc5/cvc5/git/ref/tags/cvc5-1.3.4)
  resolves to `f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341`.
  Both tested upstream executables report `1.3.4`, `git f3b21c4`, GPLv3,
  `cocoa: yes`, `poly: yes`, `cln: yes`, `gmp: no`, `assertions: no`.
  GCC 11.4.0 build times: ARM May 7 2026 15:32:17; x86 May 7 2026 15:35:15.
- The [fork tag API](https://api.github.com/repos/psaccomani15/cvc5/git/ref/tags/clean-wip)
  resolves to **`f011843845a37ddeb555d04a8b07c68641810c52`**, not either
  tested binary revision. The x86 asset reports `b1f8abb`, GPLv3, `cocoa: yes`,
  `poly: yes`, `gmp: yes`, `cln: no`, `assertions: no`, Clang 18.1.3,
  Apr 24 2026 00:37:10. Its version string is evidence of its claimed revision,
  not independently verified build provenance.
- The fork ARM asset reports `1.3.3.dev+clean_WIP@73ef63c`, resolving through the
  [commit API](https://api.github.com/repos/psaccomani15/cvc5/commits/73ef63c)
  to `73ef63c4a77cdd53c277496982b496d946cb5529`; Clang 18.1.3,
  Mar 18 2026 18:39:09, `cocoa: no`, BSD banner. It rejects field problems:
  `cvc5 can't solve field problems since it was not configured with --cocoa`.
  **Reject this ARM asset for both profiles.** A shared tag does not imply
  cross-platform source, feature or license equivalence.
- The preinstalled `/usr/local/bin/cvc5` resolves to
  `/opt/cvc5-Linux-arm64-static-gpl/bin/cvc5`, reports `1.4.1`, `git 2b2e844`,
  GPLv3/CoCoA and executable SHA-256
  `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`.
  It solves the same examples, but its proof also contains a trust step.
  It is not selected: preinstallation alone provides neither an approved
  archive/source pin nor an advantage for this proof-production requirement.

### Exact candidate identities

Hosted releases: [upstream 1.3.4](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.4)
([API](https://api.github.com/repos/cvc5/cvc5/releases/tags/cvc5-1.3.4), release
319022075) and [fork clean-wip](https://github.com/psaccomani15/cvc5/releases/tag/clean-wip)
([API](https://api.github.com/repos/psaccomani15/cvc5/releases/tags/clean-wip), release
274645891). Both APIs report `immutable: false`. Asset IDs aid audit; **hashes
are mandatory** even if URLs/IDs remain unchanged. All four archive hashes below
were computed after downloading and matched the API digests; executable hashes
were computed from the extracted bytes.

| Profile / platform | Asset ID; archive name | Archive SHA-256 | Executable SHA-256 |
| --- | --- | --- | --- |
| Proposed solve / Linux arm64 | 414511647; `cvc5-Linux-arm64-static-gpl.zip` | `92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889` | `d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9` |
| Proposed solve / Linux x86_64 | 414514204; `cvc5-Linux-x86_64-static-gpl.zip` | `3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5` | `278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a` |
| Proposed proof / Linux x86_64 | 408363254; `cvc5-Linux-x86_64-static.zip` | `918361fcee2e1d3c64be5d20eb62156aaee73943df3ae7aa62d58f199b6785dc` | `514ccdaea9e4a5a0eb7d3be2e89b9d6fc893e3560d0f536cbe5e122ef6376a61` |
| Rejected fork / Linux arm64 | 377257754; `cvc5-Linux-arm64-static.zip` | `583869b742529eab238c802d9dffd6386e3c258b5c83c1bb250aeb642df30f3a` | `65222271b95f52c495f5ff9483b7cfbd9c047170719efa9a4108469ec21caf10` |

Download URL is exactly the corresponding release prefix plus archive name:

- `https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/`
- `https://github.com/psaccomani15/cvc5/releases/download/clean-wip/`

Executable member is `<archive name without .zip>/bin/cvc5` in every row.
Source references for selected profiles are respectively
[`f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341`](https://github.com/cvc5/cvc5/tree/f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341)
and [`b1f8abb80021d687df7547fedc41882c4416d981`](https://github.com/psaccomani15/cvc5/tree/b1f8abb80021d687df7547fedc41882c4416d981).
Do not use the fork release tag as the source-build revision.

### Solving is not proof qualification

The smoke inputs use F5: `x*x = 4` is SAT (model `x = #f3m5` observed);
`x*x = 2` is UNSAT because the squares are 0, 1 and 4. The proof input adds
`:produce-proofs true` and `(get-proof)` to that nonlinear contradiction.

| Executable | SAT/model and UNSAT | Proof production |
| --- | --- | --- |
| Upstream 1.3.4 GPL, ARM and x86 | Both exit 0 with expected answers | Exit 0, but CPC includes `trust TRUST THEORY_LEMMA` and `:rule trust`; not selected for FF proof production. |
| Fork x86 `b1f8abb` | Both exit 0 with expected answers | Exit 0, CPC contains `ff_ideal_generator`, `ff_poly_norm`, `ff_poly_norm_eq`, `ff_poly_conversion`, `ff_root_branch`; explicit `--proof-format-mode=cpc` also exercised. |
| Fork ARM `73ef63c` | Both exit 1, missing CoCoA | Exit 1, same missing-CoCoA error. |
| Installed ARM 1.4.1 GPL | Both exit 0 with expected answers | Exit 0 with the same trust-step limitation as upstream 1.3.4. |

The x86 ELF binaries executed successfully in this ARM-hosted sandbox. This is
**not a native x86 runner qualification or a portable emulation guarantee**.
For both-profile support on ARM workers, the image owner must either explicitly
qualify and approve the x86 execution facility (record its implementation,
version/configuration and image digest), or supply a CoCoA-enabled ARM build of
the selected proof source with new archive/executable hashes and native evidence.
No such ARM proof build or execution-facility approval exists in this record.
There is no fallback to the rejected ARM asset or to ordinary PATH `cvc5`.

FFM-09 must separately test each selected executable's version/config, FF
SAT/model, FF UNSAT, requested proof format, and proof output on each approved
execution platform. These tiny examples do not establish all FF operations,
proof formats or proof completeness. No CPC parser, independent proof checker,
or Lean reconstruction was exercised. Rule names above are output observations,
**not checked Lean proof coverage**; FFM-19 owns that distinction. No trusted
axiom or widening of `blasterProven` is authorized.

## Provisioning and consumer contract

### Initial acquisition, independent of the future protocol script

The following are exact **proposed operator commands**, runnable in an approved
network-enabled image build/acquisition stage **after policy approval**. They
stage the three proposed artifact rows without a source checkout. They are not
installed scripts, manifests, or an invocation of a nonexistent FFM-09 script.
Use a fresh staging root; never overwrite an existing identity in place.

```sh
set -eu
ROOT="$PWD/.artifacts/finite-fields"
acquire() {
  profile=$1 platform=$2 prefix=$3 name=$4 archive_sha=$5 executable_sha=$6
  d="$ROOT/$profile/$platform"
  test ! -e "$d"
  mkdir -p "$d"
  curl --fail --location --proto '=https' --proto-redir '=https' \
    "$prefix/$name.zip" --output "$d/archive.zip"
  printf '%s  %s\n' "$archive_sha" "$d/archive.zip" | sha256sum --check --strict -
  unzip -q "$d/archive.zip" -d "$d/payload"
  exe="$d/payload/$name/bin/cvc5"
  printf '%s  %s\n' "$executable_sha" "$exe" | sha256sum --check --strict -
  test -x "$exe"
}
acquire solve linux-arm64 \
  https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4 \
  cvc5-Linux-arm64-static-gpl \
  92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889 \
  d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9
acquire solve linux-x86_64 \
  https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4 \
  cvc5-Linux-x86_64-static-gpl \
  3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5 \
  278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a
acquire proof linux-x86_64 \
  https://github.com/psaccomani15/cvc5/releases/download/clean-wip \
  cvc5-Linux-x86_64-static \
  918361fcee2e1d3c64be5d20eb62156aaee73943df3ae7aa62d58f199b6785dc \
  514ccdaea9e4a5a0eb7d3be2e89b9d6fc893e3560d0f536cbe5e122ef6376a61
```

On each approved execution platform, set `d` and `exe` to the matching row
above and retain the complete outputs and exit codes, not just a version line:

```sh
"$exe" --version > "$d/version.txt"
"$exe" --show-config > "$d/config.txt"
```

The owner checks the expected revision, GPL banner and `cocoa: yes`, then runs
both solving cases; the proof profile additionally runs the explicit CPC case
below. A digest mismatch, missing executable, wrong architecture/configuration,
failed run or absent required proof profile stops provisioning. Never refresh a
hash from the failed download or choose another release automatically.

### Handoff to first protocol job, later workers and CI

- Image operator retains `archive.zip`, extracted payload (including licensing
  files), identity inventory and version/config evidence at
  `/opt/finite-fields/<profile>/<platform>/` in an **approved image digest**.
  Record the digest separately from mutable `agentstack-worker-iog:latest`.
  At job startup the operator runs, before offline checks:

  ```sh
  test ! -e .artifacts/finite-fields
  mkdir -p .artifacts
  cp -a /opt/finite-fields .artifacts/finite-fields
  ```

  For the proposed Linux x86_64 pair, the exact offline recheck from the checkout
  root is:

  ```sh
  set -eu
  printf '%s  %s\n' \
    3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5 \
    .artifacts/finite-fields/solve/linux-x86_64/archive.zip \
    278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a \
    .artifacts/finite-fields/solve/linux-x86_64/payload/cvc5-Linux-x86_64-static-gpl/bin/cvc5 \
    918361fcee2e1d3c64be5d20eb62156aaee73943df3ae7aa62d58f199b6785dc \
    .artifacts/finite-fields/proof/linux-x86_64/archive.zip \
    514ccdaea9e4a5a0eb7d3be2e89b9d6fc893e3560d0f536cbe5e122ef6376a61 \
    .artifacts/finite-fields/proof/linux-x86_64/payload/cvc5-Linux-x86_64-static/bin/cvc5 \
    | sha256sum --check --strict -
  test -x .artifacts/finite-fields/solve/linux-x86_64/payload/cvc5-Linux-x86_64-static-gpl/bin/cvc5
  test -x .artifacts/finite-fields/proof/linux-x86_64/payload/cvc5-Linux-x86_64-static/bin/cvc5
  ```

  These checks read only the copied tree and do not reacquire missing artifacts.
  They verify bytes/permissions, not execution-platform or proof capability.
  ARM solving uses its separate row above; it still needs an approved proof
  execution route. No global `cvc5` symlink or PATH replacement is permitted.
- **First FFM-09 sandbox:** image/operator stages bytes and the approved identity
  inventory first, without relying on FFM-09 code or a not-yet-created manifest.
  The job then implements manifests/probes against those preexisting inputs.
  It cannot declare live validation complete until both selected profiles run.
- **Manifest interface reserved for FFM-09:**
  `.artifacts/finite-fields/solve/<platform>/manifest.json` and
  `.artifacts/finite-fields/proof/<platform>/manifest.json`. All artifact/evidence
  paths in each manifest are relative to its containing profile/platform
  directory: `archive.zip`, `payload/<name>/bin/cvc5`, `version.txt`,
  `config.txt`. No absolute sandbox paths, cross-profile `..` paths or inferred
  PATH executable. FFM-09 owns the schema, not this ticket.
- Each manifest must bind profile purpose, platform and execution requirements,
  approved policy/owner decision, URL/release/asset ID, archive and executable
  SHA-256, source commit and provenance status, version/config evidence,
  explicit solver arguments, license/build-recipe reference and execution
  status, and independent solve/proof qualification results. An unsupported
  platform has no valid manifest; absence is an error, not permission to reuse
  another row. Hashes are required separately for every platform/build.
- **Later offline workers:** the image supplies both profiles plus the
  owner-reviewed FFM-09 manifests. Offline checks verify them, never download or
  build missing artifacts. The image operator and distribution owner maintain
  the inventory/manifests together; changing bytes requires a reviewed new
  identity and requalification, never an in-place hash update.
- **CI:** FFM-10 implements the approved network acquisition stage using the
  same immutable inventory and exports `.artifacts/finite-fields` with both
  profiles/manifests to the consuming job, which verifies again offline. Retain
  license/source obligations on exported artifacts and caches. Ordinary solver
  jobs keep their current acquisition and pins. No CI implementation is added.
- An explicitly approved **operator-provided archive/executable pair** may
  replace a network transfer, but must match both pinned hashes, extraction
  member and evidence above. An unpinned executable alone is insufficient.
  Network access or an operator archive is an alternative requiring explicit
  approval, not a hidden bootstrap assumption for offline workers.

## External source-build recipe requirement

**Recipe status:** requirement specified; complete reproducible owner recipe
not yet supplied. **Execution status:** **not run**; neither candidate rebuilt.
Downloaded-byte verification and smoke success do not establish reproducibility
from source or bit-for-bit correspondence to the claimed source revision.

The distribution owner must retain a recipe for each approved build, including
host/target triples, base OS/container digest, compiler/linker/CMake versions,
full source commit and source archive hash, all dependency URLs/hashes and
patches (especially patched CoCoA), configure flags, build/test/package commands,
licenses/corresponding source, final archive/executable hashes and qualification
outputs. Store recipe availability separately from execution status (`not run`,
`failed`, or `passed` with platform, date and logs). New externally built ARM
proof artifacts require an executed recipe and their own identity row.

The pinned [fork INSTALL.rst](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/INSTALL.rst)
documents `--cocoa --gpl` and recommends `--auto-download` for patched CoCoA.
An owner recipe must lock those downloads; an unchecked `--auto-download` run
is not reproducible. Starting configure/build commands for an externally
provided, verified source tree are `./configure.sh --static --cocoa --gpl`,
`make -C build`, and `make -C build check`, with exact dependency paths/options
and packaging supplied by the owner. These are **not an executed or complete
recipe**. Do not clone the referenced repository, install unapproved native
dependencies, or claim the mutable `clean-wip` source reproduces `b1f8abb` here.

## FFM-03 ticket report and job summary

Change in this refresh: clarify the approval/dispatch gate, add exact offline
hash/permission checks for the proposed x86 pair, and separate inherited binary
evidence from current metadata and repository validation. The existing record's
candidate choices, rejected fork ARM asset and profile-relative contract are
retained. No manifests, protocol scripts, workflows, Lean code, tests, pins or
protected files are changed.
This section is the ticket report and job summary retained for the stack's
commit; no publication, maintainer consent or completed FFM-09 gate is claimed.

### Inherited reproduction commands and observed outcomes

Research used `.artifacts/ffm03-research` temporarily, not the approved consumer
tree. Four downloads used `curl -fL --retry 2 -o <archive> <exact URL above>`;
local archive names were `upstream-arm64.zip`, `upstream-x86_64.zip`,
`fork-arm64.zip`, `fork-x86_64.zip`. All exited 0. For each archive:
`sha256sum <archive>`; `unzip -q <archive> -d <same basename without .zip>`;
`sha256sum <extraction directory>/<archive member>` all exited 0 with the
identities recorded above. Each candidate's `--version`/`--show-config` was
observed (the fork's `--show-config` includes its full version banner).
The x86 `file` command identified both as statically linked ELF x86-64.

The temporary files contained exactly:

```smt2
; sat.smt2
(set-logic QF_FF)
(set-option :produce-models true)
(declare-fun x () (_ FiniteField 5))
(assert (= (ff.mul x x) #f4m5))
(check-sat)
(get-value (x))
```

```smt2
; unsat.smt2
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 5))
(assert (= (ff.mul x x) #f2m5))
(check-sat)
```

```smt2
; proof.smt2
(set-logic QF_FF)
(set-option :produce-proofs true)
(declare-fun x () (_ FiniteField 5))
(assert (= (ff.mul x x) #f2m5))
(check-sat)
(get-proof)
```

For each of the four extracted executables and `/usr/local/bin/cvc5`, each
input was run as `timeout 20 "$solver" --lang=smt2
".artifacts/ffm03-research/$input.smt2"`. Per-process exit codes and answers are
in the comparison table; none timed out. Additional exact invocation:

```sh
timeout 20 .artifacts/ffm03-research/fork-x86_64/cvc5-Linux-x86_64-static/bin/cvc5 --lang=smt2 --proof-format-mode=cpc .artifacts/ffm03-research/proof.smt2
```

This exited 0 with the FF-specific CPC steps recorded above.
`--proof-format-mode=help` printed `cpc (default)` and the other format choices
but exited 1; it was an informational query, not a passing capability check.
A Python HTTPS metadata attempt failed with DNS resolution error; shell `curl`
and HTTPS reader requests subsequently succeeded. No source checkout resulted.
The proposed operator staging commands were documented, **not executed as
approved provisioning**. Temporary research downloads/inputs are removed after
inspection; no binaries or experimental manifests enter the commit.

### Inherited repository validation

The incoming record reports these earlier commands from the repository root,
using the prescribed CI Z3 PATH rather than the default assurance solver.
These are historical results, not this refresh's runs:

| Exact command | Outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass, exit 0; `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 4.15.2; 171 jobs, 89.94 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; same Z3 4.15.2; pure tier completed 200 jobs, Z3 tier completed 611 jobs; 197.56 seconds total. Lifecycle model-response and arithmetic Undetermined warnings were emitted; no checks or expectations changed. |
| `git add --intent-to-add docs/finite-fields/m1-solver-distribution-decision.md && git diff --check && test -s docs/finite-fields/m1-solver-distribution-decision.md` | Pass, exit 0; includes the new document in the whitespace check. |
| `git diff --check && test -s docs/finite-fields/m1-solver-distribution-decision.md` | Pass, exit 0 after the final report update. |

The requested pin search was performed with the repository search tool, pattern
`1\.3\.4|1\.2\.1|4\.15\.2`, path `.github/workflows/ci-linux.yaml` (equivalent
to the ticket's `rg -n` predicate). It matched Z3 4.15.2 at line 16, cvc5 1.3.4
at line 18, and floor 1.2.1 at line 19, plus the floor lane references. The
workflow was not edited. No default-environment `lake test` was run. Local
PROJECT checks do not run remote CI or the ordinary cvc5/floor/all-solvers lanes.

### Current refresh evidence

The HTTPS reader retrieved the two release APIs linked above, the upstream
[x86 asset API](https://api.github.com/repos/cvc5/cvc5/releases/assets/414514204),
and the fork tag API. Release IDs, mutable-release status, the three proposed
archive names/IDs/digests/download URLs, and the rejected ARM archive metadata
still match this record. The fork tag still resolves to `f011843...`, not the
proof executable's reported `b1f8abb...` revision. Metadata does not establish
executable hashes, provenance or capability.

The filesystem lookup `.artifacts/**` found no `.artifacts` directory in this
refresh. Neither profile is staged here. No archive was downloaded, no solver
smoke was rerun, and no source build or approved provisioning was performed.
The inherited failure of the fork ARM binary remains a rejection, not a reason
to rerun or waive that capability check.

Current validation, run from the repository root on 2026-10-23:

| Exact command / check | Observed outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2; 171 jobs, 86.83 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; same Z3 4.15.2; pure tier 200 jobs and Z3 tier 611 jobs, 172.36 seconds total. Lifecycle model-response warnings were emitted; no check or expectation was changed. |
| `git diff --check && test -s docs/finite-fields/m1-solver-distribution-decision.md` | Pass, exit 0. |
| `bash -n`, each of this document's five `sh` fenced blocks supplied separately on stdin | Pass, all five exited 0. Syntax only: acquisition, copy and offline verification were not executed against staged profiles. |
| Repository search, pattern `1\.3\.4\|1\.2\.1\|4\.15\.2` with regex alternatives (unescaped pipes), path `.github/workflows/ci-linux.yaml` | Matches at lines 16, 18, 19, 41, 138 and 139; ordinary pins remain unchanged. This uses the search tool rather than shell `rg`. |

No default-environment `lake test`, remote CI, ordinary cvc5/floor/all-solvers
lane, or new FF capability run is claimed. The passing PROJECT checks validate
the unchanged core and pure/Z3 tiers, not the proposed distribution's approval.

### Remaining prerequisites

1. Maintainer policy response and accepted distribution/platform ownership.
2. Approved image digest and first-job staging of both profiles; an approved
   x86 execution facility on ARM, or an externally built/qualified ARM proof
   artifact with both hashes. The rejected ARM release is not a substitute.
3. Owner's complete source-build/provenance recipe and distinct execution status;
   no fresh build or verified source-to-binary correspondence is claimed here.
4. FFM-09 manifests and broader per-platform protocol qualification, followed
   by FFM-10 separately authorized CI acquisition. FFM-19/verified reconstruction
   must not equate CPC output or rule names with Lean-checked coverage.

The documentation can be committed as a **proposed, blocked decision**. The
approved-distribution acceptance goal remains unresolved until those human
policy/ownership and provisioning prerequisites are supplied; this record does
not grant them on the maintainer's behalf.
