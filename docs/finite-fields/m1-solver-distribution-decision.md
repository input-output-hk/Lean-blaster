# FFM-03: Finite-field solver distribution and ownership

## Decision: solving approved; proof production deferred to M2

Select **upstream cvc5 1.3.4 static GPL/CoCoA** as the M1 `solve` profile for
**Linux x86_64 and Linux arm64**, with the exact archive/executable pairs below.
This is an independently hash-pinned FF distribution of the existing ordinary
version, not a replacement for ordinary cvc5. A newer FF-only version is not
needed on the observed solving evidence.

**Decision authority:** Riley's maintainer decisions supplied with FFM-03,
2026-10-27. These supersede this record's previous proposed/blocked policy,
unnamed ownership and two-profile M1 provisioning requirements.

| Decision | Approved scope / accountable owner |
| --- | --- |
| GPL-linked CI policy | Riley permits separate-process execution of the hash-pinned GPLv3/CoCoA cvc5 binaries in workers and the dedicated FF CI lane. They are never linked into Blaster. License notices and corresponding-source availability must be reviewed before any public hosting or image redistribution. Execution approval is not a claim that this review has occurred or blanket distribution consent. |
| Distribution and immutable identities | Riley is the accountable distribution owner and maintainer of the URL/source/hash inventory, platform scope, replacements and requalification. Upstream `cvc5/cvc5` hosts the selected release; it has no newly assigned project support obligation. |
| Image operations | Riley is the iog worker-image operator: acquisition, hash verification, retention of archives/licenses/source evidence, platform qualification, image publication and startup handoff. No external build owner is needed for M1. |
| Platforms | Linux x86_64 and Linux arm64 for solving. No macOS, Windows or cross-architecture execution guarantee is selected. |
| Provisioning and CI acquisition | The approved route is the **iog worker image**, including the dedicated FF CI consumer. Its build fetches the approved hosted assets before jobs start. FFM-10 implements the CI image/tree handoff, not a replacement ordinary solver lane. |
| Image digest | Riley records the immutable digest when the image containing the approved solving artifacts is built. That future digest is **not a prerequisite for completing this distribution decision**; it is required for reproducible consuming jobs. `agentstack-worker-iog:latest` alone is not an immutable identity. |
| Proof production | Deferred to M2. The fork below is a bookmark only: not approved, staged, forked or built in M1. |

The [ordinary workflow](../../.github/workflows/ci-linux.yaml) remains required:
cvc5 **1.3.4**, cvc5 support-floor **1.2.1**, Z3 **4.15.2**, and the all-solvers
lane. Its ordinary cvc5 download is the non-`-gpl` asset. No ordinary binary,
PATH, pin, check or workflow is changed. The GPL asset has a separate identity
and explicit executable path even though its version matches the ordinary lane.

## Selected hosted artifacts and evidence

Release: [cvc5-1.3.4](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.4),
[API release 319022075](https://api.github.com/repos/cvc5/cvc5/releases/tags/cvc5-1.3.4).
The release reports `immutable: false`; URLs and asset IDs are locators, not
content guarantees. Both hashes are mandatory on every acquisition.

| Platform / profile | Asset ID and archive | Archive SHA-256 | Executable SHA-256 |
| --- | --- | --- | --- |
| Linux arm64 / `solve` | 414511647; `cvc5-Linux-arm64-static-gpl.zip` | `92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889` | `d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9` |
| Linux x86_64 / `solve` | 414514204; `cvc5-Linux-x86_64-static-gpl.zip` | `3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5` | `278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a` |

Exact download URLs:

- <https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-arm64-static-gpl.zip>
- <https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-x86_64-static-gpl.zip>

Executable archive member: `<archive name without .zip>/bin/cvc5`.
The [upstream tag](https://api.github.com/repos/cvc5/cvc5/git/ref/tags/cvc5-1.3.4)
resolves to source commit
[`f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341`](https://github.com/cvc5/cvc5/tree/f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341).
This is the selected source reference, consistent with the binaries' short
revision; it is not independent source-to-binary reproducibility evidence.
No external repository was cloned or built.

### Current executable qualification (2026-10-27)

Both release archives were freshly downloaded. Archive hashes matched the
pinned values and GitHub API digests; extracted executable hashes matched the
selected rows. `file` identified static ELF aarch64 and x86-64 respectively.
Both executables returned exit 0 for `--version` and `--show-config`:

| Evidence | Linux arm64 | Linux x86_64 |
| --- | --- | --- |
| Version / revision | `1.3.4`, `git f3b21c4 on branch HEAD` | Same |
| Compiler / build time | GCC 11.4.0; May 7 2026 15:32:17 | GCC 11.4.0; May 7 2026 15:35:15 |
| License banner | GPL version 3; linked CoCoALib, CLN, glpk-cut-log | Same |
| Configuration | `cocoa: yes`, `poly: yes`, `cln: yes`, `glpk: yes`, `gmp: no`, `assertions: no` | Same |
| F5 `x*x = 4`, model requested | Exit 0; `sat`, `((x #f3m5))` | Same |
| F5 `x*x = 2` | Exit 0; `unsat` | Same |

These are native ARM and successful x86 executable runs in an ARM-hosted worker,
**not native x86 runner qualification or approval of an emulation facility**.
The image operator must qualify each native image platform before its consumers
run. The decision supports those two target architectures; the present smoke
only establishes the execution environments actually exercised.

### Existing-version GPL versus a separate newer FF version

- **Selected: 1.3.4 GPL.** Hosted assets exist for both target platforms, exact
  bytes are verified, and the nonlinear SAT/model and UNSAT cases pass. This
  avoids a needless version divergence while keeping FF acquisition separate.
- **Not selected: installed 1.4.1 GPL/CoCoA.** Freshly observed at
  `/opt/cvc5-Linux-arm64-static-gpl/bin/cvc5`, revision `2b2e844`, executable
  SHA-256 `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`.
  Its `--version`, `--show-config` and the same two solving cases exit 0, with
  the same model and answers. This demonstrates an alternative solving version,
  not a reason to select it: no additional needed capability is established,
  and this decision does not pin its full two-platform archive/source set.
  Preinstallation is not approval to substitute it for `solve`.

SAT/UNSAT and model success establish only the exercised solving cases. They
establish neither proof-format support nor proof completeness. No proof format
is selected for M1, and no proof-production probe was run in this refresh.
FFM-09 owns broader solving protocol qualification; FFM-19 must not equate
printed proof-rule names with Lean-checked coverage. No axiom, `sorry`, `admit`
or widening of `blasterProven` is authorized.

## M2 proof-production bookmark: not an approved artifact

Retain the supplied candidate identity solely for a future M2 decision:

- Repository/release: [psaccomani15/cvc5, clean-wip](https://github.com/psaccomani15/cvc5/releases/tag/clean-wip).
- Executable version: `1.3.3.dev+clean_WIP@b1f8abb`.
- Reported source: [`b1f8abb80021d687df7547fedc41882c4416d981`](https://github.com/psaccomani15/cvc5/tree/b1f8abb80021d687df7547fedc41882c4416d981).
- Linux x86_64 archive URL: <https://github.com/psaccomani15/cvc5/releases/download/clean-wip/cvc5-Linux-x86_64-static.zip>.
- Archive SHA-256: `918361fcee2e1d3c64be5d20eb62156aaee73943df3ae7aa62d58f199b6785dc`.
- Executable member: `cvc5-Linux-x86_64-static/bin/cvc5`.
- Executable SHA-256: `514ccdaea9e4a5a0eb7d3be2e89b9d6fc893e3560d0f536cbe5e122ef6376a61`.

Inherited evidence reports the mutable release tag at
`f011843845a37ddeb555d04a8b07c68641810c52`, different from the tested executable's
source identifier. The pinned [lean-cvc5 lakefile](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean)
selects mutable `clean-wip` assets; that selection is not a reproducible identity.
These fork facts are supplied/inherited, not freshly executed or requalified here.

Do not download/stage this bookmark, create a `proof` manifest, adopt/fork/build
its source, or require its presence in M1 workers. M2 must separately approve
its distribution, platforms, source provenance and proof-format qualification.
The previous requirement that FFM-09 run “both selected profiles” is superseded:
**M1 has one selected profile (`solve`), with two platform artifacts, and no
selected proof-production profile.** Missing solving artifacts remain setup
failures; absent M2 proof artifacts are intentional, not skipped M1 tests.

## Initial acquisition and offline consumer contract

### Image-build acquisition, independent of FFM-09

Riley runs the following in a network-enabled **iog image build**, using a fresh
staging root. It uses release archives, not source checkouts, and does not invoke
a nonexistent protocol script. Both platform payloads are retained so the same
inventory can service both image architectures. These are operator instructions,
not an implementation of FFM-09 or FFM-10.

```sh
set -eu
ROOT="$PWD/.artifacts/finite-fields"
acquire() {
  platform=$1 name=$2 archive_sha=$3 executable_sha=$4
  d="$ROOT/solve/$platform"
  test ! -e "$d"
  mkdir -p "$d"
  curl --fail --location --proto '=https' --proto-redir '=https' \
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/$name.zip" \
    --output "$d/archive.zip"
  printf '%s  %s\n' "$archive_sha" "$d/archive.zip" | sha256sum --check --strict -
  unzip -q "$d/archive.zip" -d "$d/payload"
  exe="$d/payload/$name/bin/cvc5"
  printf '%s  %s\n' "$executable_sha" "$exe" | sha256sum --check --strict -
  test -x "$exe"
}
acquire linux-arm64 cvc5-Linux-arm64-static-gpl \
  92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889 \
  d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9
acquire linux-x86_64 cvc5-Linux-x86_64-static-gpl \
  3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5 \
  278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a
```

After the license/corresponding-source review, the image operator retains this
tree at `/opt/finite-fields`, including the archives and complete payloads
(license files included), this approved inventory and qualification evidence.
The operator records the built image digest and per-platform execution results;
no image build, redistribution review or publication is claimed by this ticket.

At every job startup, before offline checks, the image operator's entrypoint or
runner integration copies the tree into the checkout, failing on a stale target:

```sh
set -eu
test ! -e .artifacts/finite-fields
mkdir -p .artifacts
cp -a /opt/finite-fields .artifacts/finite-fields
```

Setup containing only `lake --version` is **not provisioning**. Neither an
installed PATH `cvc5` nor that setup command supplies the approved archives.
The first FFM-09 sandbox must receive these bytes and the decision inventory
from the image before it starts; it cannot bootstrap itself using the protocol
script or manifests it has yet to implement.

### Exact offline verification and solving smoke

Run from the checkout root after startup handoff. Hash checks cover both
artifacts; execution uses only the matching native platform. A mismatch, missing
file, unsupported host, wrong configuration or wrong solving result stops the
consumer. Never replace a failing hash with the downloaded hash or fall back to
PATH `cvc5`. Retain full version/config output and smoke results with exit codes.

```sh
set -eu
ROOT="$PWD/.artifacts/finite-fields"
printf '%s  %s\n' \
  92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889 \
  "$ROOT/solve/linux-arm64/archive.zip" \
  d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9 \
  "$ROOT/solve/linux-arm64/payload/cvc5-Linux-arm64-static-gpl/bin/cvc5" \
  3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5 \
  "$ROOT/solve/linux-x86_64/archive.zip" \
  278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a \
  "$ROOT/solve/linux-x86_64/payload/cvc5-Linux-x86_64-static-gpl/bin/cvc5" \
  | sha256sum --check --strict -
test "$(uname -s)" = Linux
case "$(uname -m)" in
  aarch64|arm64) arch=arm64 ;;
  x86_64) arch=x86_64 ;;
  *) echo 'Unsupported FF solving platform' >&2; exit 1 ;;
esac
d="$ROOT/solve/linux-$arch"
exe="$d/payload/cvc5-Linux-$arch-static-gpl/bin/cvc5"
test -x "$exe"
"$exe" --version > "$d/version.txt"
"$exe" --show-config > "$d/config.txt"
grep -F 'cvc5 1.3.4 [git f3b21c4 on branch HEAD]' "$d/version.txt"
grep -F 'GNU General Public License (GPL) version 3' "$d/version.txt"
grep -E '^cocoa[[:space:]]*:[[:space:]]*yes$' "$d/config.txt"
timeout 20 "$exe" --lang=smt2 > "$d/sat.txt" <<'SMT'
(set-logic QF_FF)
(set-option :produce-models true)
(declare-fun x () (_ FiniteField 5))
(assert (= (ff.mul x x) #f4m5))
(check-sat)
(get-value (x))
SMT
# Either square root is valid; do not pin a solver's incidental model choice.
test "$(cat "$d/sat.txt")" = "$(printf 'sat\n((x #f3m5))')" || \
  test "$(cat "$d/sat.txt")" = "$(printf 'sat\n((x #f2m5))')"
timeout 20 "$exe" --lang=smt2 > "$d/unsat.txt" <<'SMT'
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 5))
(assert (= (ff.mul x x) #f2m5))
(check-sat)
SMT
test "$(cat "$d/unsat.txt")" = unsat
```

F5 squares are 0, 1 and 4, so these cases have independently known answers.
The command block is a bootstrap verification recipe, not the broader protocol
implementation. It deliberately does not request proofs.

### Manifests, subsequent workers and CI

- FFM-09 creates `.artifacts/finite-fields/solve/<platform>/manifest.json`
  against the prestaged bytes. Artifact/evidence paths are relative to that
  manifest's containing profile/platform directory: `archive.zip`,
  `payload/<name>/bin/cvc5`, `version.txt`, `config.txt`, `sat.txt`, `unsat.txt`.
  No absolute sandbox paths, cross-profile `..` paths or PATH discovery.
- The manifest binds profile purpose, platform/execution requirements, this
  policy/owner decision, release/asset/source identities, both SHA-256 values,
  provenance status, version/config evidence, explicit arguments, image digest,
  license/build-recipe reference, separate recipe execution status, and solving
  qualification results. Proof qualification is `deferred to M2`, not `passed`.
  FFM-09 owns the schema. No manifest is created by this ticket.
- Later offline workers receive the same image tree plus owner-reviewed FFM-09
  manifests. They verify, never download or build missing inputs. Riley maintains
  inventory/manifests together; any byte change requires a reviewed new identity
  and requalification, not an in-place hash refresh.
- FFM-10 must use the approved image digest and startup handoff for its dedicated
  FF CI lane, then verify offline. Ordinary lanes retain their own acquisition
  and pins. CI implementation and filename authorization remain FFM-10 work.
- A separate network acquisition job or an operator-provided archive/executable
  pair is **not the selected route**. Switching routes requires an explicit
  owner decision with the same immutable hashes; offline workers must not assume
  either alternative is available.

## Source-build recipe requirement and execution status

| Field | Status |
| --- | --- |
| Selected distribution | Upstream hosted binaries; no externally supplied M1 build required. |
| Recipe availability | Requirement specified here; a complete reproducible owner recipe/dependency lock is not supplied by this decision. Riley retains it with distribution evidence. |
| Source-build execution | **Not run** on either platform. No source checkout or dependency build was performed. |
| Source-to-binary correspondence | Release tag plus matching reported short revision, not independently reproduced or attested. |
| Redistribution review | Required before public hosting or image redistribution; not performed here. |

For each approved build, the owner recipe must retain full source commit and
source archive hash, host/target triples, base OS/container digest, compiler,
linker and CMake versions, every dependency URL/hash and patch (especially
patched CoCoA), exact configure/build/test/package commands, license notices,
corresponding-source availability, output archive/executable hashes and logs.
Keep recipe availability distinct from execution status (`not run`, `failed`,
or `passed` with platform/date/logs). A future external rebuild needs its own
reviewed artifact row and executed qualification, not an assumption of identical
bytes.

The selected revision's [INSTALL.rst](https://github.com/cvc5/cvc5/blob/f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341/INSTALL.rst)
documents `--cocoa --gpl` and patched CoCoA via `--auto-download`. Starting points
for a separately authorized, verified source tree are
`./configure.sh --static --cocoa --gpl`, `make -C build`, and
`make -C build check`. These are **not a complete reproducible recipe**; the
owner must lock dependencies, flags, toolchain and packaging. Unchecked automatic
downloads do not satisfy that requirement. Source URLs here are references, not
permission to clone unlisted repositories or repair native dependencies.

## FFM-03 ticket report and job summary

Change: replace the stale proposed/blocked decision with Riley's explicit GPL,
ownership, platform and worker-image approvals; select the verified 1.3.4 GPL
solving pair; defer proof production and its fork to M2; replace two-profile
bootstrap commands with solving-only acquisition and offline verification.
This section is the ticket report/job summary retained in the repository change.
No manifests, protocol implementation, CI, Lean code, tests, protected files,
toolchain pins or ordinary solver lanes changed.

### Validation performed in this job

Fresh artifact research used temporary directory `ffm03-bpdj7pgy` under the
checkout, not the production consumer tree. For each `arch` in `arm64`, `x86_64`,
`name` was exactly `cvc5-Linux-$arch-static-gpl`. Commands were:

- `curl --fail --location --proto '=https' --proto-redir '=https' https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/$name.zip --output /workspace/lean-blaster/ffm03-bpdj7pgy/$name.zip`: both shell downloads exit 0. An initial Python-subprocess curl failed with exit 6 (DNS); the shell download succeeded. No pin changed.
- Python `hashlib.sha256(archive.read_bytes()).hexdigest()` and the same expression for each executable matched all four approved hashes.
- `unzip -q <archive> -d /workspace/lean-blaster/ffm03-bpdj7pgy/$arch`: both exit 0.
- `file <exe>`, `<exe> --version`, `<exe> --show-config`: both platforms exit 0; evidence recorded above.
- `timeout 20 <exe> --lang=smt2`, with each F5 case above supplied on stdin: all four solving runs exit 0, SAT/model or UNSAT as recorded. The SAT smoke enables models; the research UNSAT smoke also enabled models without requesting a value.
- `/usr/local/bin/cvc5 --version`, `/usr/local/bin/cvc5 --show-config`, and the same two stdin solving cases through `timeout 20 /usr/local/bin/cvc5 --lang=smt2`: all exit 0 for the unselected 1.4.1 comparison. Its executable SHA-256 was computed with the same Python expression.
- HTTPS reader: upstream release API, x86 asset API and upstream tag API matched the release/asset/hash/source identities above; pinned upstream `INSTALL.rst` confirmed the CoCoA/GPL recipe requirements.
- Repository search tool, regex `1\.3\.4|1\.2\.1|4\.15\.2`, `.github/workflows/ci-linux.yaml`: matches lines 16, 18, 19, 41, 138 and 139. Equivalent to the ticket's `rg -n` predicate; the workflow was not edited.

Repository checks used the exact prescribed commands from the checkout root:

| Exact command / scenario | Observed outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 4.15.2; 171 jobs, 90.31 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; same Z3 4.15.2; pure tier 200 jobs and Z3 tier 611 jobs, 171.62 seconds total. Lifecycle model-response warnings were emitted; no checks or expectations changed. |
| `git diff --check && test -s docs/finite-fields/m1-solver-distribution-decision.md` | Pass, exit 0. |
| `bash -n`, each of the three `sh` fenced blocks separately on stdin | Pass, all exit 0. |
| `bash -eu`, the exact offline verification block on stdin, working directory `ffm03-bpdj7pgy/bootstrap-smoke` with both verified archive/payload pairs copied under its `.artifacts/finite-fields` | Pass, exit 0; all four hashes OK, native ARM version/GPL/CoCoA checks pass, SAT/model and UNSAT match. This is a temporary recipe smoke, not image provisioning. |

Temporary research archives, extracted payloads and bootstrap-smoke tree were
removed after validation. Acquisition primitives were exercised as listed above;
the full image-build acquisition block and `/opt/finite-fields` startup copy
were syntax-checked, not executed as production provisioning. No default-solver
`lake test`, ordinary cvc5/floor/all-solvers lane or remote CI run is claimed.

### Remaining work and limits

Riley must complete the license/corresponding-source review, retain the full
source-build recipe evidence, build the image, record its digest and qualify
native platform execution before dependent live jobs. The distribution decision
is approved; these are operational handoff obligations, not unanswered policy
choices or a requirement to build the bookmarked fork. FFM-09 cannot claim live
validation without the approved solving artifacts prestaged through that route.
FFM-09/FFM-10 implementation and M2 proof qualification remain outside this ticket.
No image was built/published, no remote CI was run, and no native x86 runner,
proof format, Lean reconstruction or bit-for-bit source rebuild was qualified.
