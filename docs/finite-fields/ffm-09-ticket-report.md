# FFM-09: Solver artifact/protocol prerequisite report

## Status: blocked before implementation

The supplied sandbox does not contain the approved cvc5 1.3.4 solving
artifacts. FFM-09 is **not complete**. No solver manifest, protocol scripts or
fixtures were created, and no live finite-field protocol case was executed.
This report records the prerequisite failure rather than committing protected
scripts that cannot receive their required first-job live validation.

The consumed [FFM-03 decision](m1-solver-distribution-decision.md), sections
“Initial acquisition and offline consumer contract” and “Remaining work and
limits”, requires the first FFM-09 sandbox to receive the approved archives and
payloads from the iog image before implementation. It explicitly excludes a
worker acquisition job or operator-provided pair as a substitute route without
an owner decision. The [FFM-01 contract](m1-execution-decision.md) requires a stop
on missing prerequisites. Network access to reference documents is not image
provisioning authorization.

The ticket's old “both selected profiles” note is superseded by FFM-03: M1 has
only solving. The proof-production profile is deferred to M2. No bookmarked
fork executable was downloaded, staged or run; no `get-proof` command was sent.

## Observed prerequisite evidence (2026-10-27)

- Both consumed decision documents are present and were read.
- Directory inspection of `/opt` found the installed
  `/opt/cvc5-Linux-arm64-static-gpl` tree, but no `/opt/finite-fields` handoff.
- File discovery found no `.artifacts/finite-fields` tree in the checkout, no
  cvc5 ZIP or `archive.zip` under `/workspace`, and no cvc5 ZIP under `/tmp`.
  Searches for finite-fields handoff directories under `/tmp`, `/home/agent`
  and `/cache` also found none. No alternative handoff location was supplied.
- `test -d /opt/finite-fields && test -d .artifacts/finite-fields` exited 1.
  Neither required directory was found by directory/file discovery.
- The following command exited 0:

  ```sh
  cvc5 --version && cvc5 --show-config && readlink -f /usr/local/bin/cvc5 && sha256sum /usr/local/bin/cvc5
  ```

  It reported cvc5 `1.4.1`, revision `2b2e844`, `cocoa: yes`, and executable
  `/opt/cvc5-Linux-arm64-static-gpl/bin/cvc5`, with SHA-256
  `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`.
  This is the **unselected** alternative recorded in FFM-03, not the approved
  1.3.4 executable. Its version/configuration output does not establish any
  FFM-09 solving, model or proof capability.
- The consumed decision supplies no built image digest; no new immutable image
  identity was provided with this job. `agentstack-worker-iog:latest` alone
  cannot establish one.

These observations are from this job. FFM-03's earlier archive downloads,
F5 solving results and x86 execution are historical evidence only. Its report
explicitly says its temporary archives were removed and no production image
was built or published. None of those results is counted as an FFM-09 rerun.

## Required owner/image handoff

Riley, as the distribution owner and image operator named in FFM-03, must
complete the license/corresponding-source review and provide the approved
image tree and immutable image digest. Qualify the native platform used by
each consumer; this job does not qualify native x86 execution.

The concrete first-job acquisition commands below are preserved from FFM-03.
They belong in an explicitly network-enabled **image build**, not this offline
consumer job. **Execution status in this job: not run.** No source build or
unapproved artifact substitution was attempted.

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

Retain the verified tree, full payloads/licenses, decision inventory and image
qualification evidence at `/opt/finite-fields` in that image, as FFM-03
requires. The startup handoff, also **not run** because its source is absent:

```sh
set -eu
test ! -e .artifacts/finite-fields
mkdir -p .artifacts
cp -a /opt/finite-fields .artifacts/finite-fields
```

The initial FFM-03 tree uses `solve/<platform>`. FFM-09's requested public
interface is `--profile solving` with `ROOT/solving/bin/cvc5`. These are distinct
layouts; no existing tree or nonexistent interface is claimed to satisfy the
other. After provisioning, FFM-09 must verify the initial bytes and implement
the documented profile layout, provenance retention and reusable interfaces.
The image handoff for subsequent consumers must retain that validated layout.

If image provisioning cannot be supplied, an explicit scoped owner amendment
would be required to authorize another acquisition route. This report does not
make that decision or download artifacts on its behalf.

## Reference review and source-build limits

The following commit-pinned public files were read through HTTPS in this job;
no additional repository was cloned:

- [FF options at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/options/ff_options.toml):
  `ff-field-polys` defaults to false; the GB default and split choice are source
  declarations, not exercised configurations in this job.
- [SMT2 parser at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/parser/smt2/smt2_term_parser.cpp):
  the `FIELD_LITERAL` branch splits canonical `#fNmP` into value and modulus.
  Neither canonical nor typed finite-field input was rerun here.
- [INSTALL.rst at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/INSTALL.rst):
  the build/dependency sections describe GCC >= 7 or Clang >= 5, CMake >= 3.16,
  Make or Ninja, Python >= 3.7 with pyparsing and tomli on Python < 3.11,
  GMP 6.3, CaDiCaL >= 2.1.0 and SymFPU. CoCoA requires a patched dependency
  and `--cocoa --gpl`; optional CLN, LibPoly and glpk-cut-log are separate
  configuration choices. These are reference guidance, not a locked dependency
  inventory or evidence that the selected upstream release was rebuilt.
- [Historical lean-cvc5 lakefile at 4733baf](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean):
  selects mutable `clean-wip` assets. Its package was not built or acquired.

FFM-03 records selected upstream source commit
`f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341`. Its reference recipe starts with
`./configure.sh --static --cocoa --gpl`, `make -C build`, and
`make -C build check` in a separately approved source tree. **Source-build
execution status: not run.** No build is authorized here. A reproducible recipe
still requires the owner-held source/dependency hashes, patches, compiler and
linker versions, base image digest, configuration and packaging inventory.
Unchecked `--auto-download` is not a substitute for those locks. The fork's
reference dependency guidance does not attest the upstream binary's origin.

## Ticket report and job summary

Change: add only this prerequisite/evidence report. No existing scripts, tests,
CI, PROJECT/setup configuration, toolchain, runtime handshake or solver pins
were changed. No manifest or incomplete script scaffold was committed.

The requested manifest, offline live-probe and negative-fixture commands were
**not run**: their implementation is blocked by the explicit first-job
provisioning prerequisite. Zero protocol cases executed is not a pass. No
F7 residue-6 model validation, F3/F7 UNSAT qualification, malformed-response
rejection, acquisition safety or offline network isolation is claimed.

FFM-09 remains incomplete. Resume it in a sandbox with the approved image
handoff and immutable image identity, then implement and execute all requested
interfaces and cases before downstream consumers rely on the protected scripts.

### Repository and documentation validation

Executed from the repository root, exactly as required:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

- Build: pass, exit 0; 171 jobs, 92.54 seconds.
- Tests: pass, exit 0; pure tier 200 jobs, Z3 tier 611 jobs, 182.87 seconds.
  Lifecycle model-response warnings and an `Undetermined` warning at
  `Tests/Smt/SmtNat/SmtNatMod.lean:41:56` were emitted. No expectations or
  checks were changed.
- Both commands selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version
  4.15.2. No default-environment `lake test` was run. These passes do not
  validate finite-field provisioning or the unimplemented FFM-09 protocol.
- `bash -n` on stdin for each preserved bootstrap/handoff block: both exit 0.
  Python equality checks confirmed both blocks are byte-identical to the
  corresponding FFM-03 blocks. This is syntax/preservation evidence only;
  neither acquisition nor startup handoff was executed.

The three ticket-specific validation commands below remain **not run**, for
the provisioning/implementation reason above:

```sh
python3 scripts/finite_fields/check_manifest.py docs/finite-fields/solver-manifest.json
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --offline --check
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --negative-fixtures
```
