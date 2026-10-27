# FFM-09: Ticket report and job summary

## Status: blocked before implementation

The approved solving artifacts were not provisioned in this sandbox. FFM-09 is
**incomplete**; no manifest, protocol scripts or fixtures have been created.
This report is the only project change. No protected file, PROJECT/setup
configuration, solver pin, test expectation or runtime handshake was changed.

The consumed [FFM-03 distribution decision](m1-solver-distribution-decision.md)
requires the initial artifacts to arrive through the iog worker image before
FFM-09 starts ("Initial acquisition and offline consumer contract"). It explicitly
rejects a worker-side acquisition job or operator archive pair as a substitute
without an owner decision. The [FFM-01 execution contract](m1-execution-decision.md)
requires stopping dependent implementation on missing worker prerequisites.
Downloading binaries from this worker would therefore bypass the approved route,
even if the download matched the approved hashes. No such download was attempted.

## Fresh observations

- Directory inspection of `/opt` found the installed
  `/opt/cvc5-Linux-arm64-static-gpl`, but no `/opt/finite-fields` image handoff.
- Checkout inspection and a hidden/ignored-inclusive glob found no
  `.artifacts/finite-fields` tree, protocol fixtures or `scripts/finite_fields`.
- A hidden/ignored-inclusive search for `archive.zip` beneath `/opt` and
  `/workspace`, and `cvc5*` beneath `/opt`, `/workspace`, `/tmp` and `/home/agent`,
  found only the installed cvc5 distribution; no selected 1.3.4 archive or
  executable was found.
- `/usr/local/bin/cvc5 --version` exited 0 and reported
  `cvc5 1.4.1 [git 2b2e844 on branch HEAD]`, with the GPLv3 and CoCoALib banner.
  This is the explicitly unselected version, not evidence for the pinned 1.3.4
  solving profile. No finite-field solving or model probe was run against it.

These are current observations, not reruns of FFM-03's historical artifact
qualification. FFM-03 states that its temporary downloaded artifacts were
removed; its successful historical results do not provision this job.

## Exact prerequisite to resume

Riley, as the approved image operator, must complete the FFM-03 image handoff:

1. In the explicitly network-enabled **image build**, execute the concrete
   `acquire` command block under FFM-03's "Image-build acquisition, independent
   of FFM-09". It downloads both approved 1.3.4 GPL release archives and verifies
   the archive and executable SHA-256 pairs before accepting the payloads.
2. Complete the required license/corresponding-source review before image
   redistribution, retain archives, complete payloads and decision inventory at
   `/opt/finite-fields`, and record the immutable image digest and native-platform
   qualification. The mutable image name alone is not that evidence.
3. Provision a fresh worker from that image and run the documented startup
   handoff before the offline job:

   ```sh
   set -eu
   test ! -e .artifacts/finite-fields
   mkdir -p .artifacts
   cp -a /opt/finite-fields .artifacts/finite-fields
   ```

Neither the image-build acquisition block nor this startup copy was executed in
this job: their required image tree is absent. No image build or publication is
claimed. Alternatively, the owner must explicitly amend the provisioning route;
this report does not grant that amendment.

The required payload inventory remains exactly FFM-03's:

| Platform | Archive SHA-256 | Executable SHA-256 |
| --- | --- | --- |
| Linux arm64 | `92fe9fba961a6e4808939a4ac4c97dead4a8a862a5bd5b40f0a316515d185889` | `d8fcf8886803b9cec6ff94906f20fb0499582c2ea8b5c86d9d617d2564421cb9` |
| Linux x86_64 | `3428c8b4f125f17ac9dbd901e1ebb33d002619e7b67d34143b2bf44e801b37c5` | `278058af5c6fc5ca42d79217b3b2096eb1f4ba9efd5b92345434f781a1d8773a` |

FFM-03's bootstrap layout is `solve/<platform>/archive.zip` and
`solve/<platform>/payload/cvc5-Linux-<arch>-static-gpl/bin/cvc5`. FFM-09's requested
public script interface is `--profile solving`, with the staged executable at
`ROOT/solving/bin/cvc5`. Once the prerequisite is satisfied, implementation must
explicitly accommodate this bootstrap-to-public-layout transition without
changing artifact identities or falling back to PATH discovery.

There is **no M1 proof-production profile**. The clean-wip executable is an M2
bookmark only; it was not downloaded, staged or probed. No `get-proof` command
was issued. The old two-profile provisioning note is superseded by FFM-03.

## Pinned reference review, not executable qualification

Read the following public commit-pinned files through HTTPS; no additional
repository was cloned and no source build or Lean package build was performed:

- [FF options at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/options/ff_options.toml):
  `ff-field-polys` defaults to false, with `gb` and `split` solver choices.
  Neither choice was exercised in this job; these fork defaults are not a live
  configuration attestation for the selected upstream binary.
- [SMT2 parser at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/parser/smt2/smt2_term_parser.cpp):
  the `FIELD_LITERAL` branch separates the value and modulus in `#fNmP` and
  constructs the corresponding field element. No canonical or typed-input
  model probe was rerun here.
- [INSTALL.rst at b1f8abb](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/INSTALL.rst):
  documents GCC/G++ >= 7 or Clang >= 5, CMake >= 3.16, Make or Ninja,
  Python >= 3.7 with pyparsing and tomli for Python < 3.11, GMP, CaDiCaL and
  SymFPU; finite-field support needs patched CoCoA with `--cocoa --gpl`.
  CLN, LibPoly and glpk-cut-log are optional build dependencies described there.
  This is reference guidance, not a locked recipe for the selected upstream
  release. FFM-03's reference commands `./configure.sh --static --cocoa --gpl`,
  `make -C build`, and `make -C build check` were **not run**. No automatic
  dependency downloads or source-build substitution were attempted.
- [Historical lean-cvc5 lakefile at 4733baf](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean):
  selects the mutable `clean-wip` assets. Reading it does not approve or
  qualify that M2 candidate.

## Validation and remaining acceptance work

The three requested Python validation commands were **not run**: their scripts,
manifest and staged selected binary do not exist. Zero M1 protocol cases were
executed; this is a blocker, never a passing offline validation. Manifest/schema,
negative-input rejection, acquisition safety, offline network isolation and
SAT/UNSAT/model acceptance remain unimplemented and unverified. Native x86,
`gb`/`split`, proof export and source-to-binary reproducibility have no new
qualification from this job.

Required repository checks were run exactly from the checkout root:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting Z3 4.15.2.

| Check | Outcome |
| --- | --- |
| `make check_blaster` | Pass; 171 jobs, 96.82 seconds. |
| `make check_tests` | Pass; pure tier 200 jobs, Z3 tier 611 jobs, 192.03 seconds total. |

The tests emitted lifecycle model-response warnings and an `Undetermined`
warning at `Tests/Smt/SmtNat/SmtNatMod.lean:41:56`; the check completed
successfully without edits to tests or expectations. No default-environment
`lake test`, cvc5/support-floor/all-solvers lane, or remote CI run is claimed.
These passing repository checks do not resolve the missing FFM-09 provisioning.

Local publication attempt:
`git add docs/finite-fields/ffm-09-ticket-report.md && git commit -m "Record FFM-09 provisioning prerequisite blocker"`
failed with exit 128 because Git author identity is not configured. No identity
was invented or configuration changed. This report remains a working-tree
deliverable for the stack's owner-attributed commit; no local commit or push is
claimed.
