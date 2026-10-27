# FFM-09: Ticket report and job summary

## Outcome

Implemented the amended **cvc5 1.4.1 GPL/CoCoA solving-only** distribution and
protocol contract. Both approved platform archives were acquired through the
new `--fetch-only` interface and their archive/executable hashes verified.
Native arm64 offline qualification passes all four required cases; all 34 local
negative fixtures pass. Both mandatory Z3 4.15.2 repository checks pass.

The preceding report's blocked status is **historical**. It correctly observed
that the earlier 1.3.4 image-handoff artifacts were absent and did not acquire
them without approval. Riley's 2026-10-27 amendment now authorizes this job's
worker-side acquisition of the specified 1.4.1 release assets, superseding that
handoff and the earlier version selection. No PROJECT or image change/digest is
needed. FFM-03's GPL policy, ownership and approved platforms remain unchanged.
The parent [execution](m1-execution-decision.md) and
[distribution](m1-solver-distribution-decision.md) decisions were consumed; no
historical qualification is represented as a current rerun.

## Changes

- `docs/finite-fields/solver-manifest.json`: release/source/asset identities,
  both SHA-256 pairs, stable staging paths, expected version/configuration,
  production argv, resource bounds and independent capability requirements and
  per-platform observations. Only `solving` is selected; proof export is
  explicitly deferred to M2.
- New `scripts/finite_fields/check_manifest.py`: stdlib schema/fixture validation,
  immutable identity requirements, production handshake and model obligations,
  safe local references and nonempty required cases.
- New `scripts/finite_fields/probe_solver.py`: separate acquisition/offline/local
  negative modes, safe bounded ZIP extraction, atomic publication after hash
  verification, host/profile/configuration checks, bounded execution and complete
  evidence retention. Later approved profiles and cases are manifest data; no
  fixed profile-name dispatch or PATH solver fallback.
- `fixtures/finite-fields/protocol/`: four complete canonical/typed SMT2 inputs,
  34 invalid-input fixtures and a full successful native-arm64 transcript in
  `observed-linux-arm64.json` (inputs, stdout, stderr, argv/shell commands and
  exit/resource statuses).
- [solver-protocol.md](solver-protocol.md): amendment, initial staging commands
  and outcomes, stable consumer interface, fresh versus historical evidence,
  pinned reference-file identities, source-build guidance and execution limits.
- `.gitignore`: excludes local `.artifacts/` binaries/evidence and the new Python
  modules' bytecode cache.

Only new files were added under `scripts/finite_fields`; the existing scripts,
Tests, workflows, Lake files and Lean toolchain were not edited. No solver
runtime/handshake, expected test outcome, axiom or `blasterProven` changed. No
additional repository was cloned. No proof candidate was acquired, staged or
probed, and no M1 input issued `get-proof`.

## Exact acquisition and validation commands

All shell commands below ran from the repository root on 2026-10-27.

### Manifest and acquisition

```sh
python3 scripts/finite_fields/check_manifest.py docs/finite-fields/solver-manifest.json
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --fetch-only
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields-x86_64 --profile solving --platform linux-x86_64 --fetch-only
sha256sum /opt/cvc5-Linux-arm64-static-gpl/bin/cvc5
```

| Check | Outcome |
| --- | --- |
| Manifest | Exit 0; one selected profile, both platform identities and all case/evidence references validate. |
| arm64 acquisition | Exit 0, 5.79 seconds; approved archive hash `e6cac10f…9a1e7c` and executable hash `b0dd6483…7d86` verified before publication at `.artifacts/finite-fields/solving`. |
| x86_64 acquisition | Exit 0, 5.90 seconds; approved archive hash `d0b54324…16666` and executable hash `b265759b…e59f` verified before publication at `.artifacts/finite-fields-x86_64/solving`. No x86_64 executable run. |
| Installed arm64 cross-check | Exit 0; full SHA-256 `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`, identical to the selected executable. Not used instead of archive acquisition. |

The manifest/protocol retain the full identities, not these abbreviated table
values. Acquisition correctly reports `qualified: false`: downloaded bytes are
not a claim of solving/model qualification. Both complete archives and their
payloads remain in the ignored artifact roots for offline consumers.

### Offline and negative acceptance

```sh
python3 scripts/finite_fields/check_manifest.py docs/finite-fields/solver-manifest.json
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --offline --check
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --negative-fixtures
```

All three final acceptance commands exited 0:

- Archive, payload executable, staged executable and bound metadata validated
  locally before execution. Version 1.4.1 / revision 2b2e844 and required
  configuration including `cocoa: yes` passed independently.
- Every fixture used `--lang smt2 --incremental --parsing-mode=lenient
  --dt-nested-rec` and the full production setup, including accepting
  `produce-proofs` without asking for a proof. Every `ff-field-polys` query was
  false and every `ff-solver` query was gb.
- F7 `x*y=0`, `x!=0`, `y!=0`: UNSAT. F3 `x*x+1=0`: UNSAT.
- Canonical and typed F7 `x+1=0`: SAT and `((x #f6m7))`, validated as residue
  6 at modulus 7. All four case processes exited 0 with empty stderr.
- All 34 negative fixtures rejected their intended invalid inputs with the
  required category, including checksum/schema/profile/platform mismatches,
  `cocoa:no`, missing models, wrong residue/modulus, malformed/truncated/oversized
  responses and SMT errors despite exit 0, unsafe ZIP paths and zero cases.
  Negative mode invokes no solver and requires no staged installation.

The first offline attempt stopped before solving because the initial version
validator required the incidental word `version`. Actual pinned output is
`cvc5 1.4.1 [git 2b2e844 on branch HEAD]`. The validator was corrected to accept
both banner forms while retaining exact version/revision checks. Wrong-version
and wrong-revision fixtures remain rejected. Both subsequent live runs passed;
no artifact identity, runtime handshake or expected solving result was relaxed.

Complete committed evidence:
[observed-linux-arm64.json](../../fixtures/finite-fields/protocol/observed-linux-arm64.json),
from successful run `run-20261027T192546Z-8d758a78d28e4a0d8fa5ba67d1a1667f`.
The final acceptance rerun is retained locally as
`run-20261027T192825Z-dbe77128d6f64237b7ad9e3b99edd062` under the same profile's
`evidence/`. Initial failed evidence is retained separately, not overwritten.

### Expected-failure boundary checks

```sh
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields-x86_64 --profile solving --offline --check
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/absent-ffm09 --profile solving --offline --check
```

Both returned the intended exit 1: respectively `platform: staged metadata does
not match the host platform` and a missing `metadata.json` artifact. Neither
started a solver or attempted acquisition.

Additional inline Python smoke checks exercised the real exported helpers (not
replacement validators), with temporary directories removed afterward:

| Scenario / exact helper input | Outcome |
| --- | --- |
| `validate_response` on the F7 model case with `#f6m7`, `(as ff6 (_ FiniteField 7))`, and `#f-1m7`, including added whitespace/comments | All accepted as residue 6 modulo 7. |
| `validate_version` on the actual banner and a synthetic exact `1.3.3.dev+clean_WIP@b1f8abb` version token | Both token forms accepted with their matching revisions; no candidate binary was used. |
| `validate_data` after adding a copied `another-approved-solving-profile` entry | Passed without script edits; this was schema-only, not artifact selection/staging. |
| `prohibit_network()` followed by `socket.socket()` and `socket.getaddrinfo('github.com', 443)` | Both rejected with `network:` before a request. |
| `run_process(['/usr/bin/python3', '-c', 'import time; time.sleep(5)'], ...)`, wall/CPU limit 1 second | Timeout rejected, child killed, nonzero exit/status retained. |
| `run_process(['/usr/bin/python3', '-c', 'import os; os.write(1, b"x" * 4096)'], ...)`, output bound 128 bytes | Oversized output rejected; exactly the bounded prefix and truncation status retained. |
| `offline_check` on a temporary inventory with valid archive/payload/metadata but a replaced executable | `checksum:` rejection before creating execution evidence or running the replacement. |

Reference-source acquisition used the four exact commit-pinned `curl` commands
and SHA-256 inventory recorded in [solver-protocol.md](solver-protocol.md).
All shell acquisitions exited 0 before offline validation. An earlier urllib
attempt in the evaluation subprocess failed DNS; no alternate source or pin
was substituted. The source-build recipe and historical Lean package were read,
not built. A later tool-write attempt in the same evaluation process was also
blocked by the installed offline network hook; the tool write was performed
from a separate process, outside solver validation.

### Required repository checks

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.

| Check | Outcome |
| --- | --- |
| `make check_blaster` | Exit 0; 171 jobs; 89.73 seconds. |
| `make check_tests` | Exit 0; pure tier 200 jobs and Z3 tier 611 jobs; 176.58 seconds total. |

Lifecycle diagnostic warnings were emitted by the existing tests; no warnings
or expectations were suppressed. `Tests/Smt/SmtNat/SmtNatMod.lean:41:56`
reported Valid in this run. No default-environment `lake test` was run.

## Limitations and handoff

- Native **Linux arm64 / gb** only is live-qualified. The approved Linux x86_64
  archive/executable hashes are verified, but native configuration, setup,
  solving and model checks are explicitly `not run`. A native x86_64 consumer
  must run the same offline interface; this arm64 worker rejects that mismatch.
- `split` was not rerun. Small solving probes do not establish general solving
  completeness, performance, rule coverage, proof export or verified closure.
- Proof production is deferred to M2. No proof artifact is missing from M1:
  none is selected or required. Accepting `produce-proofs` is not FF proof
  evidence; unsat cores are diagnostic only.
- The reference source-build commands were not executed on either platform;
  no bit-reproducible source-build claim, dependency repair, image publication
  or redistribution/source-availability review is made.
- The offline guard prohibits Python networking; it is not an OS-level network
  sandbox for subprocesses. Only verified solver bytes are executed. CI may
  additionally disable network access at the worker boundary.
- FFM-10 owns Lake/CI integration; ordinary cvc5/floor/all-solvers lanes and
  remote CI were not run here. The maintainer's later ordinary cvc5 pin update
  remains outside this ticket.

## Job summary

Delivered the amended pinned solving manifest, reusable acquisition/offline
interfaces, positive/negative protocol fixtures, complete native-arm64 evidence
and reproducible provisioning/source-reference documentation. Both approved
archive pairs are staged locally; all three requested Python validations and
both exact PROJECT checks pass. Remaining qualification is explicitly limited
to native x86_64, split, M2 proof work and the separate FFM-10 integration scope.
This report is a repository deliverable for the stack's owner-attributed commit;
no local push, remote CI execution or maintainer signoff is claimed.
