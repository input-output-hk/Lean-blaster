# Certified recursive searches: SellNFT measurements

The opt-in legacy adapter reduces SellNFT preparation from a median **22.874 s
to 18.348 s** (19.8%) across three serial, alternating pairs. It replaces two
recognized recursive searches with kernel-verified Lean workers. This does not
reach the sub-10-second target. Governance has no supported template yet.

## Clean packaged comparison

These measurements use the actual installed adapter, with fully symbolic
SellNFT inputs and the original fuel 1800. Each pair ran reference preparation,
reference proofs, candidate preparation, candidate proofs. Dependencies were
built before timing; no other owned build or benchmark ran concurrently.
CPU sampling and normalization profiling were disabled. The reference uses
the fused CEK and static-control annotations; the candidate enables
`--lifted-search` and its worker annotations in the same workspace.

| Pair | Reference optimize (s) | Candidate optimize (s) | Reference prep + proofs wall (s) | Candidate prep + proofs wall (s) |
| --- | ---: | ---: | ---: | ---: |
| 1 | 22.534 | 18.245 | 63.604 | 57.483 |
| 2 | 22.958 | 18.348 | 64.216 | 57.502 |
| 3 | 22.874 | 18.473 | 64.294 | 57.593 |
| Median | **22.874** | **18.348** | **64.216** | **57.502** |

The total wall-time reduction is 10.5%. The proof phase includes one existing
30-second solver timeout in both arms; these totals are time to the observed
verdicts, **not time to complete all proofs successfully**. The verdict sequence
in every arm was:

1. `Valid` for the first two positive properties.
2. The existing timeout for `success_imp_no_multi_spent`.
3. `Expected Falsified` for both remaining negative controls, including the
   accepting/non-vacuity control.

The proof-only command deliberately exits with status `error` because of that
timeout. It is retained in the result JSON and not reclassified as a pass.

| Median or invariant metric | Reference | Candidate |
| --- | ---: | ---: |
| Preparation module wall time (s) | 25.438 | 20.450 |
| Proof module wall time (s) | 38.777 | 37.052 |
| Final hash-cons entries | 8,271,491 | 5,510,804 |
| Allocated context IDs | 29,063 | 29,234 |
| Beta-cache entries | 35,479 | 23,802 |
| Preparation sampled peak process-tree RSS (GiB) | 2.203 | 2.033 |
| Prepared module size (bytes) | 826,280 | 818,288 |

Final hash-cons entries fall by 33.4%; sampled preparation RSS falls by 7.7%.
These are final cache counts and sampled process-tree memory, not a count of
CEK transitions or an operating-system memory high-water mark.

The machine is an Apple M2 Max, 12 logical CPUs, 64 GiB RAM, macOS 25.5.0.
Lean is 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`). Z3 is 4.15.2,
with a wrapper passing `-T:30`. Native `lake build` is used for every measured
module. Setup, dependency compilation, and proof of the optimization itself
are excluded from preparation timing.

The measured Blaster commit is
`71dfe27f3b0b05fa0a7d095a46f1ba0b9a67dcc2`, based on the dependent-matcher fix
in [PR #246](https://github.com/input-output-hk/Lean-blaster/pull/246).
Every `release-pair*.json` records all five repository pins, tracked-patch
hashes, generated-source hash, runner hash, flags, raw times, and verdicts.
Log paths are reduced to basenames; corresponding `*.excerpt.txt` files are
explicitly selected telemetry/verdict excerpts. Full logs remain in the local
benchmark workspace. Later documentation commits do not change tested code.

## Correctness and installation

The [adapter guide](../../overlays/lifted-search/README.md) explains installation,
the exact fuel costs, and the scope of recognition. The packaged installer was
run against fresh checkouts of the pins. Its 13 added Lean modules, preparation
patch, and fixtures were built successfully using native Lake (371 jobs),
including 37 `#testOptimize` controls and two certificates that the literal
templates occur in the decoded production SellNFT script.

[`validation.log`](validation.log) contains the build and axiom output.
`LoopCek.run_eq_runSteps` and `LoopCek.execute_eq` use only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`; neither depends on
`sorryAx`, `native_decide`, or `blasterProven`. Both production-template
certificates have no axioms. The pinned reference CEK contains an unrelated
pre-existing `sorry` warning; it is absent from these theorems' dependencies.
Blaster's property verdicts retain its existing solver trust boundary.

The core Blaster fix is separate: issue #245 was filed before PR #246, with
five passing `Issue245.lean` regression checks. The final serial native Blaster
suite on that base passed all 729 jobs. No core optimizer change is added by
this adapter.

## Governance and rejected prototypes

A prior, separate scouting comparison at the original Governance fuel 9000
measured 23.079 s without the worker dispatch and 24.543 s with it. Both had
all four existing proof checks `Valid` (proof wall time 4.445 s and 4.411 s).
Its full metadata is archived in `lifted-*-governance-9000*.json`. This is
**one scout per arm in the experimental workspace**, not part of the three
clean SellNFT pairs and not evidence of a Governance speedup. Keep the flag
disabled for Governance until a matching worker is implemented and measured.

Earlier integration variants were rejected: an indexed certificate on the
runtime path took 26.259 s on SellNFT and caused an additional negative-control
timeout; the unindexed single-search version took 22.590 s but retained that
extra timeout. The two-search version measured here restores the reference
outcomes. Earlier timing sets are not pooled into the clean comparison.

The current recognizers support two exact named-variable templates (integer
and map payload searches for an empty byte-string key). They check complete
bodies and captured bindings, not just binder names. This is not a general
Y/Z-combinator compiler and does not target the indexed CEK in PlutusCore
PR #44. The remaining SellNFT predicate search and Governance's Z/mutual
recursion are the next candidates for the same certificate interface.

Open Lean-blaster and PlutusCoreBlaster PRs were checked before publication.
PlutusCore PR #42 has related CEK composition lemmas and PR #44 has the indexed
fused interpreter; neither supplies these certified legacy recursive workers.
