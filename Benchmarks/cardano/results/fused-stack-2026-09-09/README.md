# Fused optimizer stack: paired Cardano measurements

Storing each continuation frame and its tail in one constructor reduces median optimizer time by **3.3% for SellNFT** and **4.2% for Governance** in three serial pairs. This is a modest generic allocation improvement; neither script reaches the sub-10-second preparation target.

The measured candidate is `da7a50e1`, based on PR #247 (`40786b22`, whose code matches reference `71dfe27f`). The only runtime change is the optimizer stack representation. Every rewrite action, continuation payload, and evaluation order is preserved. Known frame construction inlines to one stack constructor, and the generated C return path reads the payload and tail directly instead of reading a separate list cell and frame. Rewrites that return a standalone `OptimizeFrame` retain that intermediate value until it is pushed.

## Measurements

All inputs are symbolic. Fuel is 1800 for SellNFT and 9000 for Governance. Both arms use the fused CEK and static-control annotations. SellNFT enables the two certified search workers in both arms; Governance leaves them disabled. Dependencies were built before measurement. Profiling was off, and no other owned build or benchmark ran concurrently.

Each arm runs preparation followed immediately by its proof module. Pair 1 is labeled `scout`; pairs 2 and 3 confirm the same unchanged candidate. Arm order is reference/candidate, candidate/reference, reference/candidate. The results come from the existing M2 Max machine with Lean 4.24.0 and Z3 4.15.2 (`-T:30`). Raw metadata records all repository pins, tracked patch hashes, generated-source and runner hashes, memory samples, verdicts, and timings.

| Contract | Pair | Reference optimizer (s) | Candidate optimizer (s) | Reference prep + proofs wall (s) | Candidate prep + proofs wall (s) |
| --- | --- | ---: | ---: | ---: | ---: |
| sellnft | 1 | 17.924 | 17.637 | 56.852 | 57.231 |
| sellnft | 2 | 18.236 | 16.928 | 57.506 | 55.804 |
| sellnft | 3 | 18.356 | 17.906 | 57.539 | 57.037 |
| sellnft | **Median** | **18.236** | **17.637** | **57.506** | **57.037** |
| governance | 1 | 20.947 | 20.066 | 27.694 | 26.566 |
| governance | 2 | 20.835 | 20.130 | 27.158 | 26.538 |
| governance | 3 | 21.066 | 20.067 | 27.719 | 26.612 |
| governance | **Median** | **20.947** | **20.067** | **27.694** | **26.566** |

| Median wall metric | SellNFT reference | SellNFT candidate | Governance reference | Governance candidate |
| --- | ---: | ---: | ---: | ---: |
| Preparation module (s) | 20.458 | 19.941 | 23.267 | 22.136 |
| Proof module (s) | 37.016 | 37.082 | 4.429 | 4.429 |

Whole preparation improves by 2.5% for SellNFT and 4.9% for Governance. Median paired preparation-plus-proof wall time improves by 0.8% and 4.1%. SellNFT pair 1 has a small total-wall regression; this is not a claim that every run or proof phase is faster.

Every SellNFT arm preserves two `Valid` properties, the existing timeout in `success_imp_no_multi_spent`, and two `Expected Falsified` controls, including acceptance/non-vacuity. The proof module therefore exits with an error in both arms. Its approximately 37-second wall time includes the 30-second timeout and is not time to successful completion of all proofs. Every Governance arm preserves its four `Valid` checks.

Final hash-cons entries, context IDs, beta-cache entries, and prepared module sizes are identical within each contract. SellNFT has 5,510,804 entries, 29,234 contexts, 23,802 beta entries, and an 818,288-byte prepared module; Governance has 5,070,520 entries, 17,761 contexts, 17,985 beta entries, and a 2,216,312-byte module. The representation change reduces transient stack work, not the number of normalized expressions. No memory reduction is claimed.

## Validation and scope

The native full Blaster suite passed all 732 jobs. The new `StackRepresentation.lean` theorems prove round-trip conversion for every frame payload and arbitrary stack depth, using only `propext`. These are representation proofs, not a new formal proof of the whole optimizer. Existing tests exercise the actual optimizer, including Issue245 and scoped cache regressions. The Cardano dependency/control build passed 371 jobs, including all 37 recursive-search controls and production-template certificates.

The packaged installer recreated a source-only workspace from the measured commit. All tracked files in all five repositories and six generated control/source-certificate fixtures were byte-identical to the built benchmark workspace. This source-only check did not itself rebuild dependencies; the measured workspace's native build is the execution evidence. Selected validation output is in `validation.log`. Log excerpts are explicitly labeled; full logs remain local.

PR #160 was inspected for overlap: its ancestor-cache/context changes retain `List OptimizeStack` and do not provide this representation. This PR is an optimization, not a newly discovered bug fix. Existing issue regressions remain intact.

Reproduce with `prepare_local.py --staged-cek --lifted-search --blaster-rev da7a50e1` using the local source repositories described in the benchmark guide. Run preparation and proof phases serially with matching flags. Enable `--lifted-search` for SellNFT only. No stack-specific runtime flag is needed.
