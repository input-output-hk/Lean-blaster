# Shared SMT emission benchmark

Build Blaster, then compare exactly the same executable with sharing disabled and enabled:

```sh
lake build Blaster
python3 Benchmarks/shared_emission.py --depths 16 20 --repeat 3
python3 Benchmarks/shared_emission.py --depths 24 --repeat 1 --skip-dump --output Benchmarks/shared-emission-depth24.json
```

`SharedEmission.lean` generates an Int let-chain whose shared expression graph grows linearly while its expanded text doubles at every level. Each sample starts a fresh Lean process and must return `Valid`. Dump-only runs are separate from timing. Negative cases and binder-scope cases live in `Tests/FixedIssues/Issue231.lean` and `Issue232.lean`.

Recorded environment: Apple M2 Max, Lean 4.24.0, Z3 4.15.4. These measurements compare the candidate built on `4ae4d4fe` with its sharing option off/on. The JSON records individual samples, stage times and medians.

| Depth | Off, wall time | On, wall time | Off, dumped query | On, dumped query |
|---|---:|---:|---:|---:|
| 16 | 1.83 s | 1.29 s | 459,121 bytes | 811 bytes |
| 20 | 9.78 s | 1.31 s | 7,340,401 bytes | 931 bytes |
| 24 | 132.69 s | 1.28 s | Not measured | Not measured |

Depths 16 and 20 use medians of three samples. Depth 24 is a single-run comparison. At depth 20, median submission time falls from 8.417 s to 0.002 s; solver time stays around 0.03 s. At depth 24, submission falls from 131.462 s to 0.002 s. These cases isolate serialization rather than solver search.

The first depth-24 dump-only run exceeded its 180-second limit. Its earlier uncheckpointed timing samples were lost and are excluded. The recorded depth-24 run was repeated with dumping disabled; no byte count or three-run median is claimed for that depth. The runner now checkpoints completed samples and terminates its process group on timeout.

This synthetic result does not measure Cardano validator preparation or establish a general 104× speedup. It demonstrates that repeated SMT text is avoidable for a shared residual expression. The full test suite was separately checked with Z3 4.15.2 and a uniform 30-second process cap.
