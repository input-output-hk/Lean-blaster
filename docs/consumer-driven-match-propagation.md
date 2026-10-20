# Experiment: defer matches in constructor fields

This branch targets `beta-lambda-cache-optimization`. It tests one small part of a
consumer-driven reduction strategy: avoid turning `Ctor (match x with ...) rest`
into `match x with ... => Ctor ... rest` before a consumer asks for the field.
The existing rewrite is useful in some situations, but repeated independent
fields can multiply the number of optimizer contexts.

`(preserve-constructor-choices: 1)` skips the constructor arm of
`funPropagation?`. It leaves propagation for non-constructor functions and the
rest of the optimizer unchanged. The default is `0`, so existing normal forms
and tests retain their behavior. This is an experiment, not yet a complete
consumer-driven evaluator.

The example in `Tests/Benchmarks/ConsumerDrivenMatchBench.lean` builds a list-like
`Data` value with `n` independent `Option Nat` fields. Each field has two
encoding branches. Reproduce both modes with:

```sh
lake build Blaster
lake env lean Tests/Benchmarks/ConsumerDrivenMatchBench.lean
lake env lean Tests/Benchmarks/ConsumerDrivenMatchBehavior.lean
lake env lean Tests/Benchmarks/ConsumerDrivenMatchProof.lean
```

`Tests/Benchmarks/SymbolicEncoderBlowup.lean` shows the factored and
distributed forms for two fields, proves them equal by cases, and prints
parent/child context IDs via `trace.Optimize.context` for two and four fields.

One run on an Apple Silicon Mac, in nanoseconds (times include optimizer work;
they are not a controlled performance study):

| Fields | Current contexts | Deferred contexts | Current time | Deferred time |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 31 | 27 | 0.17 s | 0.11 s |
| 4 | 75 | 31 | 0.19 s | 0.11 s |
| 6 | 263 | 35 | 0.64 s | 0.12 s |
| 8 | 1,027 | 39 | 5.01 s | 0.14 s |
| 10 | 4,095 | 43 | 61.04 s | 0.15 s |

The stable observation is the context count: the current rule grows roughly
exponentially for this constructor-building expression, whereas the opt-in mode
grows linearly. The time figures are illustrative single runs. The benchmark
does not establish an end-to-end speedup for every consumer of the data.

For a cross-repository check, we ran the actual
`CardanoLedgerApi.IsData.Class.optionToData` encoder from
`CardanoLedgerApiBlaster` PR 14, building a `Data` constructor from 2–8
independent `Option Integer` inputs. With PR 14's `markAsRecursive optionToData`
workaround present, both modes produced 25 contexts at each size: that
workaround already prevents the blow-up in this case. In an isolated checkout
with *only that workaround removed*, the measurements were:

| Fields | Current contexts | Deferred contexts | Current time | Deferred time |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 31 | 27 | 0.15 s | 0.10 s |
| 4 | 75 | 31 | 0.23 s | 0.11 s |
| 6 | 263 | 35 | 0.90 s | 0.13 s |
| 8 | 1,027 | 39 | 6.82 s | 0.13 s |

This suggests that deferred constructor propagation could replace this
*particular* workaround, after downstream proof/translation tests pass. The
Cardano edit is not part of this branch.

There is an important remaining problem. A shallow consumer such as
`first (.pair x rest) = x` reduces the opt-in example to a match on `x` alone;
`ConsumerDrivenMatchProof.lean` also checks the resulting equality with
`#blaster`. But a nested consumer such as
`firstLeaf (.pair (.leaf n) rest) = n` remains stuck on a match of the entire
pair, even though only the first field matters. `ConsumerDrivenMatchBehavior.lean`
prints both forms. The matcher currently needs a sufficiently normalized
discriminant. The next step is a demand-aware matcher that inspects the
constructor spine, identifies which field the pattern examines, and exposes
only that field's choice. That mechanism should preserve sharing and avoid
globally distributing every choice into every constructor. This branch should
not be used to remove PR 14's workarounds yet.

PR 335's deferred match work is in the SMT translator. The experiment here is
in the optimizer's constructor propagation rule; the two changes address
different stages and should be reviewed together before integration.

`lake build Tests.Optimize` passes with the default mode. The local Z3 binary
does not support the `recfun-finder` tactic used in a stronger nested Blaster
proof, so this branch has not validated that path end to end.
