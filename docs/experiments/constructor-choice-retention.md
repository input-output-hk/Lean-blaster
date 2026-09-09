# Scoped constructor-choice retention

Status: experimental, opt-in. This fixes the compact-representation example in
[issue #238](https://github.com/input-output-hk/Lean-blaster/issues/238), but it
is not a recommended Cardano performance setting.

The optimizer normally moves a conditional out of a constructor application.
For independent fields, repeated distribution can enumerate combinations that
a consumer never needs. The minimal 12-element example in issue #238 allocates
16,379 contexts and 117,084 hash-cons entries at baseline, versus 47 contexts and
2,817 entries with field choices retained.

Use a local attribute on an inductive type or constructor:

```lean
import Blaster

section
attribute [local blaster_keep_choices] List
-- Optimizer calls here can keep conditional elements inside List.cons.
end
```

A labelled datatype also affects containers parameterized by it. Labelling
`Value` therefore affects `List Value` and `Option Value`, while leaving
`List Frame` alone. Type abbreviations are not unfolded by this label lookup;
label the underlying inductive type. Labelling an unrelated declaration has no
effect. Local attributes do not change the policy in importing modules.

The attribute disables only the constructor-hoisting decision. Consumers may
still split on choices, and other normalization rules still run. It does not
provide a complete lazy evaluator, new datatype support, or a proof of
correctness for preparation. Without labels, the existing policy is unchanged.

`Tests/FixedIssues/Issue238.lean` checks the compact normal form, consuming a
choice, positive and negative Blaster verdicts, a structural growth bound,
container propagation, and preservation of the policy for unmarked types.
The growth test uses node/context bounds instead of machine-dependent timing.

## Cardano gate

The [benchmark review](../reviews/cardano-preparation-2026-09-09.md) records the
complete investigation. On the production global validator at fuel 1,600:

| Policy | Optimizer time |
| --- | ---: |
| Baseline | 59.46 s |
| Retain choices in every constructor (earlier prototype) | 105.85 s |
| Label List, Prod and Plutus Data | 107.12 s |
| Label interpreter values, environments, constants, terms and Data | 99.78 s |

These are single scouts, not repeated speedup estimates. The last policy
reduced SellNFT's retained nodes from 8.11 M to 7.82 M, but its small timing
change is unconfirmed and does not outweigh the global regression. Its
ParamFeed proof passed; full Cardano proof comparisons were not pursued after
the preparation gate failed. The earlier all-constructor prototype also made
the SellNFT proof phase substantially slower.

This experiment isolates a useful control over representation growth. It must
not be promoted as a general speedup until a demand-driven consumer policy
passes preparation-plus-proof and acceptance/non-vacuity gates. The
[staged-preparation design](../design/cardano-staged-preparation.md) describes
that next architectural investigation.
