# Rejected preparation experiments

These patches are archived evidence, not enabled code or recommended defaults.
The review explains each failed gate. Apply one patch at a time to Blaster
`36c3a15a9fdc9f3237ad376f8d67665e3742d3f8`, then rebuild both Cardano dependency
sets before measuring. Do not combine these patches.

- `ancestor-candidate.patch`: the first port of PR #160 ancestor lookup. It
  returns ancestor results directly and fails child-normalization tests. Copy
  `ancestor-scope-tests.lean` to `Tests/Optimize/CacheReuse/AncestorScopes.lean`
  before running the full test suite.
- `pure-candidate.patch`: bounded raw abstraction/substitution memoization.
  Copy `pure-transform-tests.lean` to
  `Tests/Optimize/CacheReuse/PureTransforms.lean`. The recorded additional
  cache counters came from temporary preparation diagnostics; the core patch
  reproduces the algorithm, while the regular telemetry patch reports the
  comparable optimizer time and retained node/context counts.
- `constructor-choices.patch`: opt-in global constructor-choice retention. Use
  the runner's `--retain-constructor-choices`. `ConstructorChoices.lean` is the
  focused semantic test; it can be copied under `Tests/Optimize/CacheReuse/`.
- `demand-candidate.patch`: broad early function/projection reduction. Use
  `--reduce-before-arguments`. `DemandReduction.lean` contains the focused
  tests; they pass while real Cardano workloads regress.
- `selective-candidate.patch`: retain choices for named types/constructors.
  The recorded scout uses `--retain-choice-types List Prod PlutusCore.Data.Data`.
  It still regresses global preparation and does not improve the ordinary
  examples. Its algorithm does not recursively label container element types.

The test names imported by the first two patches are not part of the benchmark
build targets. For benchmark-only reproduction, their test-import hunks can be
excluded with `git apply --exclude=Tests/Optimize.lean PATCH`.

`replay2-candidate.patch` is the conservative ancestor-replay follow-up. Copy
`replay2-scope-tests.lean` to
`Tests/Optimize/CacheReuse/AncestorRenormalization.lean`. It passes the previous
normalization failures but gives no Cardano speedup. The full-suite arithmetic
timeout did not reproduce when the module ran alone (both arms pass).

`values-candidate.patch` adds container-aware labels to the selective policy.
Its scout labels PlutusCore.UPLC.Term.Const, PlutusCore.UPLC.Term.Term,
PlutusCore.UPLC.CekValue.CekValue, PlutusCore.UPLC.CekValue.Environment and
PlutusCore.Data.Data. It regresses global preparation. The final scoped-label
PR removes the earlier global Boolean switch; labels are its only opt-in.
