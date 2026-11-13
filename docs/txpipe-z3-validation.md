# Integration validation — 13 November 2026

Validated implementation commit: `58e9dafd3605efa9bec53e9d7e0a53859b010615`. Subsequent documentation commits do not change the Lean implementation.

Environment: Lean 4.24.0 on macOS arm64; Z3 5.4.0 (build `d6c9b4fbb31cb76e35cc325dd7e64b7c26c7d70f`). Proof tests selected `BLASTER_SMTPROOF_BACKENDS=z3` and one solver seed. Other Z3 variants are available but are not part of this focused validation.

| Check | Result |
|---|---|
| Every one of the 29 pinned TxPipe PR heads is an ancestor | Passed |
| `lake build Blaster Tests.Reconstruct.Z3` | Passed, 258 jobs |
| Fresh `lake env lean Tests/Reconstruct/Z3.lean` | Passed; nine named theorems plus two checked commands |
| Standard-axiom audits for all nine named theorems | Passed; only `propext`, `Classical.choice`, `Quot.sound` |
| False-claim and incomplete optimizer-only proof rejection | Passed |
| `BLASTER_GEN_PROOF=1` with unmodified tactic and command calls | Passed; theorem axiom audit contains only the standard three |
| All optimizer modules, plus focused/basic reconstruction | One known failing fixture: `NormChoiceAppDite_10` |
| Original full `lake test` attempt | Incomplete; see below |

The fresh focused run emitted 11 checked-proof messages. Its trace records 12 accepted Z3 residual replays across eight source locations; a single proof request can require more than one residual proof. This confirms actual Z3 replay rather than just a trusted solver verdict. Hypothesis/quantifier transport and the optimizer-only example can close through TxPipe certificates without requiring a Z3 leaf.

The final optimizer recheck used:

```sh
LEAN_NUM_THREADS=4 BLASTER_SMTPROOF_BACKENDS=z3 BLASTER_SMTPROOF_SEEDS=1 \
  lake build Blaster Tests.Optimize Tests.Reconstruct.Z3 Tests.Reconstruct.Basic
```

It completed with only the previously identified `Tests/Optimize/NormChoiceApp.lean:229` proof-gap error. The four inherited String failures now pass. An initially broader early-reduction shortcut caused five Nat recursion-depth failures during the full-suite attempt; restricting that shortcut to String computations fixed them. The final recheck built all five affected Nat modules successfully. No proof expectation was weakened.

The full-suite attempt also reported a `Tests/StateMachine/Counter06.lean:101` expected-message mismatch: Z3 selected different counterexample values. This is distinct from a proof reconstruction failure. The same test was already solver-sensitive in the pre-integration review. The attempt was stopped after about 379 seconds, with progress at 712/735 jobs and these three solver tests still running:

- `Tests/Smt/SmtPredQualifier.lean`
- `Tests/Smt/SmtNat/SmtNatMod.lean`
- `Tests/FixedIssues/Issue16.lean`

Consequently **the full test suite is not claimed to pass**, and no full BlasterBenchmarking run has been performed for this branch.

The branch intentionally retains the TxPipe feature-stack base. It is not a rebase of that stack onto current main. Source pins, attribution and usage are in [TxPipeZ3Integration.md](TxPipeZ3Integration.md) and [txpipe-z3-sources.json](txpipe-z3-sources.json). No PR was opened.
