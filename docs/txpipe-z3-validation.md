# Integration validation — 13 November 2026

Initial validated implementation commit: `58e9dafd3605efa9bec53e9d7e0a53859b010615`. The full source-suite follow-up below validates the later implementation at `6a13d2cbee99970ac40e2a7b5b3e1a65f60263a9`.

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

## Full source-suite follow-up

After enabling proof generation in `SmtNatMod`, every one of the 161 Lean sources (`Tests/**/*.lean` plus `Tests.lean`) was invoked freshly with `lake env lean`. This avoids treating cached Lake diagnostics as a new reconstruction run. The comparison used repository option defaults and `BLASTER_GEN_PROOF=1`; default mode still includes tests that explicitly request strict reconstruction, including the updated `SmtNatMod`.

Each full-run file had a 120-second external limit, with its process group stopped on timeout. The default run used one worker and the strict run three. After fixing the new strict-command regression test, that file was rechecked in both modes. The final `SmtNatMod` source was also rechecked in both modes with a 180-second limit. These specific reruns replace their earlier rows. The library and focused reconstruction build passed (258 jobs).

| Outcome | Repository defaults | `BLASTER_GEN_PROOF=1` |
|---|---:|---:|
| Passed | 151 | 125 |
| Failed with a Lean diagnostic | 3 | 23 |
| Interpreter/process abort | 0 | 5 |
| External timeout | 1 | 2 |
| Could not load a test dependency | 6 | 6 |
| Total sources attempted | 161 | 161 |

The six dependency entries are aggregate modules whose test `.olean` dependencies are unavailable while the suite has failures. They are listed separately, rather than counted as six additional reconstruction bugs. The strict run and its targeted replacements emitted 443 accepted, standard-axiom-checked proof-request messages, including requests in files that subsequently failed. This does not mean 443 independent benchmark theorems, nor does it make the full suite green. These runs use the default `z3,z3rec,z3+` proof portfolio and its three seeds, and are not performance comparisons.

Per-file outcomes for both modes are in [txpipe-z3-suite-results.csv](txpipe-z3-suite-results.csv).

The default-mode failures are:

- `Tests/Optimize/NormChoiceApp.lean`: the retained `NormChoiceAppDite_10` optimizer proof gap.
- `Tests/Smt/SmtNat/SmtNatMod.lean`: nonlinear modulo cases with strict proof generation enabled explicitly.
- `Tests/StateMachine/Counter06.lean`: the solver-sensitive expected counterexample-message mismatch.
- `Tests/Smt/SmtPredQualifier.lean`: exceeded the external time limit.

Strict mode additionally exposes unsupported residual Lean forms, polymorphic/higher-order replay gaps and arithmetic replay failures. `Issue29` also contains explicit user axioms, which the `gen-proof` standard-axiom policy rejects. The interpreter aborted in `Issue17`, `Issue26`, `Issue27`, `SmtMatch` and `SmtRecFun`. Detecting a repeated identical case-predicate expansion does not resolve all of these recursion failures. The remaining strict-mode external timeouts are `SmtNatMul` and `SmtPredQualifier`.

### Nat.mod results and fixes

`SmtNatMod` now requests strict proof generation for all 17 positive properties, with ten-second solver budgets. Its seven negative checks retain their counterexample expectations. The positive properties were also isolated and run independently with just backend `z3` and one seed: 15 reconstructed, two failed, and all seven negative checks passed. The final whole-file runs reconstructed 15 properties with repository defaults and 16 with `BLASTER_GEN_PROOF=1`; nonlinear results are not yet stable between runs.

The two remaining difficult properties are:

```lean
∀ (x y z : Nat), (x + y * z) % y = x % y
∀ (x y z : Nat), (z * x) % (z * y) = z * (x % y)
```

The first returned `Undetermined` at the ten-second budget. The second timed out in the isolated backend run, failed on arithmetic replay in one full-file run, and reconstructed in another. Neither case has been weakened or admitted.

The reported `translateApp` failure on the first modulo example was caused by a residual ordinary `ite` before the optimizer's conditional normalization. Two other examples similarly retained `Iff`. The translator now handles these forms directly, with the existing reconstruction bridge proving their correspondence to SMT conditionals and Boolean equality. Transparent residual definitions can be unfolded definitionally, and unsupported application diagnostics show the function name and Lean expression instead of a raw `Lean.Expr` tree. Strict commands now error on an unexpected `Undetermined` result instead of returning successfully without a proof. The focused regression suite passes with this behavior checked.
