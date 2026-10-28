# FFM-16 — Typed finite-field counterexamples without verdict changes

## Change and decisions

`Blaster/Smt/FiniteFieldModel.lean` adds a narrow decoder, not a general SMT AST or Lean model reconstructor. `decodeLiteral` accepts only canonical unsigned `#fNmP` literals with the expected modulus, modulus at least two, and `0 ≤ N < P`. `decodeResponse` requires exactly one complete `((symbol literal))` entry and checks the echoed SMT symbol byte-for-byte. Wrong modulus, negative/out-of-range representatives, extra entries, malformed/truncated framing, trailing data, nonliteral expressions and let sharing are unavailable evidence rather than values to normalize.

Both pure decoders cap input at 4096 UTF-8 bytes before parsing. The native streaming reader caps bytes before an unbounded line allocation, supports ASCII whitespace/multiline framing and quoted symbols, and consumes no bytes after the response's terminating newline. Its byte limit includes that newline. Numeral accumulation is bounded by the expected modulus. Unsupported nesting, invalid ASCII, EOF, a missing final newline and oversized responses fail with static diagnostics. The existing five-second optional-model response timeout also bounds stalled streams.

`Blaster/Smt/Env.lean` selects this path only for native residue bindings. It validates a unique `SourceAssociation`, source variable/name association, inferred source type, retained declared type, and normalized modulus in the association's saved local context and local instances. A validated value is displayed beside its original source name, for example:

```text
x: (6 : Blaster.FiniteField.Residue 7) [#f6m7]
```

The canonical `Residue P` annotation is used even when the source type is a reducible alias. The original canonical SMT literal remains visible. No Lean value or proof term is constructed.

The model request retains its producing `SolverSession`; the request boundary additionally checks that the current process PID still matches it. Invalid FF evidence retires that session before another variable can consume a failed frame. Earlier validated values remain available, later variables receive bounded per-variable unavailable diagnostics, and the owner finalizer kills/reaps all remaining children on success, diagnostic and exception paths. No replacement solver is started to obtain optional evidence.

SAT remains `Result.Falsified`, including absent, failed and timed-out evidence. The existing verdict aggregation and theorem-closing paths are unchanged. Non-native raw handling is unchanged, including let-shared values; ordinary Boolean bindings in native queries retain that raw path. No changes were made to polynomial translation, production proof retrieval, `blasterProven`, axioms or trusted closure.

## Optional typed syntax decision

`(as ffN F)` is **unavailable**, not accepted speculatively. The selected Linux-arm64 solving profile is pinned cvc5 1.4.1, revision `2b2e844`. The fresh `make ff-stage` capture for `case-f7-linear-model-typed` emitted:

```text
sat
((x #f6m7))
```

This agrees with the committed `fixtures/finite-fields/protocol/observed-linux-arm64.json`: typed *input* does not establish typed *output*. Fresh staging evidence was recorded under `.artifacts/finite-fields/solving/evidence/run-20261028T053139Z-9078225c8cd9420d9884e9bff6abd606/`. No manifest, capability expectation or frozen fixture was changed. Enabling an alternate output spelling would require an actual selected-profile capture and explicit sort-identity validation.

## Regression coverage

- New `Tests/FiniteField/Model.lean`: F2/F3/F7 and a large modulus; F7 representative six; strict literal/range/symbol/framing validation; byte-limit boundaries; multiline/quoted symbols; next-response preservation; malformed, truncated, oversized, let-shared and optional typed syntax rejection.
- Actual shell-pipe lifecycle cases: wrong source type/modulus, missing/ambiguous metadata, bounded per-variable diagnostics, EOF, timeout, disabled model generation, partial counterexamples, no request after retirement, repeated fresh sessions, SAT-producer ownership in first-mode orchestration, child reaping, and unchanged ordinary/Boolean raw values. Concurrent native preflight policy is not changed; the first-mode case exercises the existing model lifecycle boundary directly.
- Its one import is appended to the end of `Tests/FixedIssues.lean`. Earlier imports and all other existing protected tests/scripts remain unchanged.
- New `ff-tests/TestsFF/Model.lean` runs `ff-tests/ModelSource.lean` through the real production translator. Five pinned live SAT cases cover exact F2=1, F3=2, F7=6 displays, three moduli together, and disabled evidence. Each binding's request and captured response is checked against its own source symbol and producing solver record. The tests require cleanup, no proof request, and unchanged Falsified verdicts.
- `ff-tests/TestsFF.lean` imports the new live module. Existing polynomial and capability cases still run with their original expectations. No Makefile, CI, lakefile, toolchain or solver pin changes were needed.

## Exact validation commands and outcomes

All final commands below passed. Staging was the only network step; subsequent native runs used the staged, hash-verified offline profile. No `lake test` was run.

### Staging

```sh
make ff-stage
```

Exit 0, 3.48 seconds. Archive/executable staging and offline version, configuration, setup, solving and model checks passed. All four protocol cases passed. Proof export remains deferred to M2.

### Focused pure module and pinned live suite

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Model.lean && make test-cvc5-ff
```

Exit 0, 63.75 seconds for the combined command. The pure module produced no errors. The native coverage gate completed 250 jobs: four existing capability cases, five new SAT model cases (four typed displays, one disabled), and the existing five SAT/ten UNSAT polynomial cases. The latter also exercised a Curve25519 typed counterexample. No capability skips or changed expected outcomes.

### Actual command-surface smoke

A temporary `FiniteFieldModelSmoke.lean` invoked `#blaster (solver: cvc5) (solve-result: 1)` on `∀ (_ : PrimeModulus 7) (x : Residue 7), x + 1 ≠ 0` and the analogous F3 goal with source variable `y`.

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS BLASTER_FF_CVC5=/workspace/lean-blaster/.artifacts/finite-fields/solving/bin/cvc5 lake env lean FiniteFieldModelSmoke.lean
```

Exit 0, 1.50 seconds. Both commands printed `Expected Falsified`. Their counterexample lines were exactly `x: (6 : Blaster.FiniteField.Residue 7) [#f6m7]` and `y: (2 : Blaster.FiniteField.Residue 3) [#f2m3]`. The temporary source was removed after execution.

### Clean project build and source coverage

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

Exit 0, 109.21 seconds; 243 jobs, complete source coverage. Resolved `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting Z3 4.15.2.

### Project pure and Z3 tests

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Exit 0, 245.93 seconds with the same Z3 4.15.2 executable. This executed `make test-pure` (including `make test-ff-pure`) and `make test-z3` from clean test outputs. Finite-field pure coverage freshly compiled **16/16** registered modules, including `Tests.FiniteField.Model`; ordinary `Tests.Pure` passed, and the Z3 tier completed 761 jobs. Existing lifecycle warning cases, the protected axiom-audit warning and the existing `SmtNatMod` Undetermined warning remained visible; no checks or expectations were suppressed or weakened.

### Iterative failures resolved

The first `lake build Blaster Tests.FiniteField.Model` built the library but rejected new test code using an unavailable `BEq (Except String Nat)` instance, `String.ofList`, direct `Option String` message interpolation and an unannotated IO/MetaM block. Tests were corrected to pattern matching, `String.mk`, explicit diagnostic extraction and `run_meta`. The next focused module run found a multiline structure-literal layout error in the new partial-evidence fixture; its typed local declaration was corrected. The final focused/live command and both complete project gates then passed. No production behavior or expected result was weakened to resolve these fixture errors.

## Job summary and limitations

FFM-16 is implemented and validated: typed residue display is checked against retained source metadata, model failures remain optional SAT evidence failures, session ownership and cleanup are exercised, and non-FF model handling is preserved. Exact commands and outcomes are above. The committed delivery is this report plus the implementation and registered regressions; no publication or maintainer signoff is claimed.

Deliberate limits: plain literal output only, ASCII SMT framing, 4096 bytes including the final newline, no let expansion/general model reconstruction, and no native proof retrieval or verified theorem closure. The unobserved `(as ffN F)` form remains unavailable. Cross-platform model spelling was not exercised here. Production proof reconstruction/verified closure remains M2; division translation remains FFM-18. No unresolved FFM-16 implementation or validation work remains within the requested scope.

## Standalone pure gate

```sh
make test-pure
```

Also run directly after the project gates: exit 0, 48.10 seconds. Fresh finite-field coverage was again 16/16 modules; the ordinary pure lifecycle suite also passed. This gate launched no actual solver.
