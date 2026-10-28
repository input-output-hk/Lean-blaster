# FFM-15 — Bounded polynomial translation and typed source metadata

## Change and decisions

`Blaster/Smt/Translate/FiniteField.lean::translatePolynomial` translates the optimized native residual through the parent recognition, admission, indexed syntax and preflight interfaces. `Translate.main` selects this bounded path before generic translation. Generic `Quantifier` and `Application` entry points still reject nominal residue carriers rather than offering an admission bypass or an alternate encoding.

The fragment comprises canonical dictionary-checked addition, multiplication, negation, subtraction encoded as addition of negation, canonical Euclidean literals, equality/disequality, Boolean structure, nondependent implication and supported ite. Closed natural exponents use one semantic wrapper per normalized modulus/exponent, with nested SMT lets sharing squares and accumulators. Construction and emitted body size are logarithmic in the exponent. Zero exponents emit one, including `0^0`.

Sort aliases and arithmetic wrappers are keyed by normalized modulus. Exact source carrier admissions are cached only inside the opened query scope; distinct moduli remain separate. Every source carrier is checked by `admitNativeField`; a numeric modulus alone does not authorize emission. Successful preflight sets query qualification, and session retirement clears it. Dry translation requires cvc5 policy but never discovers or probes a solver. Live qualification remains offline and uses the pinned inventory; profile lookup now supports the child test package by resolving the repository manifest from an ancestor working directory.

`Blaster/Smt/FiniteFieldMetadata.lean` defines `SourceAssociation`: SMT symbol, source user name, originating Lean expression, exact type, normalized modulus, assertion polarity, local context and local instances. Native declarations and opened theorem variables retain these associations. The existing tuple-valued `TopLevelVars` remains solely the model-display index; typed provenance is the separate authoritative `sourceAssociations` array. This preserves the protected model fixture and avoids implementing FFM-16 display changes. No type is recovered from a printed name.

Unsupported residual binders, higher-order expressions, variable/integer exponents, representation projections/casts, order and mixed theories fail with diagnostics rather than generic translation fallback. The optimizer rejects representation access and integer powers before unfolding could erase their nominal boundary. These are rejection guards, not finite-field arithmetic rewrite families. Ordinary raw `Fin.div` retains its truncating behavior.

`Blaster/FiniteField/Pow.lean` supplies kernel-checked zero, successor-zero, even/odd and half-exponent arithmetic lemmas. Its executable transitive axiom guard permits only `propext`, `Classical.choice` and `Quot.sound`. No production proof reconstruction, new axiom, verified outcome, or modification to `blasterProven` was introduced.

## Test layout

- New `Tests/FiniteField/Translation.lean`: solver-independent transcripts, normalized aliases and distinct fields, arithmetic/Boolean/ite, powers and logarithmic sharing, saved typed scope, fail-closed inputs, production dry dispatch, source arithmetic and raw `Fin.div`.
- Its import is appended only at the end of `Tests/FixedIssues.lean`. No earlier protected test is edited.
- New `ff-tests/TestsFF/Polynomial.lean`: source-to-production solver SAT/UNSAT cases for characteristic two, seven, Curve25519 and two moduli, with checked local prime evidence and concrete model assertions. The child aggregate imports it.
- Existing scripts, workflows, lakefiles, toolchain and solver pins are unchanged.

## Observed smoke evidence

`make ff-stage` exited 0: the pinned Linux-arm64 solving profile staged successfully and passed offline setup, solving, model, version and configuration checks. Proof export remains explicitly deferred to M2.

A temporary `PolynomialSmoke.lean` was executed with:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean PolynomialSmoke.lean
```

The corrected smoke exited 0. The actual production `#blaster` commands observed:

- F2 false implication `2*x=0 → x=0`: Falsified, counterexample `x: #f1m2`.
- F7 zero-product implication: Valid.
- Dry power translation: Undetermined, without a solver verdict.
- A successful native `blaster` tactic retained the existing warning `declaration uses 'blasterProven' (SMT-verified, no proof term)`; `#print axioms` reported exactly `Blaster.Tactic.blasterProven` for that temporary theorem.

Initial smoke command options incorrectly used outcome code 2 for Valid and a Boolean instead of numeric `only-smt-lib`; these harness errors were corrected (Valid is 0, Falsified is 1, Undetermined is 2). Iterative compilation also caught structure-layout syntax, a mutable variable shadow, nonconstant-head access, and elaborated natural numeral handling. The latter now uses the parent's checked closed-natural normalizer. No expected mathematical result was weakened.

The initial `make test-cvc5-ff` attempt reached the existing four capability cases but timed out at the outer 600-second command deadline. Importing the parent `Tests.FiniteField.LargePrime` module directly into the child package caused Lake to build the entire parent test library shared facet, including ordinary Z3 tests in the wrong default solver environment. `Counter06Z3` showed model-text mismatches; no protected expectation was changed. The child module now runs an explicit `lake build Tests.FiniteField.LargePrime` followed by `lake env lean ff-tests/PolynomialSource.lean` from the repository root. The source cases still consume the checked fixture and the actual production translator; the driver no longer crosses into the ordinary test tier. A direct translation run against stale compiled optimizer artifacts also caught the newly added integer-power rejection assertion; validation below uses freshly built sources.

The temporary smoke source was removed after observing the tactic warning and axiom closure.

## Remaining scope

Typed counterexample display is FFM-16; inverse/division graph translation is FFM-18; general primality automation and mixed encodings are FFM-22. ProofStep/CPC checking, verified closure and FF optimizer rewrite families remain M2. Source arithmetic lemmas do not turn trusted solver success into a reconstructed Lean proof.

## Final validation commands and outcomes

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

Passed, exit 0, 103.35 seconds. Resolved `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2. Clean compilation and complete Blaster source-coverage gate succeeded (234 jobs), including the new source-power axiom guard.

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Translation.lean
```

Passed, exit 0, 2.20 seconds, no output. Includes the actual optimized ite path, representation/integer-power rejection before unfolding, typed metadata scope, canonical residues, F2 false-implication transcript, reducible aliases, distinct fields and shared-power assertions.

```sh
make test-cvc5-ff
```

Passed, exit 0, 19.09 seconds. Offline qualification passed. The child coverage gate compiled all child modules (240 jobs) and executed the four existing capability cases plus **5 SAT and 10 UNSAT native polynomial cases**, with no capability skips. Actual counterexamples included `x = #f1m2` for the false characteristic-two implication, `x = #f0m7` for unguarded `x^6=1`, a Curve25519 value, and independent F2/F7 values. Valid cases included characteristic identities, zero-product, `0^0`, positive powers of zero, guarded `p−1`, exponent `p`, ite/subtraction/negation, and large-prime distributivity.

Before this passing run, the isolated source fixture failed elaboration because the concrete large-modulus numeral needed its own `NeZero curve25519` instance at definition time. A kernel-decided instance was added; checked prime admission still uses `curve25519_evidence`. No solver result or expected outcome changed.

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Passed, exit 0, 210.33 seconds, using Z3 4.15.2. The recipe executed the requested `make test-pure`: all **13/13** discovered finite-field modules freshly compiled, followed by a successful clean `Tests.Pure` build (263 jobs). Its `make test-z3` then completed successfully (743 jobs), including the unchanged `Counter06Z3`, all prior finite-field regressions and the appended translation module. Existing lifecycle fault-injection warnings remained visible; no check, expected result, timeout policy or protected test was weakened.

## Job summary

FFM-15's bounded native translator, typed declaration metadata, logarithmic shared powers and guarded source lemmas are implemented. All requested validation lanes passed: staging, clean Blaster build/source coverage, pure coverage, direct translation module, pinned native live cases and the complete Z3 4.15.2 project test gate. The production trust closure and warning remain unchanged. Remaining work is only the separately scoped FFM-16/18/22 and M2 functionality listed above; no publication or maintainer signoff is claimed.
