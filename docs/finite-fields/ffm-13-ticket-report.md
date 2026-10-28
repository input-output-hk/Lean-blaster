# FFM-13: Structural indexed sorts and canonical finite-field literals

## Job summary

Completed structural indexed sorts, canonical finite-field syntax helpers, and
solver-independent tests of both output paths. All four requested validations
and both exact PROJECT gates passed. No requested check remains incomplete.
This is a syntax-layer change, not native translation or solver admission.

## Changes and syntax contract

- `Blaster/Smt/Syntax.lean`: adds
  `SortExpr.IndexedSort (nm : SmtSymbol) (indices : Array Nat)` with structural
  equality, constructor-tagged hashing, and `(_ name indices...)` rendering.
  Index names, values, order, and arity participate in identity. Equality never
  uses printed strings; equal reconstructed values have equal hashes.
- `Blaster/Smt/EmitCommand.lean`: streams indexed sorts using their structural
  name and numeral indices, including nested sort arguments and alias bodies.
- Corrected two pre-existing printer discrepancies necessary for byte parity:
  `ParamSort.toString` inserted an extra space before its first argument, and
  streaming `defineSort` omitted the space before its parameter list. The
  ordinary printer now matches the existing streaming parameter-sort format;
  streaming aliases now match the ordinary command printer. Command streaming
  retains its trailing newline, which the tests explicitly check.
- `Blaster/Smt/Term.lean`: `isParamSort` explicitly rejects indexed sorts.
- `Blaster/Smt/FiniteFieldSyntax.lean`: pure APIs
  `finiteFieldSort : Nat → Option SortExpr` and
  `finiteFieldLit : Int → Nat → Option SmtTerm`. Both reject modulus zero.
  Literals use integer Euclidean remainder for `0 ≤ N < P` and produce
  `#fNmP` as an unquoted reserved identifier. No machine-word truncation is
  introduced. Positive modulus one and composites are accepted as syntax only.
- `Blaster/Smt.lean`: imports the helper module so the normal library build
  covers it. The helper module itself imports only `Blaster.Smt.Syntax`.
- New `Tests/FiniteField/Syntax.lean` imports `Tests.Pure`. Its only explicit
  aggregate registration is a new final import in `Tests/FixedIssues.lean`.
  All pre-existing test content and import ordering remain unchanged. No
  existing scripts, workflows, Lake configuration, or toolchain pins changed.

The consumed [solver manifest](solver-manifest.json) selects the cvc5 1.4.1
solving profile. Its `f7-linear-model` fixture,
[`f7-linear-model.smt2`](../../fixtures/finite-fields/protocol/f7-linear-model.smt2),
uses `(_ FiniteField 7)` and `#fNm7`; those spellings drive the helpers. The
manifest is not loaded at runtime and was not modified. No solver capability
probe, download, or discovery is added by this ticket.

## Regression coverage

The new module checks:

- Equal reconstructed indexed and nested sorts, equal hashes, different moduli,
  different symbol kinds/names, index order/arity, and constructor separation.
- Hash-table insertion, replacement by a repeated structural key, and lookup
  without aliasing an old `SymbolSort` whose rendered text is identical.
- Existing symbol and parameter sorts, quoted names, nested arrays, declarations,
  alias bodies and parameters, function argument/return sorts, and qualified
  identifiers through both printers.
- Exact literal bytes through both printers and within `define-fun` commands:
  negative and oversized inputs, zero, exact positive/negative multiples,
  characteristic two, modulus one/composites, and inputs/moduli beyond 64 bits.
- Rejection of modulus zero for sorts and positive, negative, and zero literals.

The streaming harness invokes `/bin/cat` at a fixed path solely as a byte relay
for the real `TranslateEnvT` emitter. It compares the complete emitted transcript,
including newlines, and kills/reaps the relay in `finally`. It does not discover
binaries, launch a solver, or use native-query routing. This test harness requires
`/bin/cat`; the syntax constructors themselves require no process or filesystem.

## Exact validation commands and outcomes

Commands ran from the repository root.

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Syntax.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/Smt/SmtSetupCommands.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/Smt/SolverResponses.lean
make test-pure
```

All exited 0. The direct Lean checks passed without diagnostics. `make test-pure`
freshly compiled all 10 discovered finite-field pure modules, including the new
syntax module, then successfully built `Tests.Pure` (248 jobs). This existing
automatic discovery required no script or test-aggregate changes.

Exact PROJECT build command:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
```

Exited 0. Resolved `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reported
`Z3 version 4.15.2 - 64 bit`, and completed the clean library/compilation-coverage
check (219 jobs), including `Blaster.Smt.FiniteFieldSyntax`.

Exact PROJECT tests command:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Exited 0 with the same Z3 path/version. Passed fresh finite-field pure coverage
(10/10), `Tests.Pure`, and the default Z3 tier (`Tests.Z3`, 719 jobs). The new
syntax module also compiled through `Tests.FixedIssues` in the Z3 tier. Existing
lifecycle tests emitted their model-error/timeout diagnostics, also observed in
the baseline dependency build; no expectation or diagnostic was suppressed.

Additional development validation:

```sh
lake --version
lake build Blaster Tests.Pure
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean --run Ffm13Smoke.lean
```

Lake reported 5.0.0 with Lean 4.24.0. The baseline dependency build passed
(246 jobs); the final incremental library/dependency build passed (249 jobs).
The temporary standalone smoke program imported only the helper module and
exercised sort construction, alias rendering, negative reduction, and zero
rejection. Its final run exited 0 and printed:

```text
(declare-const x (_ FiniteField 7))
(define-sort F7 () (_ FiniteField 7))
#f6m7
zero modulus rejected: true
```

The smoke file was removed after validation. It was not registered as a test.

Before changing the production printers, the initial two regression cases in
`Tests/FiniteField/Syntax.lean` failed with exactly `(Array  Int Bool)` versus
`(Array Int Bool)` and `(define-sort Scalar() Int)` versus
`(define-sort Scalar () Int)`. Both cases remain in the passing final module.
An earlier direct invocation preceded the dependency build and failed because
`Tests.Pure` was not built. Intermediate compilation failures from an ambiguous
recursive hash reference and two new-test elaboration errors were corrected;
none remains in the final validations above.

## Boundaries and limitations

- Indexed-sort indices are natural-number numerals, not symbolic SMT indices.
  The raw AST remains a syntax representation, not a semantic validity checker.
- Positivity is the helper precondition, not primality or carrier evidence.
  The AST and helpers do not register residue types, alter backend selection,
  bypass checked admission, authorize queries, decode models, or claim proof
  support. No axioms, `sorry`, `admit`, or changes to `blasterProven` were added.
- No native finite-field solver run or cvc5 capability check was performed or
  required for this syntax ticket. Manifest protocol acceptance is consumed
  from FFM-09, not re-certified here. Routing, translation and typed decoding
  remain outside this ticket's scope.
- No optimization or performance improvement is claimed.
- Publication, remote branch ancestry, and maintainer completion signoff are
  not established by these local checks.
- The local commit attempt was refused because Git author identity is unset.
  The eight deliverable files were staged successfully; no identity was invented
  or repository configuration changed. Owner-attributed commit creation remains
  with the stack's publication step.
