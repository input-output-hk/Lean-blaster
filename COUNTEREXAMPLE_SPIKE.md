# cvc5 counterexample spike

## Reproduction

Environment used for this spike:

- Lean 4.24.0
- cvc5 1.3.4 (`git f3b21c4`)
- Z3 4.15.4

Run the saved instrumented cases:

```bash
lake env lean Tests/Smt/CounterexampleSpike.lean
```

`verbose: 3` records the Lean goal, optimized expression, complete SMT-LIB
transcript, solver version and invocation, `check-sat` response,
`topLevelVars`, model command, raw response, parsed S-expression,
Lean-facing rendering, and cleanup stderr stage.

Run the local model/process failure reproductions:

```bash
lake env lean Tests/Smt/CrashLifecycle.lean
```

Run all existing cvc5 model cases (scalars, structures, options, tuples,
lists, strings, uninterpreted values, and functions):

```bash
lake env lean Tests/Smt/SmtSolverCvc5.lean
```

## Cases and classifications

| Case | Observed pipeline | Classification | Result |
|---|---|---|---|
| Forced scalar `∀ x : Int, x ≠ 3` | `sat`; `topLevelVars=[$0:x]`; `(get-value ($0))`; raw `(($0 3))`; parsed and rendered as `3` | No failure | `Falsified`, `x: 3` |
| Consecutive telescope `∀ x y : Int, y = x` | Both binders become eligible declarations and both receive `get-value` queries | No failure | Complete scalar evidence |
| Quantifier under disjunction `∀ x, x = 0 ∨ ∀ y, y = x` | `sat`; `$0` is a declaration, `$1` remains bound inside SMT `forall`; `topLevelVars=[$0:x]`; only `$0` can be queried | Source variable not present in `topLevelVars`; encoding/query shape prevents a top-level query for the nested witness | `Falsified` is preserved; evidence contains `x` but not `y` |
| Abstract type `∀ α : Type, ∀ x y : α, x = y` | `α` is intentionally excluded as a type universe; `x` and `y` are queried and cvc5 `as` values render as raw uninterpreted elements | No missing value; raw-rendering fallback | `Falsified` with `x` and `y` evidence |
| Controlled cvc5 timeout in `Tests/Smt/SmtSolverCvc5.lean` | `unknown`; no model command sent | cvc5 returned `unknown` | `Undetermined` |
| Fake solver returns `sat`, then `(error "model unavailable")` | Raw model error retained; evidence status becomes `modelFailed` | get-model returned an SMT error | Remains `Falsified`; clear counterexample-unavailable warning |
| Fake child closes stdout and writes stderr | Framing/read failure; child is retired, killed if live, reaped, and stderr retained | Response framing / solver process failure | Infrastructure failure, never `Undetermined` |
| Cancellation during model extraction | Both sessions retired before interruption; both process groups terminated and reaped | Solver process interrupted during model retrieval | Cancellation propagated; no child remains |

No S-expression parser rewrite was indicated. Existing pure reconstruction cases for
primitives, strings, quoted symbols, datatype constructors, multiline values,
`as` qualifiers, and shared `let` values remain covered by
`Tests/Smt/ModelReconstruction.lean`.

## Fixes in this branch

- Canonical queries and per-solver protocol records are retained independently
  of SMT dumping.
- Level-3 diagnostics expose every model-retrieval stage without unconditional
  debug output.
- `check-sat` verdict parsing is separated from model retrieval. A model command,
  framing, parser, or rendering failure after `sat` sets `modelFailed` but does
  not erase `Falsified`.
- Raw model responses and stderr are retained in solver records and agreement
  artifacts.
- Process/protocol failures have structured statuses and cannot be represented
  as ordinary solver `unknown` outcomes.
- Fake-process regressions cover stderr preservation, closed stdout, exact-once
  retirement, loser cancellation, two-child cancellation, and cancellation
  during model extraction.

## Unresolved follow-up

### Nested quantified witnesses are absent from rendered counterexamples

Saved reproduction:

```lean
#blaster (solver: cvc5) (verbose: 3) (solve-result: 1)
  [∀ (x : Int), x = 0 ∨ (∀ (y : Int), y = x)]
```

The generated query declares `$0` but binds `$1` inside an SMT `forall`.
`topLevelVars` correctly contains only `$0`; `(get-value ($1))` would be
ill-scoped. Producing `y` therefore requires an encoding/evidence design change
(e.g. witness-bearing negation or scoped model queries), not a local parser
fix. This is intentionally out of branch scope. The GitHub follow-up issue
should use the title **“Counterexample evidence omits witnesses bound by nested
SMT quantifiers”** and attach `Tests/Smt/CounterexampleSpike.lean` plus its
level-3 transcript.

## Known limitations

- `unknown` has no model evidence.
- Type-universe binders are intentionally absent from `topLevelVars`.
- Nested quantified witnesses are not top-level queryable.
- Values without a Lean display form remain raw SMT text.
- Agreement artifacts are written only for unsuccessful or model-incomplete
  agreement runs, under `.blaster/agreement-*`.
