# libz3 migration and typed counterexamples

## Acceptance criteria

The native backend consumes `SmtCommand`, `SortExpr`, and `SmtTerm` directly and
builds Z3 sorts, declarations, and ASTs with the C API. No solver command is
sent through an SMT-LIB parser. The existing SMT-LIB renderer remains useful for
debug output and as a temporary comparison backend.

For each solver-facing command and term emitted by Blaster, the native backend
must either reproduce the existing result or report an explicit unsupported
case. It must never silently skip a command that affects solving. This includes
`recfun-finder`, options, recursive and parametric datatypes, quantifiers and
patterns, assumptions, timeout, cancellation, model evaluation, and
state-machine checks.

After `sat`, model values for top-level Lean variables are read from Z3 ASTs.
A decoder may return a Lean expression only after checking that its inferred
type is definitionally equal to the original Lean variable's type. If a value
cannot be reconstructed, diagnostics retain the raw Z3 value and explain that
the typed value is unavailable. A reconstructed value is diagnostic evidence,
not a proof of the original proposition.

`(replay: 1)` instantiates the original Lean proposition with the typed native
model values in binder order and evaluates the resulting `Decidable` expression.
It reports false, true (a solver/translation mismatch), or inconclusive when
the model or Lean computation is insufficient. The default is `(replay: 0)`.
Replay requires `(backend: ffi)` while the subprocess backend remains available.

## Work sequence

1. Rebase the existing native AST builder from `feat/z3-ffi-migration` onto
   current `main`; update it for Z3 5.4.0 and all new SMT syntax.
2. Run focused native tests, then run the existing Lean Blaster test suite
   against both backends. Keep every existing test module in the import graph.
3. Expose Z3 model AST inspection (sort, numeral, string, constructor name,
   children) through the C shim. Decode `Nat`, `Int`, `Bool`, `String`,
   `BitVec`, and constructor applications using the expected Lean type.
4. Add tests that inspect reconstructed expressions with Lean's type checker,
   including nested inductives and deliberately unsupported values. Test the
   user-facing counterexample messages separately from the decoder.
5. Check the build on macOS and Linux, the library loading path in downstream
   Lake projects, solver errors, and cancellation. Select the native backend by
   default after the full parity suite passes.

## Parity matrix

| Area | Representative tests |
| --- | --- |
| Arithmetic, Bool, strings, BitVec | `Tests/Smt/`, native backend fixtures |
| Recursive and parametric datatypes | `Tests/Smt/SmtList/`, `Tests/Smt/FFI/` |
| Quantifiers, patterns, assumptions | `Tests/Smt/`, `Tests/StateMachine/` |
| Counterexamples and Lean types | dedicated typed model tests |
| Unknown, timeout, cancellation | native backend option tests |
| Build and package wiring | `make check_all`, downstream Lake smoke test |

The migration is complete when the same suite passes through the native
backend on Z3 5.4.0, with no excluded imports or changed expected verdicts,
and typed counterexamples pass the Lean type checks above.
