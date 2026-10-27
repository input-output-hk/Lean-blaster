# Lean 4.35 compatibility

Blaster pins Lean **4.35.0** in both `lean-toolchain` and stable CI. CI checks that
the pins agree. A new Lean release does not change the supported version.
The solver pin remains Z3 **5.3.1**, as on the beta-lambda-cache-optimization base.

## Strings and slices

Lean strings now have a UTF-8 byte-array model with a validity proof. Construct a
string with `String.ofList`; inspect its characters with `String.toList`. For
example, replace a pattern on the former `String.mk` constructor with a match on
`s.toList`. Blaster normalizes both public round trips and reasons about
`String.ofList` injectivity using character lists, while preserving expression sharing.

`String.take` and `String.drop` return `String.Slice`. Use `.copy` when a String
value is required:

```lean
#eval ("é∀x".take 2).copy -- "é∀"
#eval ("é∀x".drop 2).copy -- "x"
```

Blaster folds copied-text observations and Boolean comparisons of supported constant
slices. Slice structure equality differs from copied-text equality; the optimizer
preserves that distinction. General symbolic Slice operations still require an
encoding beyond the currently supported operators.

Standard String-pattern/String-replacement calls to `String.replace` use a
monomorphic internal wrapper. The normalizer checks the iterator, searcher, and
conversion arguments, identified from the declaration's binder metadata, before
assigning standard SMT semantics. Custom instances
and other pattern types produce an explicit unsupported diagnostic.

Lean 4.35 inserts replacements at every character boundary for an empty pattern:
`"ab".replace "" "x" = "xaxbx"`. The SMT encoding implements this branch with a
suffix recursion. Non-empty patterns use `str.replace_all`. Recursive string
queries can return `Undetermined`, which remains distinct from `Valid`.

## Characters and the SMT alphabet

Lean Char represents Unicode scalar values in `0..0x10FFFF`, excluding the
surrogate interval `0xD800..0xDFFF`. SMT-LIB's Unicode string alphabet ends at
`0x2FFFF`. Optimizer-only operations preserve the full Lean range, including
`0x30000` and `0x10FFFF`. String literals above the SMT alphabet bound are rejected
when translation needs to emit them; issue 35 retains its boundary diagnostics.

Constant `Char.ofNat` and `Char.ofNatAux` values receive kernel-generated validity
proofs in the dedicated character rewriter. Invalid inputs to `Char.ofNat` retain
Lean's NUL result. Pattern proof handling is independent of Char: a closed witness
is restored only when optimization changes its required dependent type. The original
witness is reused when it still has that type; otherwise reconstruction requires a
checked decision proof. Open proof variables remain available for unification. No
Char-to-SMT code-point cast is introduced by this migration.

## Recursive normalization

Blaster recognizes equivalent recursive functions by normalized body structure.
Lean changed the bodies of `Int.pow`, `Nat.ble`, and `List.beq`. Stable logical
models in `Blaster/Optimize/Canonical.lean` preserve the previous normalization
behavior. Each model is selected through a Lean-checked equivalence theorem.
Registration checks that the theorem applies both the native operation and its
model to every parameter. The list model works
for arbitrary BEq instances. The native operation's identity and instance keys
remain in use.

## Validation and downstream projects

Run with Lean 4.35.0 and the pinned Z3 version on PATH:

```sh
lake build z3check
lake exe z3check
make check_all
```

Tests cover native string views, UTF-8 byte counts, replacement semantics, character
boundaries and validity proofs, recursive normalization, solver outcomes, and state
machines. The legacy constructor-pattern fixtures use explicit character lists;
native string literal and public-view cases remain covered independently. No test
cases are dropped to accommodate the new representation.

Downstream projects must use the same Lean toolchain and a Blaster revision
containing the entire migration. Update the dependency revision, run
`lake update Blaster`, clean old build products, and rebuild the downstream tests.
Source changes in separate consumer repositories are a separate migration step.
