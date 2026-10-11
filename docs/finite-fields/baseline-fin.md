# Finite fields, step S4: `Fin 7` baseline

This records how Blaster handles `Fin 7` ring goals **before** any finite-field
support. Everything here was observed by running the commands below; nothing is
inferred. The regression test that pins it is `TestsSolver/SmtFinBaseline.lean`
(Z3, run by `make test-solver`). Its cvc5 counterpart is
`TestsCvc5/Cvc5FinBaseline.lean` (run by `make test-cvc5`). The protected
`Tests` tree is left unchanged, so neither file is part of `make check_tests`.

## Environment

| Item | Value |
|------|-------|
| Base commit | `hillclimb-base` @ `ab82a3cb647cbdecc198202244622554e2464e4d` |
| Lean | 4.24.0 (`lean-toolchain`) |
| Z3 | `Z3 version 5.1.0 - 64 bit - build hashcode ca39e58c525c5b03c2484f118ade2b92fae31215` (the pinned `recfun-finder` fork) |
| cvc5 (merged branch only) | `cvc5 1.4.1 [git 2b2e844 on branch HEAD]`, `cocoa : yes` |

The base itself has no cvc5 backend. The base observations were taken in a
detached worktree of `ab82a3c` with `lake env lean <file>`. The same file was
then run unchanged on the branch that merges `feat/cvc5-concurrency`, and
produced identical messages.

## Goals and observed results

`set_option trace.Translate.optExpr true` prints the expression produced by the
optimizer (the input to SMT translation).

| # | Goal | Optimized expression | Result |
|---|------|----------------------|--------|
| A | `∀ (a b c : Fin 7), a * (b + c) = a * b + a * c` | nested `Fin.add`/`Fin.mul` matches (below) | **error**: `Inductive datatype with instance parameters not supported: `` `Fin `` |
| A' | same, `(only-optimize: 1)` | same | `⚠️ Undetermined` |
| B | `∀ (a : Fin 7), a * a ≠ 2` (false: `3 * 3 = 2`) | `∀ (a : Fin 7), ¬⟨2, ⋯⟩ = match a, a with \| ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩` | **error** (same message). No counterexample |
| C | `(3 : Fin 7) * 5 + 2 = 3` | `True` | `✅ Valid` (no solver call) |
| D | `(1 : Fin 7) / 2 = 0` | `True` | `✅ Valid` |
| E | `(6 : Fin 7) / 2 = 3` | `True` | `✅ Valid` |
| E' | `(3 : Fin 7) / 0 = 0` | `True` | `✅ Valid` (merged branch; added to the test after the base run) |
| F | `(1 : Fin 7) / 2 = 4` | `False` | `❌ Falsified` (`✅ Expected Falsified` with `(solve-result: 1)`) |
| G | `∀ (a b : Fin 7), a / b * b = a` | `∀ (a b : Fin 7), a = match (match a, b with \| ⟨a, h⟩, ⟨b, isLt⟩ => ⟨a.div b, ⋯⟩), b with \| ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩` | **error** (same message) |

Optimized expression for goal A, verbatim:

```
∀ (a b c : Fin 7),
      (match a,
          match b, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩) =
        match
          match a, b with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩,
          match a, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩
```

### SMT representation

There is none. Running goal A with `(dump-smt-lib: 1)`, and again with
`(only-smt-lib: 1) (dump-smt-lib: 1)`, prints only the error above and no
`Smt Query:` block. Translation aborts before the query is complete, so no
`check-sat` is ever sent. Goals C–F are closed by the optimizer and never reach
translation (`(dump-smt-lib: 1)` on goal C prints only `✅ Valid`).

### Why translation fails

`Fin n` is translated as an inductive datatype (`Fin.mk (val : Nat) (isLt : val < n)`).
`translateInductiveType.genIndParams` (`Blaster/Smt/Translate/Quantifier.lean`)
only accepts inductive parameters that are type universes (polymorphic
parameters) or class constraints. `Fin`'s parameter `n : Nat` is a value, so it
throws `Inductive datatype with instance parameters not supported`. This holds
for any goal that quantifies over `Fin k`, whatever the arithmetic.

### cvc5 (merged branch)

Selecting `(solver: cvc5)` changes nothing for these goals. Goals A and B fail
with the same translation error, and goal D is `✅ Valid` from the optimizer
alone. The same ring identity over `Nat` representatives modulo 7, with
`a b c < 7`, is `✅ Valid` with both Z3 (base) and cvc5 (merged branch). On
base Z3, `∀ (a : Nat), a < 7 → (a * a) % 7 ≠ 2` is correctly falsified.

## `Fin.div` is not field division

Lean's `Fin.div` is `⟨a.val / b.val, _⟩`: **truncating `Nat` division of the
representatives**. The optimizer shows this as `⟨a.div b, ⋯⟩` in goal G. It is
not division in GF(7):

- `(1 : Fin 7) / 2 = 0` in Lean (goal D, Valid), but `1 / 2 = 4` in GF(7)
  because `2 * 4 = 8 ≡ 1`. Goal F (`= 4`) is Falsified.
- `(6 : Fin 7) / 2 = 3` agrees with GF(7) only because 2 divides 6 exactly.
- `(3 : Fin 7) / 0 = 0` is Valid: division by zero follows `Nat` (`x / 0 = 0`), with no notion of inverse.

A finite-field encoding must therefore never map `Fin.div` (or `HDiv` on `Fin p`)
to the SMT finite-field division/inverse. Field division needs a dedicated field
type or explicit inverse. `Fin` multiplication, addition, subtraction and
negation are ring operations mod `n`, and coincide with GF(p) operations only
when `n = p` is prime.

## Reproduction

```bash
# Base (Z3): every guard in the file must pass.
lake env lean TestsSolver/SmtFinBaseline.lean
# cvc5 counterpart (needs cvc5 on PATH):
lake env lean TestsCvc5/Cvc5FinBaseline.lean
```
