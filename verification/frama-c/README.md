# Frama-C verification of the libz3 C shims

This is an incremental verification target for the **production C source** in
`Blaster/Smt/FFI/c`. It currently checks the variadic AST collector, solver
construction/finalization, and parses all five shim translation units. It does
**not** prove the whole FFI safe.

## Reproduce

Install Frama-C 33.0 with opam (`opam install frama-c.33.0`). Provide the Z3
headers through `Z3_INC_PATH`, `Z3_ROOT`, or `pkg-config z3`:

```sh
Z3_INC_PATH=/path/to/z3/include bash verification/frama-c/check.sh
```

The check runs Eva on `lz3_collect` from the actual `z3_shim_terms.c`, with
concrete Lean arrays of 0, 1, 2, and 3 elements. It explores both outcomes of
`malloc`, validates the output length, element order, distinct values, and
memory accesses in those cases. Frama-C 33.0 reports 16 valid assertions,
29 valid preconditions, and zero alarms. `check.sh` fails if these counts change
or an alarm appears.

The solver harness executes the actual constructor and finalizer. Its Lean/Z3
stubs model reference-count calls and allow failures in simplifier creation,
simplifier installation, and `malloc`. The analysis checks that a successful
solver retains one reference until finalization, and every path ends with zero
solver/simplifier references and exactly one Context decrement. Eva reports
9 valid assertions, 3 valid preconditions, and zero alarms. This proves the
shim's balance **relative to the stubbed API behavior**; it does not prove Z3's
internal reference implementation or Lean's actual finalizer scheduling.

The C parser cannot consume Lean 4.24.0's `_Atomic` runtime header directly.
`model/lean/lean.h` therefore shadows it for analysis only. It models the
observable behavior of the three Lean APIs used by the collector: array size,
array access, and external data access. Its `lean_object` fields represent API
semantics, **not** Lean's physical layout. The production build still uses the
real Lean and Z3 headers. The Z3 header in the analysis is real.

The collector now guards multiplication and the `unsigned` length passed to
Z3, and propagates allocation failure as a Lean IO error. The solver box also
checks allocation failure and releases the Z3 solver reference on that path.
Separately, the format string for `Z3_get_symbol_int` now matches its `int`
return type.

## Open proof obligations

- Eva's current harness is bounded to four array lengths. It is not a proof
  for arbitrary lengths.
- WP with Alt-Ergo proves 34 of 43 generated goals for `lz3_collect`; nine
  time out. Frama-C 33.0 reports that allocation and danglingness in its
  `malloc` specification are not yet implemented in the selected WP model.
  Run this experiment with
  `bash verification/frama-c/run.sh -wp -wp-rte -wp-fct lz3_collect -wp-prover alt-ergo -wp-timeout 5 Blaster/Smt/FFI/c/z3_shim_terms.c`.
- The other shims still contain unchecked `malloc` calls, including datatype
  arrays and solver assumption arrays. Their Lean array shape assumptions, Z3 handle
  lifetimes, and reference balances need separate contracts and proof harnesses.
- Frama-C treats Lean and Z3 implementations as external. Their contracts must
  be justified against those libraries; this analysis cannot prove the
  libraries themselves.
