# Frama-C verification of the libz3 C shims

This is an incremental verification target for the **production C source** in
`Blaster/Smt/FFI/c`. It currently checks the variadic AST collector, solver
construction/finalization, solver assumption collection, datatype array
preflight and constructor lifetimes, quantifier allocations, and parses all
five shim translation units. It does **not** prove the whole FFI safe.

## Reproduce

Install Frama-C 33.0 with opam (`opam install frama-c.33.0`). Provide the Z3
headers through `Z3_INC_PATH`, `Z3_ROOT`, or `pkg-config z3`:

```sh
Z3_INC_PATH=/path/to/z3/include bash verification/frama-c/check.sh
```

The `ci-frama-c` workflow runs this command on pull requests with Frama-C 33.0,
Alt-Ergo, and the same Z3 5.4.0 headers used by the Linux build.

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

The assumption harness runs the production `solverCheckAssuming` shim for
arrays of 0, 1, and 3 ASTs, and an overflowing length. Its Z3 stub checks the
forwarded count and order; its Lean stubs check that the solver and assumption
array are each released once on success and allocation failure. Eva reports
18 valid assertions, 7 valid preconditions, and zero alarms.

The quantifier harness runs the production `mkQuantConst` shim six times:
success and a failure at each of five C allocations. It verifies that each
allocated buffer is freed, all six owned Lean arguments are decremented, and
the result is correct for the path. Eva reports zero alarms and no unknown
properties in all six runs. The injected failure is the only source of
allocation failure in this harness (`-eva-no-alloc-returns-null`).

The datatype harness runs the production shape checks against matching arrays,
an inner field-count mismatch, an out-of-group recursive reference, an outer
sort-count mismatch, and an overflowing constructor count. Eva reports
7 valid assertions, 51 valid preconditions, and zero alarms. The checks run at
the entry of all four datatype constructors before any indexed array access.
`Tests/Smt/FFI/FFIShapeGuards.lean` also checks that malformed calls return Lean
IO errors with the actual runtime.

Two lifecycle harnesses execute all four production datatype constructors with
failed C allocations and failed Z3 creation or query calls. The single and
recursive modes check six allocation sites each, constructor creation,
datatype creation, and constructor-query failure. The polymorphic mode checks
five allocation sites and both creation calls. Eva reports respectively 13/67,
14/77, and 13/74 valid assertions/preconditions, with zero alarms. The mutual
harness uses two sorts and checks thirteen allocation sites, both constructor
and constructor-list creation points, datatype creation, and either query
failure; Eva reports 16 valid assertions, 142 valid preconditions, and zero
alarms. They check that every
created constructor/list is deleted exactly once and every owned Lean argument
is decremented once. The mutual analysis uses `-eva-mlevel 20` to keep the
allocator's live blocks distinct.

WP with Alt-Ergo proves all 8 goals for the general numeric `lz3_count_fits`
contract, including its runtime-error guard. WP does not yet prove the nested
array shape functions: those need explicit Lean array validity and framing
contracts. A first attempt without those contracts generated 49 goals with
unproved API preconditions, so it is not counted as a proof of the functions.
WP also proves 3 of 3 goals for the allocation-size arithmetic in `lz3_alloc`,
and 3 of 3 for `lz3_term_alloc`, including their runtime-error guards.
Frama-C's current `malloc` model leaves the
returned block's validity and lifetime outside that result.

WP also proves 55 of 55 goals for the production mutual-constructor cleanup
under the event model in `wp_mutual_lifecycle.c`, with the prover cache disabled.
Its preconditions cover the array bounds, and its loop invariants prove
termination and that the number of constructor deletions equals an audit
expectation incremented by each `created_per[s]`, while the number of list
deletions equals `lists_created`, for arbitrary admitted counts. The model's
Z3 destructor stubs increment audit counters and its `free` stub is a no-op.
This verifies the shim's deletion control flow; it does not establish that
every handle is distinct, was created successfully, or is actually freed by Z3.

The C parser cannot consume Lean 4.24.0's `_Atomic` runtime header directly.
`model/lean/lean.h` therefore shadows it for analysis only. It models the
observable behavior of the three Lean APIs used by the collector: array size,
array access, and external data access. Its `lean_object` fields represent API
semantics, **not** Lean's physical layout. The production build still uses the
real Lean and Z3 headers. The Z3 header in the analysis is real.

The collector now guards multiplication and the `unsigned` length passed to
Z3, and propagates allocation failure as a Lean IO error. The solver box also
checks allocation failure and releases the Z3 solver reference on that path.
`solverCheckAssuming` checks the allocation and Z3's `unsigned` count. The
datatype constructors reject mismatched nested arrays, invalid recursive
references, and count overflow before passing them to Z3. They now allocate
reusable field buffers before constructing Z3 objects and release all created
constructors and constructor lists on creation failure.
Constructor queries now fill temporary C buffers; an error is returned before
creating any Lean result array. The term shims check all their temporary C
allocations and reject counts that exceed Z3's `unsigned` API or overflow the
allocation size.
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
- The datatype lifecycle harnesses exercise one-constructor single, recursive,
  and polymorphic cases, plus a two-sort mutual case. Arbitrary constructor
  counts are covered by the mutual cleanup's deletion-count proof, but the
  creation loops and per-handle uniqueness still need WP contracts and loop
  invariants. Full allocation lifetimes need a heap model. Other Z3 API calls
  can fail independently of the modeled scenarios.
- Frama-C treats Lean and Z3 implementations as external. Their contracts must
  be justified against those libraries; this analysis cannot prove the
  libraries themselves.
