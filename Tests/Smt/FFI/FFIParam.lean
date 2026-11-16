import Blaster
/-!
# End-to-end `#blaster (backend: ffi)` over a PARAMETRIC datatype (`List Int`)

Each goal below is proved through the ENTIRE in-process Z3 FFI pipeline, now including
a PARAMETRIC datatype: `List Int` emits

```
(declare-datatype @List (par (|@α|) ((List.nil) (List.cons (List.cons.0 |@α|) (List.cons.1 (@List |@α|))))))
```

which the FFI backend builds via `Z3_mk_polymorphic_datatype`, instantiates at `(@List Int)`
via `Z3_mk_datatype_sort`, and whose constructors/accessors/recognizers are resolved to the
monomorphized func_decls per use site. Before this, the FFI backend threw
"parametric datatype … pending".

As in `FFIEndToEnd`, every goal is pinned with TWO results proving the SMT solver did the work:

* `(only-optimize: 1)` ⇒ `⚠️ Undetermined` — the pre-SMT optimizer alone CANNOT close it.
* `(backend: ffi)` ⇒ `✅ Valid` — the in-process FFI Z3 (with the parametric datatype) closes it.

Both goals exercise the APPLIED constructor path (`x :: xs` ⇒ `.AppTerm (.QualifiedIdent
List.cons (@List Int)) …`) and the datatype qualifier's accessors/recognizers; the second
also relies on head-field injectivity. (Both are VALID/unsat, provable by the datatype theory
+ E-matching.)

A falsifiable model-CONSTRUCTION goal such as `∀ xs, xs = []` previously returned
`Undetermined` (in fact it DIVERGED with no timeout) via FFI where the `.smtlib` subprocess
answers instantly. Root cause: the FFI backend ignored `.setOption`, so the engine params
`setDefaultSmtOptions` emits (`auto_config false` / `smt.macro_finder true` / `smt.mbqi` /
`smt.pull_nested_quantifiers`) never reached the in-process solver. With those params now
installed as process-global `Z3_global_param_set` values in `Z3Session.create`, the FFI
backend model-constructs the counterexample and returns `❌ Falsified`, matching legacy — see
the goal at the end of this file.
-/
namespace Test.FFIParam

/-! ## Constructor injectivity (tail): `x :: xs = x :: ys → xs = ys` -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x : Int) (xs ys : List Int), x :: xs = x :: ys → xs = ys]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x : Int) (xs ys : List Int), x :: xs = x :: ys → xs = ys]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: smtlib) [∀ (x : Int) (xs ys : List Int), x :: xs = x :: ys → xs = ys]  -- legacy `.smtlib` parity control

/-! ## Head-field injectivity: `x :: xs = y :: xs → x = y` -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: smtlib) [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]  -- legacy `.smtlib` parity control

/-! ## Falsifiable model-CONSTRUCTION goal: `∀ xs, xs = []` (engine-params payoff)

Refuting this requires the solver to CONSTRUCT a witness `xs ≠ []` over the recursive
`List Int` datatype (a bounded model of `@isList`). Before the engine params reached the
FFI solver this diverged (→ `Undetermined`); with `auto_config false` + `smt.macro_finder`
now installed in the session, FFI returns `❌ Falsified` — matching the legacy subprocess. -/

/-- error: ❌ Falsified -/
#guard_msgs (error) in
#blaster (backend: ffi) (gen-cex: 0) [∀ (xs : List Int), xs = []]

/-- error: ❌ Falsified -/
#guard_msgs (error) in
#blaster (backend: smtlib) (gen-cex: 0) [∀ (xs : List Int), xs = []]  -- legacy `.smtlib` parity control

end Test.FFIParam
