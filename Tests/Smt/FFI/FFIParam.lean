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
+ E-matching. A falsifiable model-CONSTRUCTION goal such as `xs = []` was measured to return
`Undetermined` via FFI where the `.smtlib` subprocess answers instantly; the FFI backend
currently ignores `.setOption` (`Session.lean:126`), so the emitted `:smt.mbqi` /
`:smt.macro_finder` never reach the solver — root cause not isolated here, tracked separately
as the engine-params work, not parametric-datatype support.)
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
#blaster [∀ (x : Int) (xs ys : List Int), x :: xs = x :: ys → xs = ys]  -- legacy `.smtlib` parity control

/-! ## Head-field injectivity: `x :: xs = y :: xs → x = y` -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster [∀ (x y : Int) (xs : List Int), x :: xs = y :: xs → x = y]  -- legacy `.smtlib` parity control

end Test.FFIParam
