# Z3 FFI Backend Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace Lean-blaster's string/subprocess Z3 pipeline with an in-process binding that builds Z3 AST objects directly via the Z3 C API and solves in-process.

**Architecture:** A self-contained C shim (`Blaster/Smt/FFI/c/`) exposes the subset of the Z3 C API the translator needs, wrapped by `@[extern]` Lean bindings (`Blaster/Smt/FFI/`). A `BuildM` interpreter turns the existing `SmtCommand`/`SmtTerm` AST into `Z3_ast`/`Z3_sort` objects inside a per-query `Z3Session` (a non-refcounted `Z3_context` + `Z3_solver`). The existing Lean→SMT translation is unchanged; only the *consumer* of the AST changes. A backend switch keeps the old string path working until FFI reaches parity, then the old path is deleted.

**Tech Stack:** Lean 4 (v4.24.0), Z3 C API (libz3 4.15.4), Lake FFI (`input_file`/`target`/`extern_lib`), C11.

---

## Scope Reconciliation With Spec

The approved spec (§4, §10) lists **BitVec** among phase-1 sorts. **`main` does not implement BitVec/Fin/SMTArray** — that redesign lives on a separate branch and is not present on `feat/z3-ffi-migration`. The operators the translator actually emits on this branch are:

- **Sorts:** `Bool`, `Int`, `Nat` (alias → `Int`), `String`, `Prop` (defined per-query), `Empty`, `PEmpty`, `Array` (ParamSort), uninterpreted (`declare-sort`), datatypes (`declare-datatype`).
- **Operators:** `and or not => = distinct ite` (bool); `+ - * div mod abs ^ to_int < <=` (arith); `select store` (array); `str.++ str.< str.<= str.len str.replace str.replace_all` (string); `as-array`.
- **define-fun wrappers:** `@Int.ediv @Int.emod @Int.fdiv @Int.fmod @Int.tdiv @Int.tmod @Int.pow @Int.toNat @Nat.pow @Nat.sub` and any others the translator defines at runtime.

This plan implements the above. BitVec/Fin/SMTArray FFI support is **deferred** to whenever those land on `main` (each is a small additive dispatch extension following the same operator pattern). This is the only deviation from the spec; everything else matches.

## File Structure

**Created:**
- `Blaster/Smt/FFI/c/lean_z3.h` — box/unbox macros, IO-result & string helpers, error-check helper.
- `Blaster/Smt/FFI/c/z3_shim_context.c` — config/context/error/interrupt.
- `Blaster/Smt/FFI/c/z3_shim_sorts.c` — sorts.
- `Blaster/Smt/FFI/c/z3_shim_terms.c` — numerals, bool/arith/array/string ops, apply, quantifiers, let-substitution, funcdecl.
- `Blaster/Smt/FFI/c/z3_shim_datatypes.c` — datatype construction.
- `Blaster/Smt/FFI/c/z3_shim_solver.c` — solver assert/check/assumptions/model/params.
- `Blaster/Smt/FFI/Types.lean` — opaque handle types + `@[extern]` lifecycle.
- `Blaster/Smt/FFI/Sorts.lean` — sort-builder externs.
- `Blaster/Smt/FFI/Terms.lean` — term/numeral/op/quantifier/funcdecl externs.
- `Blaster/Smt/FFI/Datatypes.lean` — datatype externs.
- `Blaster/Smt/FFI/Solver.lean` — solver/model/params externs.
- `Blaster/Smt/FFI/BuildEnv.lean` — `BuildM`, build environment maps.
- `Blaster/Smt/FFI/Build.lean` — `buildSort`, `buildTerm`, `runCommand`.
- `Blaster/Smt/FFI/Session.lean` — `Z3Session`, `Session.create/checkSat/checkAssumptions/getModel/close`.
- `Blaster/Smt/FFI.lean` — umbrella import.
- `Tests/Smt/FFI/FFISmoke.lean`, `Tests/Smt/FFI/FFICore.lean`, … — FFI-specific tests.

**Modified:**
- `lakefile.lean` — add shim build targets + link args.
- `Blaster/Optimize/Env.lean:353` — `SmtEnv.smtProc` → add `smtSession : Option Z3Session` (keep `smtProc` during migration).
- `Blaster/Smt/Env.lean` — route `assertTerm`/`checkSat`/`checkSatAssuming`/`getModel`/`setBlasterProcess`/`exitSmt`/option-setters through the FFI session when the FFI backend is selected.
- `Blaster/Smt/Translate.lean:57` — `setBlasterProcess`/`checkSat`/`exitSmt` seam.
- `Blaster/Command/Options.lean` — add a `backend` option (`ffi` default, `smtlib` fallback) during migration.
- `.github/workflows/*.yml` — install libz3.

**Deleted (phase 3, after parity):**
- `Blaster/Smt/EmitCommand.lean`, the reader/process funnels in `Blaster/Smt/Env.lean` (`createBlasterProcess`, `findZ3CmdAndVersion`, `getOutputModel/Eval/Proof`, `getSatResult`, `trySubmitCommand!` process branch), `SmtEnv.smtProc`.

## Prerequisites

- The phase-0 spike (`.../scratchpad/spike/`) is the proven template for C shim + Lean extern + lakefile wiring on v4.24.
- Environment: libz3 at `/opt/homebrew/lib`, headers at `/opt/homebrew/include`. Set `Z3_LIB_PATH`/`Z3_INC_PATH` to override.
- Run all Lean builds with libz3 discoverable: `DYLD_LIBRARY_PATH=/opt/homebrew/lib` (macOS) on the runtime step.

---

# PHASE 1 — Infrastructure + Core Theory

## Task 1: Wire the C shim build into lakefile with a smoke function

**Files:**
- Create: `Blaster/Smt/FFI/c/lean_z3.h`
- Create: `Blaster/Smt/FFI/c/z3_shim_context.c`
- Create: `Blaster/Smt/FFI/Types.lean`
- Create: `Blaster/Smt/FFI.lean`
- Create: `Tests/Smt/FFI/FFISmoke.lean`
- Modify: `lakefile.lean`

- [ ] **Step 1: Write the C header with box/unbox + IO helpers**

`Blaster/Smt/FFI/c/lean_z3.h`:
```c
#ifndef LEAN_Z3_H
#define LEAN_Z3_H
#include <lean/lean.h>
#include <z3.h>

/* Declare a Lean external class + box/unbox for a Z3 handle type.
 * Handles wrapped this way carry a finalizer. AST/sort/funcdecl handles use
 * the no-finalizer variant (see box_owned). */
#define LEAN_Z3_DECLARE_CLASS(name) \
  static lean_external_class *g_##name##_class = NULL; \
  static void name##_finalize(void *p); \
  static void name##_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; } \
  static inline lean_object *box_##name(void *p) { \
    if (!g_##name##_class) g_##name##_class = lean_register_external_class(name##_finalize, name##_foreach); \
    return lean_alloc_external(g_##name##_class, p); \
  } \
  static inline void *unbox_##name(b_lean_obj_arg o) { return lean_get_external_data(o); }

/* No-finalizer external class for context-owned pointers (ast/sort/funcdecl). */
static lean_external_class *g_owned_class = NULL;
static void owned_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static inline lean_object *box_owned(void *p) {
  if (!g_owned_class) g_owned_class = lean_register_external_class(NULL, owned_foreach);
  return lean_alloc_external(g_owned_class, p);
}
static inline void *unbox_owned(b_lean_obj_arg o) { return lean_get_external_data(o); }

static inline lean_obj_res z3_io_ok(lean_object *v) { return lean_io_result_mk_ok(v); }
static inline lean_obj_res z3_io_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

#endif
```

- [ ] **Step 2: Write the context shim with a smoke function**

`Blaster/Smt/FFI/c/z3_shim_context.c`:
```c
#include "lean_z3.h"

static void z3_err_noop(Z3_context c, Z3_error_code e) { (void)c; (void)e; }

LEAN_Z3_DECLARE_CLASS(context)
static void context_finalize(void *p) { if (p) Z3_del_context((Z3_context)p); }

/* smokeCheckTrue : IO UInt32  (2=sat, 0=unsat, 1=unknown) */
LEAN_EXPORT lean_obj_res lean_z3_smoke_check_true(lean_obj_arg w) {
  (void)w;
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_set_error_handler(ctx, z3_err_noop);
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  Z3_solver_assert(ctx, s, Z3_mk_true(ctx));
  Z3_lbool r = Z3_solver_check(ctx, s);
  Z3_solver_dec_ref(ctx, s);
  Z3_del_context(ctx);
  return z3_io_ok(lean_box_uint32((r == Z3_L_TRUE) ? 2u : (r == Z3_L_FALSE ? 0u : 1u)));
}
```

- [ ] **Step 3: Write the Lean binding + umbrella import**

`Blaster/Smt/FFI/Types.lean`:
```lean
namespace Blaster.Smt.FFI

@[extern "lean_z3_smoke_check_true"]
opaque smokeCheckTrue : IO UInt32

end Blaster.Smt.FFI
```

`Blaster/Smt/FFI.lean`:
```lean
import Blaster.Smt.FFI.Types
```

- [ ] **Step 4: Add shim build targets to lakefile.lean**

Replace `lakefile.lean` contents with:
```lean
import Lake
open Lake DSL System

private unsafe def z3LinkArgsImpl : Array String :=
  let libPath := match unsafeBaseIO (IO.getEnv "Z3_LIB_PATH") with
    | some p => p | none => "/opt/homebrew/lib"
  #[s!"-L{libPath}", "-lz3"]
@[implemented_by z3LinkArgsImpl]
private opaque z3LinkArgs : Array String := #["-lz3"]

package «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]
  moreLinkArgs := z3LinkArgs

def cWeakArgs : FetchM (Array String) := do
  let leanInc := (← getLeanIncludeDir).toString
  let mut args := #["-I", leanInc, "-I/opt/homebrew/include", "-I", "Blaster/Smt/FFI/c"]
  if let some inc ← IO.getEnv "Z3_INC_PATH" then args := args.push s!"-I{inc}"
  return args

input_file «z3_shim_context.c» where
  path := "Blaster/Smt/FFI/c/z3_shim_context.c"
  text := true

target «z3_shim_context.o» (pkg : NPackage _package.name) : FilePath := do
  let o := pkg.buildDir / "ffi" / "z3_shim_context.o"
  buildO o (← «z3_shim_context.c».fetch) (← cWeakArgs) #["-O2"]

extern_lib «libz3shim» (pkg : NPackage _package.name) := do
  let oCtx ← «z3_shim_context.o».fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "z3shim") #[oCtx]

@[default_target]
lean_lib «Blaster» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--threads=4"]

lean_exe z3check where
  root := `Z3Check
```

- [ ] **Step 5: Write the smoke test (elaboration-time, the `#blaster` mode)**

`Tests/Smt/FFI/FFISmoke.lean`:
```lean
import Blaster.Smt.FFI

open Blaster.Smt.FFI

/-- info: FFI check-sat(true) = 2 -/
#guard_msgs in
#eval do IO.println s!"FFI check-sat(true) = {← smokeCheckTrue}"
```

- [ ] **Step 6: Build and verify FFI works at elaboration time inside Blaster**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Blaster && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake env lean --load-dynlib=.lake/build/lib/libz3shim.dylib Tests/Smt/FFI/FFISmoke.lean`
Expected: no errors; `#guard_msgs` passes. Then confirm auto-load via the lib path:
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests`
Expected: builds; the `#eval` prints `FFI check-sat(true) = 2`.

- [ ] **Step 7: Verify the existing suite still builds (no regression)**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: `Build completed successfully`.

- [ ] **Step 8: Commit**

```bash
git add lakefile.lean Blaster/Smt/FFI Blaster/Smt/FFI.lean Tests/Smt/FFI/FFISmoke.lean
git commit -m "feat(ffi): wire Z3 C shim into lakefile with smoke check"
```

---

## Task 2: Opaque handle types + context/solver lifecycle

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_context.c`
- Create: `Blaster/Smt/FFI/c/z3_shim_solver.c`
- Modify: `Blaster/Smt/FFI/Types.lean`
- Create: `Blaster/Smt/FFI/Solver.lean`
- Modify: `Blaster/Smt/FFI.lean`, `lakefile.lean`
- Test: `Tests/Smt/FFI/FFISmoke.lean`

- [ ] **Step 1: Add context lifecycle shims (create with error handler, del)**

Append to `Blaster/Smt/FFI/c/z3_shim_context.c`:
```c
/* mkContext : IO Context */
LEAN_EXPORT lean_obj_res lean_z3_mk_context(lean_obj_arg w) {
  (void)w;
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_set_error_handler(ctx, z3_err_noop);
  return z3_io_ok(box_context((void *)ctx));
}

/* ctxErrorCode : Context → IO UInt32 (0 == OK) */
LEAN_EXPORT lean_obj_res lean_z3_ctx_error_code(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w;
  return z3_io_ok(lean_box_uint32((uint32_t)Z3_get_error_code((Z3_context)unbox_context(c))));
}

/* ctxErrorMsg : Context → UInt32 → IO String */
LEAN_EXPORT lean_obj_res lean_z3_ctx_error_msg(b_lean_obj_arg c, uint32_t code, lean_obj_arg w) {
  (void)w;
  Z3_string m = Z3_get_error_msg((Z3_context)unbox_context(c), (Z3_error_code)code);
  return z3_io_ok(lean_mk_string(m ? m : ""));
}
```

- [ ] **Step 2: Add solver lifecycle shims**

`Blaster/Smt/FFI/c/z3_shim_solver.c`:
```c
#include "lean_z3.h"

LEAN_Z3_DECLARE_CLASS(solver)
/* finalizer needs the context; we store a {ctx,solver} pair. */
typedef struct { Z3_context ctx; Z3_solver s; } z3_solver_box;
static void solver_finalize(void *p) {
  z3_solver_box *b = (z3_solver_box *)p;
  if (b) { Z3_solver_dec_ref(b->ctx, b->s); free(b); }
}

/* mkSolver : Context → IO Solver */
LEAN_EXPORT lean_obj_res lean_z3_mk_solver(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)unbox_context(c);
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  z3_solver_box *b = (z3_solver_box *)malloc(sizeof(z3_solver_box));
  b->ctx = ctx; b->s = s;
  return z3_io_ok(box_solver(b));
}
```

NOTE: `unbox_context` is defined in `z3_shim_context.c`; declare it `extern` at the top of `z3_shim_solver.c`:
```c
extern void *unbox_context(lean_object *o);
```
Change `z3_shim_context.c`'s `unbox_context` from `static inline` to a non-static exported helper so it can be shared:
in `lean_z3.h`, keep the macro's `unbox_##name` as `static inline`, but ALSO add to `z3_shim_context.c` a non-static wrapper:
```c
void *ctx_ptr(lean_object *o) { return unbox_context(o); }
```
and in `z3_shim_solver.c` use `ctx_ptr`. (Simpler than sharing statics across translation units.)

- [ ] **Step 3: Add Lean opaque types + externs**

Replace `Blaster/Smt/FFI/Types.lean`:
```lean
namespace Blaster.Smt.FFI

opaque ContextPointed : NonemptyType
def Context : Type := ContextPointed.type
instance : Nonempty Context := ContextPointed.property

opaque SolverPointed : NonemptyType
def Solver : Type := SolverPointed.type
instance : Nonempty Solver := SolverPointed.property

@[extern "lean_z3_smoke_check_true"] opaque smokeCheckTrue : IO UInt32
@[extern "lean_z3_mk_context"]      opaque mkContext : IO Context
@[extern "lean_z3_ctx_error_code"]  opaque Context.errorCode : Context → IO UInt32
@[extern "lean_z3_ctx_error_msg"]   opaque Context.errorMsg : Context → UInt32 → IO String

end Blaster.Smt.FFI
```

`Blaster/Smt/FFI/Solver.lean`:
```lean
import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_solver"] opaque Context.mkSolver : Context → IO Solver

end Blaster.Smt.FFI
```

- [ ] **Step 4: Register the solver .o + import**

In `lakefile.lean`, add an `input_file`/`target` for `z3_shim_solver.c` (copy the context pattern) and add `«z3_shim_solver.o».fetch` to the `extern_lib` `buildStaticLib` array. Add `import Blaster.Smt.FFI.Solver` to `Blaster/Smt/FFI.lean`.

- [ ] **Step 5: Extend smoke test**

Append to `Tests/Smt/FFI/FFISmoke.lean`:
```lean
/-- info: ctx ok, err=0 -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let _s ← ctx.mkSolver
  IO.println s!"ctx ok, err={← ctx.errorCode}"
```

- [ ] **Step 6: Build + run**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; the new `#eval` prints `ctx ok, err=0`.

- [ ] **Step 7: Commit**

```bash
git add -A && git commit -m "feat(ffi): context + solver lifecycle bindings"
```

---

## Task 3: BuildM monad and build environment

**Files:**
- Create: `Blaster/Smt/FFI/BuildEnv.lean`
- Modify: `Blaster/Smt/FFI.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Write a test that constructs and reads the env (compile-only)**

`Tests/Smt/FFI/FFICore.lean`:
```lean
import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt

/-- info: env-empty -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let st ← BuildState.mk ctx
  IO.println s!"env-{if st.sorts.isEmpty then "empty" else "nonempty"}"
```

- [ ] **Step 2: Run to verify failure**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -i "BuildState"`
Expected: FAIL — `unknown identifier BuildState`.

- [ ] **Step 3: Implement BuildEnv**

`Blaster/Smt/FFI/BuildEnv.lean`:
```lean
import Blaster.Smt.FFI.Types
import Blaster.Smt.FFI.Solver
import Blaster.Smt.Syntax

namespace Blaster.Smt.FFI
open Blaster.Smt

/-- A defined-function macro: parameters + the raw SmtTerm body, to inline at apply sites. -/
structure MacroDef where
  params : Array SmtSymbol
  body   : SmtTerm

/-- Mutable build environment mapping SMT names to Z3 handles. -/
structure BuildState where
  ctx      : Context
  sorts    : Std.HashMap SmtSymbol Sort            -- declared/aliased sorts
  consts   : Std.HashMap SmtSymbol Ast             -- 0-ary constants
  funcs    : Std.HashMap SmtSymbol FuncDecl        -- uninterpreted functions
  macros   : Std.HashMap SmtSymbol MacroDef        -- inlined define-funs
  recFuncs : Std.HashMap SmtSymbol FuncDecl        -- Z3_add_rec_def functions
  /-- scoped local bindings (let + quantifier vars), innermost last -/
  locals   : Array (SmtSymbol × Ast)

def BuildState.mk (ctx : Context) : IO BuildState := return {
  ctx, sorts := {}, consts := {}, funcs := {}, macros := {}, recFuncs := {}, locals := #[] }

abbrev BuildM := StateRefT BuildState IO

def BuildM.run (ctx : Context) (m : BuildM α) : IO α := do
  let st ← BuildState.mk ctx
  (·.1) <$> m.run st

/-- Look up a local binding by symbol (searches innermost-first). -/
def lookupLocal (s : SmtSymbol) : BuildM (Option Ast) := do
  let locals := (← get).locals
  return locals.findSomeRev? (fun (k, v) => if k == s then some v else none)

end Blaster.Smt.FFI
```

NOTE: `Sort`, `Ast`, `FuncDecl` opaque types are added in Task 4/6; for this task add temporary stubs to `Types.lean`:
```lean
opaque SortPointed : NonemptyType
def Sort : Type := SortPointed.type
instance : Nonempty Sort := SortPointed.property
opaque AstPointed : NonemptyType
def Ast : Type := AstPointed.type
instance : Nonempty Ast := AstPointed.property
opaque FuncDeclPointed : NonemptyType
def FuncDecl : Type := FuncDeclPointed.type
instance : Nonempty FuncDecl := FuncDeclPointed.property
```

- [ ] **Step 4: Add import + build**

Add `import Blaster.Smt.FFI.BuildEnv` to `Blaster/Smt/FFI.lean`.
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; prints `env-empty`.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): BuildM monad + build environment"
```

---

## Task 4: Sort building

**Files:**
- Create: `Blaster/Smt/FFI/c/z3_shim_sorts.c`
- Create: `Blaster/Smt/FFI/Sorts.lean`
- Create: `Blaster/Smt/FFI/Build.lean` (buildSort only)
- Modify: `lakefile.lean`, `Blaster/Smt/FFI.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Write the sort shims**

`Blaster/Smt/FFI/c/z3_shim_sorts.c`:
```c
#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkBoolSort : Context → IO Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_bool_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_bool_sort((Z3_context)ctx_ptr(c))));
}
/* mkIntSort : Context → IO Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_int_sort((Z3_context)ctx_ptr(c))));
}
/* mkStringSort : Context → IO Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_string_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_string_sort((Z3_context)ctx_ptr(c))));
}
/* mkArraySort : Context → Sort(domain) → Sort(range) → IO Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_array_sort(b_lean_obj_arg c, b_lean_obj_arg d, b_lean_obj_arg r, lean_obj_arg w) {
  (void)w;
  return z3_io_ok(box_owned(Z3_mk_array_sort((Z3_context)ctx_ptr(c),
    (Z3_sort)unbox_owned(d), (Z3_sort)unbox_owned(r))));
}
/* mkUninterpretedSort : Context → String → IO Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_uninterp_sort(b_lean_obj_arg c, b_lean_obj_arg name, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  return z3_io_ok(box_owned(Z3_mk_uninterpreted_sort(ctx, sym)));
}
```

- [ ] **Step 2: Write the Lean externs**

`Blaster/Smt/FFI/Sorts.lean`:
```lean
import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_bool_sort"]     opaque Context.mkBoolSort   : Context → IO Sort
@[extern "lean_z3_mk_int_sort"]      opaque Context.mkIntSort    : Context → IO Sort
@[extern "lean_z3_mk_string_sort"]   opaque Context.mkStringSort : Context → IO Sort
@[extern "lean_z3_mk_array_sort"]    opaque Context.mkArraySort  : Context → Sort → Sort → IO Sort
@[extern "lean_z3_mk_uninterp_sort"] opaque Context.mkUninterpSort : Context → String → IO Sort

end Blaster.Smt.FFI
```

- [ ] **Step 3: Implement `buildSort` in Build.lean**

`Blaster/Smt/FFI/Build.lean`:
```lean
import Blaster.Smt.FFI.Sorts
import Blaster.Smt.FFI.BuildEnv
import Blaster.Smt.Term

namespace Blaster.Smt.FFI
open Blaster.Smt

/-- Translate a SortExpr into a Z3 sort, resolving Nat→Int, Prop→Bool, and
    declared/aliased sorts via the build env. -/
partial def buildSort (se : SortExpr) : BuildM Sort := do
  let ctx := (← get).ctx
  match se with
  | .SymbolSort nm =>
      match nm with
      | .ReservedSymbol "Int"    => ctx.mkIntSort
      | .ReservedSymbol "Nat"    => ctx.mkIntSort         -- Nat aliases Int
      | .ReservedSymbol "Bool"   => ctx.mkBoolSort
      | .ReservedSymbol "Prop"   => ctx.mkBoolSort        -- Prop modelled as Bool
      | .ReservedSymbol "String" => ctx.mkStringSort
      | _ =>
        match (← get).sorts.get? nm with
        | some s => return s
        | none =>
            -- unknown symbol sort → uninterpreted, registered for reuse
            let s ← ctx.mkUninterpSort nm.toString
            modify fun st => { st with sorts := st.sorts.insert nm s }
            return s
  | .ParamSort (.ReservedSymbol "Array") ps =>
      if h : ps.size == 2 then
        let d ← buildSort ps[0]!
        let r ← buildSort ps[1]!
        ctx.mkArraySort d r
      else throw (IO.userError s!"buildSort: Array expects 2 params, got {ps.size}")
  | .ParamSort nm _ =>
      -- parameterized non-Array sort: resolve as a declared/aliased sort
      match (← get).sorts.get? nm with
      | some s => return s
      | none => throw (IO.userError s!"buildSort: unknown parameterized sort {nm.toString}")

end Blaster.Smt.FFI
```

- [ ] **Step 4: Register .o + imports; add a round-trip test**

Add `z3_shim_sorts.c`/`.o` to `lakefile.lean` and the extern_lib array; add `import Blaster.Smt.FFI.Sorts` and `import Blaster.Smt.FFI.Build` to `Blaster/Smt/FFI.lean`.

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
/-- info: sorts-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildSort Blaster.Smt.intSort
    let _ ← buildSort Blaster.Smt.boolSort
    let _ ← buildSort (Blaster.Smt.arraySort #[Blaster.Smt.intSort, Blaster.Smt.boolSort])
    IO.println "sorts-ok"
```

- [ ] **Step 5: Build + run**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; prints `sorts-ok`.

- [ ] **Step 6: Commit**

```bash
git add -A && git commit -m "feat(ffi): sort building (Int/Bool/String/Array/uninterp)"
```

---

## Task 5: Numeral & literal terms

**Files:**
- Create: `Blaster/Smt/FFI/c/z3_shim_terms.c`
- Create: `Blaster/Smt/FFI/Terms.lean`
- Modify: `Blaster/Smt/FFI/Build.lean` (buildTerm — literals only)
- Modify: `lakefile.lean`, `Blaster/Smt/FFI.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Write numeral shims**

`Blaster/Smt/FFI/c/z3_shim_terms.c`:
```c
#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkNumeralInt : Context → String(decimal) → Sort → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_numeral(b_lean_obj_arg c, b_lean_obj_arg num, b_lean_obj_arg srt, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  return z3_io_ok(box_owned(Z3_mk_numeral(ctx, lean_string_cstr(num), (Z3_sort)unbox_owned(srt))));
}
/* mkBool : Context → Bool → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_bool(b_lean_obj_arg c, uint8_t b, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  return z3_io_ok(box_owned(b ? Z3_mk_true(ctx) : Z3_mk_false(ctx)));
}
/* mkString : Context → String → IO Ast  (SMT-LIB string literal, no surrounding quotes) */
LEAN_EXPORT lean_obj_res lean_z3_mk_string(b_lean_obj_arg c, b_lean_obj_arg s, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  return z3_io_ok(box_owned(Z3_mk_string(ctx, lean_string_cstr(s))));
}
```

- [ ] **Step 2: Lean externs**

`Blaster/Smt/FFI/Terms.lean`:
```lean
import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_numeral"] opaque Context.mkNumeral : Context → String → Sort → IO Ast
@[extern "lean_z3_mk_bool"]    opaque Context.mkBool    : Context → Bool → IO Ast
@[extern "lean_z3_mk_string"]  opaque Context.mkStringLit : Context → String → IO Ast

end Blaster.Smt.FFI
```

- [ ] **Step 3: `buildTerm` literal cases in Build.lean**

Add to `Blaster/Smt/FFI/Build.lean`:
```lean
/-- Strip the surrounding quotes the translator adds to string literals (see strLitSmt). -/
private def unquote (s : String) : String :=
  if s.length ≥ 2 && s.front == '"' && s.back == '"' then (s.drop 1).dropRight 1 else s

mutual
partial def buildTerm (t : SmtTerm) : BuildM Ast := do
  let ctx := (← get).ctx
  match t with
  | .NumTerm n  => ctx.mkNumeral (toString n) (← ctx.mkIntSort)
  | .DecTerm s  => ctx.mkNumeral s (← buildRealSort)   -- see NOTE below
  | .BoolTerm b => ctx.mkBool b
  | .StrTerm s  => ctx.mkStringLit (unquote s)
  | _ => throw (IO.userError s!"buildTerm: unhandled term (added in later tasks)")
end
```
NOTE: `DecTerm` is a rational literal. Real sort is not otherwise used on this branch; add a `Context.mkRealSort` extern mirroring `mkIntSort` (`Z3_mk_real_sort`) and a `buildRealSort` helper only if any test exercises `DecTerm`. If none does, replace the `.DecTerm` arm with `throw (IO.userError "DecTerm unsupported")` and revisit if a test needs it. (Grep first: `grep -rn "DecTerm" Blaster Tests`.)

- [ ] **Step 4: Register .o + imports; add a check-sat-with-numeral test using solver from Task 9's precursor**

For now test literal construction compiles/executes:
Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
/-- info: lits-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildTerm (.NumTerm 42)
    let _ ← buildTerm (.BoolTerm true)
    let _ ← buildTerm (.StrTerm "\"hi\"")
    IO.println "lits-ok"
```

- [ ] **Step 5: Build + run**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; prints `lits-ok`.

- [ ] **Step 6: Commit**

```bash
git add -A && git commit -m "feat(ffi): numeral/bool/string literal terms"
```

---

## Task 6: Constants, function declarations, and application dispatch skeleton

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_terms.c`, `Blaster/Smt/FFI/Terms.lean`, `Blaster/Smt/FFI/Build.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Add const/func-decl/apply shims**

Append to `z3_shim_terms.c`:
```c
/* mkConst : Context → String → Sort → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_const(b_lean_obj_arg c, b_lean_obj_arg name, b_lean_obj_arg srt, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  return z3_io_ok(box_owned(Z3_mk_const(ctx, sym, (Z3_sort)unbox_owned(srt))));
}
/* mkFuncDecl : Context → String → Array Sort(domain) → Sort(range) → IO FuncDecl */
LEAN_EXPORT lean_obj_res lean_z3_mk_func_decl(b_lean_obj_arg c, b_lean_obj_arg name,
    b_lean_obj_arg dom, b_lean_obj_arg rng, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  size_t n = lean_array_size(dom);
  Z3_sort *ds = (Z3_sort *)malloc(sizeof(Z3_sort) * (n ? n : 1));
  for (size_t i = 0; i < n; i++) ds[i] = (Z3_sort)unbox_owned(lean_array_get_core(dom, i));
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  Z3_func_decl fd = Z3_mk_func_decl(ctx, sym, (unsigned)n, ds, (Z3_sort)unbox_owned(rng));
  free(ds);
  return z3_io_ok(box_owned(fd));
}
/* mkApp : Context → FuncDecl → Array Ast → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_app(b_lean_obj_arg c, b_lean_obj_arg fd, b_lean_obj_arg args, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  size_t n = lean_array_size(args);
  Z3_ast *as = (Z3_ast *)malloc(sizeof(Z3_ast) * (n ? n : 1));
  for (size_t i = 0; i < n; i++) as[i] = (Z3_ast)unbox_owned(lean_array_get_core(args, i));
  Z3_ast r = Z3_mk_app(ctx, (Z3_func_decl)unbox_owned(fd), (unsigned)n, as);
  free(as);
  return z3_io_ok(box_owned(r));
}
```

- [ ] **Step 2: Lean externs**

Append to `Terms.lean`:
```lean
@[extern "lean_z3_mk_const"]     opaque Context.mkConst    : Context → String → Sort → IO Ast
@[extern "lean_z3_mk_func_decl"] opaque Context.mkFuncDecl : Context → String → Array Sort → Sort → IO FuncDecl
@[extern "lean_z3_mk_app"]       opaque Context.mkApp      : Context → FuncDecl → Array Ast → IO Ast
```

- [ ] **Step 3: `buildTerm` identifier/apply cases + `runCommand` for declareConst/declareFun**

Add to `Build.lean` (inside the `mutual` block from Task 5):
```lean
partial def buildIdent (nm : SmtQualifiedIdent) : BuildM Ast := do
  let sym := match nm with | .SimpleIdent s => s | .QualifiedIdent s _ => s
  -- 1. local (let / quantifier) binding
  if let some a ← lookupLocal sym then return a
  -- 2. declared constant
  if let some a := (← get).consts.get? sym then return a
  -- 3. 0-ary macro (define-fun with no params) — inline
  if let some m := (← get).macros.get? sym then
    if m.params.isEmpty then return (← buildTerm m.body)
  throw (IO.userError s!"buildIdent: unbound identifier {sym.toString}")

partial def buildApp (nm : SmtQualifiedIdent) (args : Array SmtTerm) : BuildM Ast := do
  let sym := match nm with | .SimpleIdent s => s | .QualifiedIdent s _ => s
  -- built-in operators handled in Task 7 via `buildBuiltin?`
  if let some a ← buildBuiltin? sym args then return a
  -- macro inline
  if let some m := (← get).macros.get? sym then return (← inlineMacro m args)
  -- rec-def or uninterpreted function application
  let argAsts ← args.mapM buildTerm
  if let some fd := (← get).recFuncs.get? sym then return (← (← get).ctx.mkApp fd argAsts)
  if let some fd := (← get).funcs.get? sym then return (← (← get).ctx.mkApp fd argAsts)
  throw (IO.userError s!"buildApp: unbound function {sym.toString}")
```
Extend `buildTerm`'s match with:
```lean
  | .SmtIdent nm => buildIdent nm
  | .AppTerm nm args => buildApp nm args
```
Add stubs (real impls in Task 7 & Task 13):
```lean
partial def buildBuiltin? (_sym : SmtSymbol) (_args : Array SmtTerm) : BuildM (Option Ast) := return none
partial def inlineMacro (_m : MacroDef) (_args : Array SmtTerm) : BuildM Ast :=
  throw (IO.userError "inlineMacro: implemented in Task 13")
```

Add `runCommand` (partial — grows across tasks) in a new section:
```lean
partial def runCommand (c : SmtCommand) : BuildM Unit := do
  let ctx := (← get).ctx
  match c with
  | .declareConst nm t =>
      let s ← buildSort t
      let a ← ctx.mkConst nm.toString s
      modify fun st => { st with consts := st.consts.insert nm a }
  | .declareFun nm dom rng =>
      let ds ← dom.mapM buildSort
      let r ← buildSort rng
      let fd ← ctx.mkFuncDecl nm.toString ds r
      modify fun st => { st with funcs := st.funcs.insert nm fd }
  | .declareSort nm _arity =>
      let s ← ctx.mkUninterpSort nm.toString
      modify fun st => { st with sorts := st.sorts.insert nm s }
  | _ => throw (IO.userError s!"runCommand: unhandled command (later tasks)")
```

- [ ] **Step 4: Build + a declare/apply test**

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
/-- info: decl-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    runCommand (.declareConst (.NormalSymbol "x") Blaster.Smt.intSort)
    let _ ← buildTerm (.SmtIdent (.SimpleIdent (.NormalSymbol "x")))
    IO.println "decl-ok"
```

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; prints `decl-ok`.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): const/func-decl/apply + runCommand skeleton"
```

---

## Task 7: Built-in operator dispatch (bool, arith, array, string)

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_terms.c`, `Blaster/Smt/FFI/Terms.lean`, `Blaster/Smt/FFI/Build.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Add operator shims**

Append to `z3_shim_terms.c` (variadic and binary/unary helpers). Full list:
```c
/* helper: collect Z3_ast array from a Lean Array Ast */
static Z3_ast *collect(lean_object *arr, size_t *out_n) {
  size_t n = lean_array_size(arr); *out_n = n;
  Z3_ast *as = (Z3_ast *)malloc(sizeof(Z3_ast) * (n ? n : 1));
  for (size_t i = 0; i < n; i++) as[i] = (Z3_ast)unbox_owned(lean_array_get_core(arr, i));
  return as;
}
#define VARIADIC(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg arr, lean_obj_arg w) { \
    (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); size_t n; Z3_ast *as=collect(arr,&n); \
    Z3_ast r=z3fn(ctx,(unsigned)n,as); free(as); return z3_io_ok(box_owned(r)); }
#define BINOP(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg w) { \
    (void)w; return z3_io_ok(box_owned(z3fn((Z3_context)ctx_ptr(c),(Z3_ast)unbox_owned(a),(Z3_ast)unbox_owned(b)))); }
#define UNOP(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) { \
    (void)w; return z3_io_ok(box_owned(z3fn((Z3_context)ctx_ptr(c),(Z3_ast)unbox_owned(a)))); }

VARIADIC(lean_z3_mk_and, Z3_mk_and)
VARIADIC(lean_z3_mk_or,  Z3_mk_or)
VARIADIC(lean_z3_mk_add, Z3_mk_add)
VARIADIC(lean_z3_mk_mul, Z3_mk_mul)
VARIADIC(lean_z3_mk_sub, Z3_mk_sub)
VARIADIC(lean_z3_mk_distinct, Z3_mk_distinct)
BINOP(lean_z3_mk_eq,      Z3_mk_eq)
BINOP(lean_z3_mk_implies, Z3_mk_implies)
BINOP(lean_z3_mk_lt,      Z3_mk_lt)
BINOP(lean_z3_mk_le,      Z3_mk_le)
BINOP(lean_z3_mk_gt,      Z3_mk_gt)
BINOP(lean_z3_mk_ge,      Z3_mk_ge)
BINOP(lean_z3_mk_idiv,    Z3_mk_div)   /* SMT `div` on ints */
BINOP(lean_z3_mk_mod,     Z3_mk_mod)
BINOP(lean_z3_mk_power,   Z3_mk_power) /* `^` */
BINOP(lean_z3_mk_select,  Z3_mk_select)
UNOP(lean_z3_mk_not, Z3_mk_not)

/* ite : c → t → e */
LEAN_EXPORT lean_obj_res lean_z3_mk_ite(b_lean_obj_arg c, b_lean_obj_arg i, b_lean_obj_arg t, b_lean_obj_arg e, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_ite((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(i),(Z3_ast)unbox_owned(t),(Z3_ast)unbox_owned(e))));
}
/* store : a → i → v */
LEAN_EXPORT lean_obj_res lean_z3_mk_store(b_lean_obj_arg c, b_lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg v, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_store((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(a),(Z3_ast)unbox_owned(i),(Z3_ast)unbox_owned(v))));
}
/* abs, to_int, and string ops */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_abs(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); Z3_ast x=(Z3_ast)unbox_owned(a);
  Z3_sort is=Z3_mk_int_sort(ctx); Z3_ast zero=Z3_mk_int(ctx,0,is);
  return z3_io_ok(box_owned(Z3_mk_ite(ctx, Z3_mk_ge(ctx,x,zero), x, Z3_mk_unary_minus(ctx,x))));
}
UNOP(lean_z3_mk_real2int, Z3_mk_real2int)       /* to_int */
UNOP(lean_z3_mk_seq_length, Z3_mk_seq_length)   /* str.len */
BINOP(lean_z3_mk_seq_concat2, /* placeholder: str.++ takes array; see NOTE */ Z3_mk_eq)
```
NOTE on strings: `Z3_mk_seq_concat` and `Z3_mk_seq_prefix`/`Z3_mk_str_lt` etc. take arrays or specific arities. Implement `str.++` as a VARIADIC over `Z3_mk_seq_concat(ctx,n,args)`; `str.<`/`str.<=` via `Z3_mk_str_lt`/`Z3_mk_str_le` (BINOP); `str.replace` via `Z3_mk_seq_replace(ctx, s, src, dst)` (ternary); `str.replace_all` — Z3 has no direct all-replace builtin in 4.15; **grep the tests first** (`grep -rn "str.replace_all\|str\." Tests`) and only implement the string ops that appear. If `str.replace_all` is unused, omit it and add an explicit `throw` in the dispatch.

- [ ] **Step 2: Lean externs**

Append to `Terms.lean` a matching `@[extern]` for each shim above, e.g.:
```lean
@[extern "lean_z3_mk_and"]     opaque Context.mkAnd     : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_or"]      opaque Context.mkOr      : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_add"]     opaque Context.mkAdd     : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_mul"]     opaque Context.mkMul     : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_sub"]     opaque Context.mkSub     : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_distinct"] opaque Context.mkDistinct : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_eq"]      opaque Context.mkEq      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_implies"] opaque Context.mkImplies : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_lt"]      opaque Context.mkLt      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_le"]      opaque Context.mkLe      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_gt"]      opaque Context.mkGt      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_ge"]      opaque Context.mkGe      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_idiv"]    opaque Context.mkIDiv    : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_mod"]     opaque Context.mkMod     : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_power"]   opaque Context.mkPower   : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_select"]  opaque Context.mkSelect  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_not"]     opaque Context.mkNot     : Context → Ast → IO Ast
@[extern "lean_z3_mk_ite"]     opaque Context.mkIte     : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_store"]   opaque Context.mkStore   : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_int_abs"] opaque Context.mkIntAbs  : Context → Ast → IO Ast
@[extern "lean_z3_mk_real2int"] opaque Context.mkToInt  : Context → Ast → IO Ast
@[extern "lean_z3_mk_seq_length"] opaque Context.mkStrLen : Context → Ast → IO Ast
-- + string externs actually used, per the grep in Step 1
```

- [ ] **Step 3: Implement `buildBuiltin?` dispatch**

Replace the `buildBuiltin?` stub in `Build.lean`:
```lean
partial def buildBuiltin? (sym : SmtSymbol) (args : Array SmtTerm) : BuildM (Option Ast) := do
  let ctx := (← get).ctx
  let bs ← args.mapM buildTerm            -- eager arg translation for most ops
  let bin (f : Context → Ast → Ast → IO Ast) : BuildM (Option Ast) := do
    if bs.size == 2 then some <$> f ctx bs[0]! bs[1]! else return none
  match sym with
  | .ReservedSymbol "and"      => some <$> ctx.mkAnd bs
  | .ReservedSymbol "or"       => some <$> ctx.mkOr bs
  | .ReservedSymbol "not"      => if bs.size == 1 then some <$> ctx.mkNot bs[0]! else return none
  | .ReservedSymbol "=>"       => bin Context.mkImplies
  | .ReservedSymbol "="        => bin Context.mkEq
  | .ReservedSymbol "ite"      => if bs.size == 3 then some <$> ctx.mkIte bs[0]! bs[1]! bs[2]! else return none
  | .ReservedSymbol "+"        => some <$> ctx.mkAdd bs
  | .ReservedSymbol "*"        => some <$> ctx.mkMul bs
  | .ReservedSymbol "-"        => some <$> ctx.mkSub bs
  | .ReservedSymbol "<"        => bin Context.mkLt
  | .ReservedSymbol "<="       => bin Context.mkLe
  | .ReservedSymbol "div"      => bin Context.mkIDiv
  | .ReservedSymbol "mod"      => bin Context.mkMod
  | .ReservedSymbol "^"        => bin Context.mkPower
  | .ReservedSymbol "abs"      => if bs.size == 1 then some <$> ctx.mkIntAbs bs[0]! else return none
  | .ReservedSymbol "to_int"   => if bs.size == 1 then some <$> ctx.mkToInt bs[0]! else return none
  | .ReservedSymbol "select"   => bin Context.mkSelect
  | .ReservedSymbol "store"    => if bs.size == 3 then some <$> ctx.mkStore bs[0]! bs[1]! bs[2]! else return none
  | .ReservedSymbol "str.len"  => if bs.size == 1 then some <$> ctx.mkStrLen bs[0]! else return none
  -- + remaining string ops discovered in Step 1's grep
  | _ => return none
```
NOTE: `ite` translated eagerly is fine (Z3 handles it; no short-circuit needed). `distinct` symbol: the translator uses `not (= …)` or `distinct`? Grep `grep -rn "distinct" Blaster` — add a `distinct` arm only if emitted.

- [ ] **Step 4: Register .o (already registered in Task 5), build, add a solver-free structural test**

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
/-- info: ops-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    runCommand (.declareConst (.NormalSymbol "x") Blaster.Smt.intSort)
    let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
    -- (x + 1 <= x*2) ∧ ¬(x = 0)
    let _ ← buildTerm (.AppTerm (.SimpleIdent (.ReservedSymbol "and")) #[
      .AppTerm (.SimpleIdent (.ReservedSymbol "<=")) #[
        .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[x, .NumTerm 1],
        .AppTerm (.SimpleIdent (.ReservedSymbol "*")) #[x, .NumTerm 2]],
      .AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
        .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 0]]])
    IO.println "ops-ok"
```

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; prints `ops-ok`.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): built-in operator dispatch (bool/arith/array/string)"
```

---

## Task 8: Assert + check-sat + model eval + Result

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_solver.c`, `Blaster/Smt/FFI/Solver.lean`
- Create: `Blaster/Smt/FFI/Session.lean`
- Modify: `Blaster/Smt/FFI.lean`
- Test: `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Add assert/check/model shims**

Append to `z3_shim_solver.c`:
```c
/* pull ctx+solver out of the box */
static Z3_context sctx(lean_object *o){ return ((z3_solver_box*)unbox_solver(o))->ctx; }
static Z3_solver ssol(lean_object *o){ return ((z3_solver_box*)unbox_solver(o))->s; }

/* solverAssert : Solver → Ast → IO Unit */
LEAN_EXPORT lean_obj_res lean_z3_solver_assert(b_lean_obj_arg s, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_solver_assert(sctx(s), ssol(s), (Z3_ast)unbox_owned(a)); return z3_io_unit();
}
/* solverCheck : Solver → IO UInt32 (2 sat / 0 unsat / 1 unknown) */
LEAN_EXPORT lean_obj_res lean_z3_solver_check(b_lean_obj_arg s, lean_obj_arg w) {
  (void)w; Z3_lbool r = Z3_solver_check(sctx(s), ssol(s));
  return z3_io_ok(lean_box_uint32((r==Z3_L_TRUE)?2u:(r==Z3_L_FALSE?0u:1u)));
}
/* solverEvalToString : Solver → Ast → IO String
 * gets the model, evals `a` with completion, returns the value as a string
 * ("" if no model / eval fails). */
LEAN_EXPORT lean_obj_res lean_z3_solver_eval_str(b_lean_obj_arg s, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_solver sol=ssol(s);
  Z3_model m = Z3_solver_get_model(ctx, sol);
  if (!m) return z3_io_ok(lean_mk_string(""));
  Z3_model_inc_ref(ctx, m);
  Z3_ast v; const char *out = "";
  if (Z3_model_eval(ctx, m, (Z3_ast)unbox_owned(a), true, &v)) out = Z3_ast_to_string(ctx, v);
  lean_object *res = lean_mk_string(out);
  Z3_model_dec_ref(ctx, m);
  return z3_io_ok(res);
}
```

- [ ] **Step 2: Lean externs**

Append to `Solver.lean`:
```lean
@[extern "lean_z3_solver_assert"]   opaque Solver.assert    : Solver → Ast → IO Unit
@[extern "lean_z3_solver_check"]    opaque Solver.check     : Solver → IO UInt32
@[extern "lean_z3_solver_eval_str"] opaque Solver.evalStr   : Solver → Ast → IO String
```

- [ ] **Step 3: Session with checkSat returning the Blaster `Result`**

`Blaster/Smt/FFI/Session.lean`:
```lean
import Blaster.Smt.FFI.Build
import Blaster.Smt.FFI.Solver
import Blaster.Smt.Env    -- for Blaster.Smt.Result

namespace Blaster.Smt.FFI
open Blaster.Smt

structure Z3Session where
  ctx    : Context
  solver : Solver
  state  : IO.Ref BuildState

def Z3Session.create : IO Z3Session := do
  let ctx ← mkContext
  let solver ← ctx.mkSolver
  let st ← BuildState.mk ctx
  let ref ← IO.mkRef st
  return { ctx, solver, state := ref }

/-- Run a BuildM action against the session's persistent state. -/
def Z3Session.run (sess : Z3Session) (m : BuildM α) : IO α := do
  let st ← sess.state.get
  let (a, st') ← m.run st
  sess.state.set st'
  return a

def Z3Session.runCommand (sess : Z3Session) (c : SmtCommand) : IO Unit :=
  sess.run (Build.runCommand c)

def Z3Session.assert (sess : Z3Session) (t : SmtTerm) : IO Unit := do
  let a ← sess.run (buildTerm t)
  sess.solver.assert a

/-- Map Z3's lbool to Blaster's Result. For `sat`, evaluate top-level vars. -/
def Z3Session.checkSat (sess : Z3Session)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  match ← sess.solver.check with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined

def Z3Session.getModel (sess : Z3Session)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO (List String) := do
  if !genCex then return []
  let mut cex := #[]
  for vars in topVars do
    for (sym, name) in vars.reverse do
      let a ← sess.run (buildTerm (smtSimpleVarId sym))
      let v ← sess.solver.evalStr a
      cex := cex.push s!"{name}: {v}"
  return cex.toList

end Blaster.Smt.FFI
```
NOTE: The `topVars.reverse` traversal must match the existing `getModel` ordering (it folds `topLevelVars` forward and each inner list in reverse — see `Blaster/Smt/Env.lean:516-524`). Mirror exactly: outer forward, inner reverse.

- [ ] **Step 4: End-to-end sat/unsat test**

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
open Blaster.Smt in
/-- info: r1=Valid r2=Falsified -/
#guard_msgs in
#eval do
  -- Valid: ∀x, x = x  → assert ¬(x=x) is unsat
  let s1 ← Z3Session.create
  s1.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, x]])
  let r1 ← s1.checkSat #[] false
  -- Falsified: assert (x = 1) is sat
  let s2 ← Z3Session.create
  s2.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1])
  let r2 ← s2.checkSat #[] false
  IO.println s!"r1={reprStr r1 |>.take 5} r2={reprStr r2 |>.take 9}"
```
(Adjust the printed form to match `Result`'s `Repr`; the key is `r1` Valid, `r2` Falsified.)

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; `r1` is Valid, `r2` is Falsified.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): session assert/check-sat/model → Result"
```

---

## Task 9: Wire the FFI session into Translate.main behind a backend switch

**Files:**
- Modify: `Blaster/Command/Options.lean` (add `backend` field)
- Modify: `Blaster/Optimize/Env.lean` (add `smtSession` field to `SmtEnv`)
- Modify: `Blaster/Smt/Env.lean` (route `assertTerm`/`checkSat`/`setBlasterProcess`/`exitSmt`)
- Modify: `Blaster/Smt/Translate.lean` (unchanged call shape; the routing lives in Env.lean)
- Test: run the existing quantifier-free suite subset

- [ ] **Step 1: Add a `backend` option (default `ffi`)**

In `Blaster/Command/Options.lean`, add to `BlasterOptions`:
```lean
  /-- Solver backend: `.ffi` (in-process Z3 C API) or `.smtlib` (legacy subprocess). -/
  backend : SolverBackend := .ffi
```
with, above the structure:
```lean
inductive SolverBackend where | ffi | smtlib
deriving Repr, BEq, Inhabited
```
(Wire a parser entry `(backend: ffi|smtlib)` mirroring the existing `(solver: …)`/`(random-seed: …)` option parsing — grep `randomSeed` in this file for the pattern.)

- [ ] **Step 2: Add `smtSession` to SmtEnv**

In `Blaster/Optimize/Env.lean`, add to `structure SmtEnv` (after `smtProc`):
```lean
  /-- In-process Z3 FFI session (used when backend = .ffi). -/
  smtSession : Option Blaster.Smt.FFI.Z3Session
```
and `smtSession := none` in the `Inhabited` instance. Add `import Blaster.Smt.FFI.Session` at the top (NOTE: watch for import cycles — `Session.lean` imports `Blaster.Smt.Env` for `Result`. Break the cycle by moving `Result` into a small `Blaster/Smt/Result.lean` imported by both. Do that move as the first sub-step.)

- [ ] **Step 3: Route the funnels on the FFI backend**

In `Blaster/Smt/Env.lean`, change the entry points to branch on backend:
```lean
def assertTerm (p : SmtTerm) : TranslateEnvT Unit := do
  storeCommand (.assertTerm p)
  match (← get).smtEnv.smtSession with
  | some sess => sess.assert p
  | none => trySubmitCommand! (.assertTerm p)   -- legacy (only when smtProc set)

def checkSat : TranslateEnvT Result := do
  match (← get).smtEnv.smtSession with
  | some sess =>
      let env ← get
      let topVars := env.smtEnv.topLevelVars
      let genCex := env.optEnv.options.solverOptions.generateCex
      sess.checkSat topVars genCex
  | none => /- existing subprocess path -/ ...
```
Similarly route `declareConst`/`declareFun`/`declareSort`/`declareDataType`/`defineFun`/etc. through `sess.runCommand` when a session exists (they currently call `trySubmitCommand!`; add the same `match … smtSession` branch, calling `sess.runCommand (.declareConst …)`). Keep `storeCommand` for dumpSmtLib.

In `setBlasterProcess`, when `backend = .ffi` and not `onlySmtLib`:
```lean
  | .ffi =>
      let sess ← Blaster.Smt.FFI.Z3Session.create
      set { env with smtEnv.smtSession := some sess }
      setDefaultSmtOptions sOpts   -- options routed to params in Phase 3; no-op / best-effort for now
```
In `exitSmt`, when a session is set, just clear it (GC frees the context): `set { env with smtEnv.smtSession := none }; return 0`.

NOTE: For phase 1, `setDefaultSmtOptions` on the FFI backend can be a no-op except `timeout` (deferred to Phase 3). Guard the option-setter bodies with `if (← get).smtEnv.smtSession.isNone then <legacy emit>`.

- [ ] **Step 4: Build the full library**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Blaster 2>&1 | tail -5`
Expected: `Build completed successfully`.

- [ ] **Step 5: Run a quantifier-free test file end-to-end via FFI**

Pick a QF file, e.g. create `Tests/Smt/FFI/FFIQF.lean`:
```lean
import Blaster
namespace Test.FFIQF
#blaster [∀ (x : Int), x + 0 = x]
#blaster [∀ (x y : Int), x + y = y + x]
#blaster [(3 : Int) + 4 = 7]
end Test.FFIQF
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "FFIQF|error|❌"`
Expected: no errors, no `❌`. (These reach `checkSat` via the FFI session because `backend` defaults to `.ffi`. NOTE: `∀` triggers quantifier translation — if quantifiers aren't implemented until Task 10, restrict this file to ground terms first, e.g. `(3:Int)+4=7`, and expand after Task 10.)

- [ ] **Step 6: Commit**

```bash
git add -A && git commit -m "feat(ffi): route Translate.main through FFI session behind backend switch"
```

---

# PHASE 2 — Hard Features

## Task 10: Quantifiers (forall / exists / lambda + patterns)

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_terms.c`, `Blaster/Smt/FFI/Terms.lean`, `Blaster/Smt/FFI/Build.lean`
- Test: `Tests/Smt/FFI/FFIQuant.lean`

- [ ] **Step 1: Add quantifier shims (bind fresh consts, not De Bruijn)**

Append to `z3_shim_terms.c`:
```c
/* mkQuantifierConst : Context → isForall(UInt8) → weight(UInt32)
 *   → Array Ast(bound consts) → Array Ast(patterns) → Ast(body) → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_quant_const(b_lean_obj_arg c, uint8_t isForall, uint32_t weight,
    b_lean_obj_arg bounds, b_lean_obj_arg pats, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t nb; Z3_app *bs=(Z3_app*)malloc(sizeof(Z3_app)*((nb=lean_array_size(bounds))?nb:1));
  for (size_t i=0;i<nb;i++) bs[i]=(Z3_app)Z3_to_app(ctx,(Z3_ast)unbox_owned(lean_array_get_core(bounds,i)));
  size_t np; Z3_pattern *ps=(Z3_pattern*)malloc(sizeof(Z3_pattern)*((np=lean_array_size(pats))?np:1));
  for (size_t i=0;i<np;i++){ Z3_ast pt=(Z3_ast)unbox_owned(lean_array_get_core(pats,i));
    ps[i]=Z3_mk_pattern(ctx,1,&pt); }
  Z3_ast r = Z3_mk_quantifier_const(ctx, isForall?true:false, weight,
    (unsigned)nb, bs, (unsigned)np, ps, (Z3_ast)unbox_owned(body));
  free(bs); free(ps);
  return z3_io_ok(box_owned(r));
}
/* mkLambdaConst : Context → Array Ast(bound) → Ast(body) → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_lambda_const(b_lean_obj_arg c, b_lean_obj_arg bounds, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t nb; Z3_app *bs=(Z3_app*)malloc(sizeof(Z3_app)*((nb=lean_array_size(bounds))?nb:1));
  for (size_t i=0;i<nb;i++) bs[i]=(Z3_app)Z3_to_app(ctx,(Z3_ast)unbox_owned(lean_array_get_core(bounds,i)));
  Z3_ast r = Z3_mk_lambda_const(ctx,(unsigned)nb,bs,(Z3_ast)unbox_owned(body));
  free(bs);
  return z3_io_ok(box_owned(r));
}
```

- [ ] **Step 2: Lean externs**

Append to `Terms.lean`:
```lean
@[extern "lean_z3_mk_quant_const"]  opaque Context.mkQuantConst  : Context → Bool → UInt32 → Array Ast → Array Ast → Ast → IO Ast
@[extern "lean_z3_mk_lambda_const"] opaque Context.mkLambdaConst : Context → Array Ast → Ast → IO Ast
```

- [ ] **Step 3: Implement quantifier cases in `buildTerm`**

Add helper + cases in `Build.lean`:
```lean
/-- Push bound vars as fresh consts, run `k`, pop them. Returns k's result + the bound consts. -/
partial def withBound (bs : SortedVars) (k : BuildM α) : BuildM (α × Array Ast) := do
  let ctx := (← get).ctx
  let mut consts := #[]
  for (sym, se) in bs do
    let s ← buildSort se
    let a ← ctx.mkConst sym.toString s   -- fresh const per bound var
    consts := consts.push a
    modify fun st => { st with locals := st.locals.push (sym, a) }
  let r ← k
  modify fun st => { st with locals := st.locals.shrink (st.locals.size - bs.size) }
  return (r, consts)

partial def buildQuant (isForall : Bool) (bs : SortedVars) (body : SmtTerm)
    (pats : Array SmtTerm := #[]) : BuildM Ast := do
  let ctx := (← get).ctx
  let ((b, patAsts), consts) ← withBound bs do
    let b ← buildTerm body
    let patAsts ← pats.mapM buildTerm
    return (b, patAsts)
  ctx.mkQuantConst isForall 0 consts patAsts b
```
Extend `buildTerm`:
```lean
  | .ForallTerm bs body => buildQuant true bs body
  | .ExistsTerm bs body => buildQuant false bs body
  | .LambdaTerm bs body => do
      let (b, consts) ← withBound bs (buildTerm body)
      (← get).ctx.mkLambdaConst consts b
  | .AnnotatedTerm t annot => do
      -- extract patterns/qid from annot; forward to the wrapped term
      match t with
      | .ForallTerm bs body => buildQuant true bs body (patternsOf annot)
      | .ExistsTerm bs body => buildQuant false bs body (patternsOf annot)
      | _ => buildTerm t
```
with:
```lean
private def patternsOf (annot : Array SmtAttribute) : Array SmtTerm :=
  annot.foldl (fun acc a => match a with | .Pattern ps => acc ++ ps | _ => acc) #[]
```
NOTE: `withBound`'s `locals` pop assumes no earlier task shrank it; since we only ever push/pop in matched pairs, `shrink (size - bs.size)` is correct.

- [ ] **Step 4: Quantifier tests**

`Tests/Smt/FFI/FFIQuant.lean`:
```lean
import Blaster
namespace Test.FFIQuant
#blaster [∀ (x : Int), x + 0 = x]
#blaster [∀ (x y : Int), x + y = y + x]
#blaster [∀ (x : Int), ∃ (y : Int), y = x + 1]
#blaster [∀ (x y : Nat), (x + y) % y = x % y]     -- exercises define-fun wrappers too (Task 13)
end Test.FFIQuant
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "FFIQuant|error|❌"`
Expected: no errors (the `%` test may need Task 13 macros; if so, comment it and re-enable after Task 13).

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): quantifiers (forall/exists/lambda + patterns)"
```

---

## Task 11: `let` terms

**Files:** Modify `Blaster/Smt/FFI/Build.lean`; Test `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: Implement `LetTerm` in `buildTerm`**

```lean
  | .LetTerm bs body => do
      -- translate each binding value, push as a local, translate body, pop
      let mut n := 0
      for (sym, valT) in bs do
        let v ← buildTerm valT
        modify fun st => { st with locals := st.locals.push (sym, v) }
        n := n + 1
      let r ← buildTerm body
      modify fun st => { st with locals := st.locals.shrink (st.locals.size - n) }
      return r
```
NOTE: SMT-LIB `let` binds simultaneously (RHSs see the *outer* scope). Translating all RHSs before pushing any preserves that. The loop above pushes each binding as it goes, so a later RHS could see an earlier binding — **fix** by translating all values first into an array, then pushing:
```lean
  | .LetTerm bs body => do
      let vals ← bs.mapM (fun (s, v) => do return (s, ← buildTerm v))
      vals.forM fun (s, v) => modify fun st => { st with locals := st.locals.push (s, v) }
      let r ← buildTerm body
      modify fun st => { st with locals := st.locals.shrink (st.locals.size - bs.size) }
      return r
```

- [ ] **Step 2: Test**

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
open Blaster.Smt in
/-- info: let-ok -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  -- (let ((y (+ x 1))) (= y (+ x 1))) must be Valid → assert its negation is unsat
  let lt : SmtTerm := .LetTerm #[(.NormalSymbol "y", .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[x, .NumTerm 1])]
    (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
      .SmtIdent (.SimpleIdent (.NormalSymbol "y")),
      .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[x, .NumTerm 1]])
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[lt])
  let r ← s.checkSat #[] false
  IO.println s!"let-{if r matches .Valid then "ok" else "BAD"}"
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: prints `let-ok`.

- [ ] **Step 3: Commit**

```bash
git add -A && git commit -m "feat(ffi): let terms (simultaneous binding)"
```

---

## Task 12: Datatypes (single + mutual)

**Files:**
- Create: `Blaster/Smt/FFI/c/z3_shim_datatypes.c`, `Blaster/Smt/FFI/Datatypes.lean`
- Modify: `Blaster/Smt/FFI/Build.lean` (runCommand datatype cases), `lakefile.lean`, `Blaster/Smt/FFI.lean`
- Test: `Tests/Smt/FFI/FFIData.lean`

- [ ] **Step 1: Datatype construction shim**

`Blaster/Smt/FFI/c/z3_shim_datatypes.c` — expose `Z3_mk_constructor`, `Z3_mk_datatype`, and accessors to pull back the generated `Z3_func_decl`s. Because the constructor API is stateful (an opaque `Z3_constructor` list), implement a single shim that takes a fully-serialized description and returns the sort + a flat array of `(name, funcdecl)` for constructors/recognizers/accessors:
```c
#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* Build ONE datatype.
 * Inputs (all Lean values):
 *   sortName   : String
 *   ctorNames  : Array String
 *   recogNames : Array String
 *   fieldNames : Array (Array String)   -- per ctor
 *   fieldSorts : Array (Array Sort)     -- per ctor; element sort (no recursion refs for MVP)
 * Returns: (Sort, Array FuncDecl)  where the FuncDecl array is, per ctor:
 *   [ctor, recognizer, field0_accessor, field1_accessor, ...] concatenated.
 * The Lean side knows the layout and registers names accordingly. */
LEAN_EXPORT lean_obj_res lean_z3_mk_datatype(b_lean_obj_arg c, b_lean_obj_arg sortName,
    b_lean_obj_arg ctorNames, b_lean_obj_arg recogNames,
    b_lean_obj_arg fieldNames, b_lean_obj_arg fieldSorts, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  unsigned nc = (unsigned)lean_array_size(ctorNames);
  Z3_constructor *cons = (Z3_constructor*)malloc(sizeof(Z3_constructor)*(nc?nc:1));
  for (unsigned i=0;i<nc;i++){
    lean_object *fn = lean_array_get_core(fieldNames,i);
    lean_object *fs = lean_array_get_core(fieldSorts,i);
    unsigned nf = (unsigned)lean_array_size(fn);
    Z3_symbol *fnames=(Z3_symbol*)malloc(sizeof(Z3_symbol)*(nf?nf:1));
    Z3_sort *fsorts=(Z3_sort*)malloc(sizeof(Z3_sort)*(nf?nf:1));
    unsigned *refs=(unsigned*)malloc(sizeof(unsigned)*(nf?nf:1));
    for (unsigned j=0;j<nf;j++){
      fnames[j]=Z3_mk_string_symbol(ctx,lean_string_cstr(lean_array_get_core(fn,j)));
      fsorts[j]=(Z3_sort)unbox_owned(lean_array_get_core(fs,j));
      refs[j]=0; /* non-recursive fields */
    }
    Z3_symbol cn=Z3_mk_string_symbol(ctx,lean_string_cstr(lean_array_get_core(ctorNames,i)));
    Z3_symbol rn=Z3_mk_string_symbol(ctx,lean_string_cstr(lean_array_get_core(recogNames,i)));
    cons[i]=Z3_mk_constructor(ctx,cn,rn,nf,fnames,fsorts,refs);
    free(fnames); free(fsorts); free(refs);
  }
  Z3_symbol sn=Z3_mk_string_symbol(ctx,lean_string_cstr(sortName));
  Z3_sort dt=Z3_mk_datatype(ctx,sn,nc,cons);
  /* extract func_decls, flatten */
  /* count total: per ctor 2 + nf */
  /* first pass to count */
  unsigned total=0;
  for (unsigned i=0;i<nc;i++) total += 2 + (unsigned)lean_array_size(lean_array_get_core(fieldNames,i));
  lean_object *arr = lean_alloc_array(total,total);
  unsigned k=0;
  for (unsigned i=0;i<nc;i++){
    Z3_func_decl cf, rf; Z3_func_decl *accs;
    unsigned nf=(unsigned)lean_array_size(lean_array_get_core(fieldNames,i));
    accs=(Z3_func_decl*)malloc(sizeof(Z3_func_decl)*(nf?nf:1));
    Z3_query_constructor(ctx, cons[i], nf, &cf, &rf, accs);
    lean_array_set_core(arr,k++,box_owned(cf));
    lean_array_set_core(arr,k++,box_owned(rf));
    for (unsigned j=0;j<nf;j++) lean_array_set_core(arr,k++,box_owned(accs[j]));
    free(accs);
    Z3_del_constructor(ctx,cons[i]);
  }
  free(cons);
  lean_object *pair = lean_alloc_ctor(0,2,0);
  lean_ctor_set(pair,0,box_owned(dt));
  lean_ctor_set(pair,1,arr);
  return z3_io_ok(pair);
}
```
NOTE: This MVP handles non-recursive, non-mutual, non-parametric datatypes (sufficient for structures like `Ratio` and the datatype-pair model). Mutual/recursive datatypes (`Z3_mk_datatypes` with sort refs) are a follow-up sub-task — grep `declareMutualDataTypes` usage in `Tests` to see if any test needs it before investing; if unused on `main`, emit an explicit `throw` for `declareMutualDataTypes` and note it.

- [ ] **Step 2: Lean extern + runCommand cases**

`Blaster/Smt/FFI/Datatypes.lean`:
```lean
import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI
@[extern "lean_z3_mk_datatype"]
opaque Context.mkDatatype : Context → String → Array String → Array String
  → Array (Array String) → Array (Array Sort) → IO (Sort × Array FuncDecl)
end Blaster.Smt.FFI
```
In `Build.lean` `runCommand`, add the `.declareDataType` case: destructure `SmtDatatypeDecl` into the five arrays (ctor names, recognizer names — synthesize `is-<ctor>` names as the emitter does; grep `EmitCommand.lean` for the recognizer naming, field names, field sorts via `buildSort`), call `ctx.mkDatatype`, then register: the datatype sort under `nm`, each constructor/recognizer/accessor func_decl under its SMT name in `funcs`. Handle nullary constructors as 0-ary funcs applied via `mkApp` with empty args (or register as consts).

- [ ] **Step 3: Register .o + import; datatype test**

Wire `z3_shim_datatypes.c`/`.o` into `lakefile.lean`; `import Blaster.Smt.FFI.Datatypes` in the umbrella.
`Tests/Smt/FFI/FFIData.lean`:
```lean
import Blaster
namespace Test.FFIData
structure Ratio where
  num : Int
  den : Int
#blaster [∀ (r : Ratio), r.num = r.num]
#blaster [∀ (a b : Int), (Ratio.mk a b).num = a]
end Test.FFIData
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "FFIData|error|❌"`
Expected: no errors.

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "feat(ffi): non-recursive datatype construction + accessors"
```

---

## Task 13: define-fun (inline) + rec-def detection

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_terms.c`, `Blaster/Smt/FFI/Terms.lean`, `Blaster/Smt/FFI/Build.lean`
- Test: `Tests/Smt/FFI/FFIDefine.lean`

- [ ] **Step 1: Implement `inlineMacro` (substitute args for params)**

Replace the `inlineMacro` stub in `Build.lean`:
```lean
partial def inlineMacro (m : MacroDef) (args : Array SmtTerm) : BuildM Ast := do
  if m.params.size != args.size then
    throw (IO.userError s!"inlineMacro: arity mismatch {m.params.size} ≠ {args.size}")
  -- translate args, bind params as locals, translate the body, pop
  let vals ← args.mapM buildTerm
  (Array.zip m.params vals).forM fun (p, v) =>
    modify fun st => { st with locals := st.locals.push (p, v) }
  let r ← buildTerm m.body
  modify fun st => { st with locals := st.locals.shrink (st.locals.size - m.params.size) }
  return r
```

- [ ] **Step 2: `runCommand` for `defineFun` — inline vs rec-def**

Add to `runCommand`:
```lean
  | .defineFun isRec nm params _rt body =>
      let paramSyms := params.map (·.1)
      if isRec || bodyReferences nm body then
        -- recursive: register a rec func decl + add its definition
        let ds ← params.mapM (fun (_, se) => buildSort se)
        let r ← buildSort _rt
        let fd ← (← get).ctx.mkRecFuncDecl nm.toString ds r
        modify fun st => { st with recFuncs := st.recFuncs.insert nm fd }
        -- add the definition: bind params as consts, build body, add_rec_def
        let (bodyAst, consts) ← withBound params (buildTerm body)
        (← get).ctx.addRecDef fd consts bodyAst
      else
        modify fun st => { st with macros := st.macros.insert nm { params := paramSyms, body } }
```
with a syntactic recursion check:
```lean
partial def bodyReferences (nm : SmtSymbol) (t : SmtTerm) : Bool :=
  match t with
  | .AppTerm (.SimpleIdent s) args => s == nm || args.any (bodyReferences nm)
  | .SmtIdent (.SimpleIdent s) => s == nm
  | .LetTerm bs b => bs.any (fun (_, v) => bodyReferences nm v) || bodyReferences nm b
  | .ForallTerm _ b | .ExistsTerm _ b | .LambdaTerm _ b => bodyReferences nm b
  | .AnnotatedTerm t _ => bodyReferences nm t
  | .AppTerm _ args => args.any (bodyReferences nm)
  | _ => false
```

- [ ] **Step 3: rec-def shims + externs**

Append to `z3_shim_terms.c`:
```c
/* mkRecFuncDecl : Context → String → Array Sort → Sort → IO FuncDecl */
LEAN_EXPORT lean_obj_res lean_z3_mk_rec_func_decl(b_lean_obj_arg c, b_lean_obj_arg name,
    b_lean_obj_arg dom, b_lean_obj_arg rng, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t n; Z3_sort *ds=(Z3_sort*)malloc(sizeof(Z3_sort)*((n=lean_array_size(dom))?n:1));
  for (size_t i=0;i<n;i++) ds[i]=(Z3_sort)unbox_owned(lean_array_get_core(dom,i));
  Z3_symbol sym=Z3_mk_string_symbol(ctx,lean_string_cstr(name));
  Z3_func_decl fd=Z3_mk_rec_func_decl(ctx,sym,(unsigned)n,ds,(Z3_sort)unbox_owned(rng));
  free(ds); return z3_io_ok(box_owned(fd));
}
/* addRecDef : Context → FuncDecl → Array Ast(args) → Ast(body) → IO Unit */
LEAN_EXPORT lean_obj_res lean_z3_add_rec_def(b_lean_obj_arg c, b_lean_obj_arg fd,
    b_lean_obj_arg args, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t n; Z3_ast *as=(Z3_ast*)malloc(sizeof(Z3_ast)*((n=lean_array_size(args))?n:1));
  for (size_t i=0;i<n;i++) as[i]=(Z3_ast)unbox_owned(lean_array_get_core(args,i));
  Z3_add_rec_def(ctx,(Z3_func_decl)unbox_owned(fd),(unsigned)n,as,(Z3_ast)unbox_owned(body));
  free(as); return z3_io_unit();
}
```
Append to `Terms.lean`:
```lean
@[extern "lean_z3_mk_rec_func_decl"] opaque Context.mkRecFuncDecl : Context → String → Array Sort → Sort → IO FuncDecl
@[extern "lean_z3_add_rec_def"]      opaque Context.addRecDef     : Context → FuncDecl → Array Ast → Ast → IO Unit
```

- [ ] **Step 4: Test the wrapper functions (`@Nat.sub`, `%`, etc.)**

`Tests/Smt/FFI/FFIDefine.lean`:
```lean
import Blaster
namespace Test.FFIDefine
-- these emit @Nat.sub / @Int.* define-fun wrappers internally
#blaster [∀ (x : Nat), x - 0 = x]
#blaster [∀ (x y : Nat), x - y ≤ x]
#blaster [∀ (x y : Nat), (x + y) % y = x % y]
end Test.FFIDefine
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "FFIDefine|error|❌"`
Expected: no errors.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): define-fun inlining + rec-def for recursive defs"
```

---

## Task 14: defineSort aliases

**Files:** Modify `Blaster/Smt/FFI/Build.lean`; Test `Tests/Smt/FFI/FFICore.lean`

- [ ] **Step 1: `runCommand` for `defineSort`**

```lean
  | .defineSort nm args body =>
      match args with
      | none | some #[] =>
          let s ← buildSort body
          modify fun st => { st with sorts := st.sorts.insert nm s }
      | some _ =>
          -- parametric sort alias: not emitted on this branch; fail loudly if it ever is
          throw (IO.userError s!"defineSort: parametric alias {nm.toString} unsupported")
```
NOTE: This is what makes the emitter's `defineNatSort`/`definePropSort` work when they route through the FFI backend. Confirm those commands reach `runCommand` (they call `defineSort` in `Env.lean:271` → route to `sess.runCommand`).

- [ ] **Step 2: Test (Nat/Prop already exercised by earlier tests; add an explicit alias)**

Append to `Tests/Smt/FFI/FFICore.lean`:
```lean
open Blaster.Smt in
/-- info: alias-ok -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.defineSort (.NormalSymbol "MyInt") none intSort)
  s.runCommand (.declareConst (.NormalSymbol "z") (.SymbolSort (.NormalSymbol "MyInt")))
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
    .SmtIdent (.SimpleIdent (.NormalSymbol "z")), .NumTerm 5])
  let r ← s.checkSat #[] false
  IO.println s!"alias-{if r matches .Falsified _ then "ok" else "BAD"}"
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: prints `alias-ok`.

- [ ] **Step 3: Commit**

```bash
git add -A && git commit -m "feat(ffi): defineSort (non-parametric aliases)"
```

---

## Task 15: checkSatAssuming + StateMachine wiring

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_solver.c`, `Blaster/Smt/FFI/Solver.lean`, `Blaster/Smt/FFI/Session.lean`
- Modify: `Blaster/Smt/Env.lean` (route `checkSatAssuming`)
- Test: `Tests/Smt/FFI/FFIStateMachine.lean` (or run existing StateMachine tests)

- [ ] **Step 1: Assumptions shim**

Append to `z3_shim_solver.c`:
```c
/* solverCheckAssuming : Solver → Array Ast → IO UInt32 */
LEAN_EXPORT lean_obj_res lean_z3_solver_check_assuming(b_lean_obj_arg s, b_lean_obj_arg assumps, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_solver sol=ssol(s);
  size_t n; Z3_ast *as=(Z3_ast*)malloc(sizeof(Z3_ast)*((n=lean_array_size(assumps))?n:1));
  for (size_t i=0;i<n;i++) as[i]=(Z3_ast)unbox_owned(lean_array_get_core(assumps,i));
  Z3_lbool r=Z3_solver_check_assumptions(ctx,sol,(unsigned)n,as); free(as);
  return z3_io_ok(lean_box_uint32((r==Z3_L_TRUE)?2u:(r==Z3_L_FALSE?0u:1u)));
}
```

- [ ] **Step 2: Extern + session method**

Append to `Solver.lean`:
```lean
@[extern "lean_z3_solver_check_assuming"] opaque Solver.checkAssuming : Solver → Array Ast → IO UInt32
```
Append to `Session.lean`:
```lean
def Z3Session.checkAssuming (sess : Z3Session) (assumps : Array SmtTerm)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  let asts ← assumps.mapM (fun t => sess.run (buildTerm t))
  match ← sess.solver.checkAssuming asts with
  | 0 => return .Valid
  | 2 => return .Falsified (← sess.getModel topVars genCex)
  | _ => return .Undetermined
```

- [ ] **Step 3: Route `checkSatAssuming` in Env.lean**

Mirror the `checkSat` routing: on a session, call `sess.checkAssuming args topVars genCex`; else legacy.

- [ ] **Step 4: Run existing StateMachine tests via FFI**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "StateMachine|BMC|KInduction|error|❌"`
Expected: no errors. (Locate the relevant test files with `find Tests -iname '*state*' -o -iname '*bmc*' -o -iname '*induction*'` and confirm they build under the FFI default backend.)

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "feat(ffi): checkSatAssuming + StateMachine/BMC/KInduction wiring"
```

---

## Task 16: Full-suite parity gate

**Files:** none (verification task)

- [ ] **Step 1: Build the entire test suite under the FFI backend (default)**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tee /tmp/ffi-suite.log | tail -20`
Expected: `Build completed successfully`.

- [ ] **Step 2: Scan for any failed expectations**

Run: `grep -cE "❌|error:" /tmp/ffi-suite.log`
Expected: `0`. If nonzero, list them and fix the responsible task's dispatch before proceeding to Phase 3. Do NOT proceed to code deletion until this gate is green.

- [ ] **Step 3: Commit a marker (optional) / note parity reached**

```bash
git commit --allow-empty -m "test(ffi): full Tests suite passes under FFI backend (parity)"
```

---

# PHASE 3 — Options, Cancellation, Cleanup

## Task 17: Options → Z3 params

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_solver.c`, `Blaster/Smt/FFI/Solver.lean`, `Blaster/Smt/FFI/Session.lean`, `Blaster/Smt/Env.lean`
- Test: `Tests/Smt/FFI/FFIOptions.lean`

- [ ] **Step 1: Params shims (build params, set on solver; config/global for pre-context opts)**

Append to `z3_shim_solver.c`:
```c
/* solverSetTimeout : Solver → UInt32(ms) → IO Unit */
LEAN_EXPORT lean_obj_res lean_z3_solver_set_timeout(b_lean_obj_arg s, uint32_t ms, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s);
  Z3_params p=Z3_mk_params(ctx); Z3_params_inc_ref(ctx,p);
  Z3_symbol k=Z3_mk_string_symbol(ctx,"timeout");
  Z3_params_set_uint(ctx,p,k,ms);
  Z3_solver_set_params(ctx,ssol(s),p);
  Z3_params_dec_ref(ctx,p);
  return z3_io_unit();
}
/* solverSetRandomSeed : Solver → UInt32 → IO Unit  (param "random_seed") */
LEAN_EXPORT lean_obj_res lean_z3_solver_set_seed(b_lean_obj_arg s, uint32_t seed, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s);
  Z3_params p=Z3_mk_params(ctx); Z3_params_inc_ref(ctx,p);
  Z3_params_set_uint(ctx,p,Z3_mk_string_symbol(ctx,"random_seed"),seed);
  Z3_solver_set_params(ctx,ssol(s),p); Z3_params_dec_ref(ctx,p);
  return z3_io_unit();
}
```
NOTE: `mbqi`, `macro_finder`, `auto_config`, `pull-nested-quantifiers` are engine/module params. Test whether `Z3_params_set_bool` on the solver params (keys `"smt.mbqi"`, `"smt.macro_finder"`, `"auto_config"`, `"smt.pull_nested_quantifiers"`) takes effect. If Z3 rejects them at solver level (check `Z3_get_error_code` after `Z3_solver_set_params`), fall back to `Z3_global_param_set("smt.mbqi","true")` called **before** `mkContext` in `Session.create`. Implement a `globalParamSet : String → String → IO Unit` shim (`Z3_global_param_set`) for that path. Decide empirically per option; document the final placement in a comment.

- [ ] **Step 2: Externs + session helpers + route the option setters**

Add externs `Solver.setTimeout`, `Solver.setRandomSeed`, `globalParamSet`. In `Session.create`, before `mkContext`, apply any global params (mbqi/macro_finder/auto_config/pull-nested-quantifiers per Step-1 findings). In `Env.lean`, change `setTimeout`/`setRandomSeed`/`setMbqi`/… so that when a session exists they call the FFI helpers instead of emitting `set-option`. `setPrintSuccess`/`setProduceModels` become no-ops on the FFI backend.

- [ ] **Step 3: Test timeout + seed determinism**

`Tests/Smt/FFI/FFIOptions.lean`:
```lean
import Blaster
namespace Test.FFIOptions
#blaster (random-seed: 2) [∀ (x y z : Nat), (x + y * z) % y = x % y]
-- a formula Z3 cannot decide quickly, with a short timeout → Undetermined (not a hang)
#blaster (timeout: 1) [∀ (f : Int → Int) (x : Int), f (f (f x)) = x]
end Test.FFIOptions
```
Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -iE "FFIOptions|error"`
Expected: builds; the timeout case yields Undetermined without hanging (adjust the `solveResult` expectation if the test harness treats Undetermined as an error — use the appropriate `(expected: …)` annotation).

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "feat(ffi): options → Z3 params (timeout, seed, engine params)"
```

---

## Task 18: Interrupt-based cancellation

**Files:**
- Modify: `Blaster/Smt/FFI/c/z3_shim_solver.c`, `Blaster/Smt/FFI/Solver.lean`, `Blaster/Smt/FFI/Session.lean`, `Blaster/Smt/Env.lean`
- Test: manual (hard to unit-test a cancel race; verify wiring compiles + a smoke interrupt)

- [ ] **Step 1: Interrupt shim**

Append to `z3_shim_solver.c`:
```c
/* solverInterrupt : Solver → IO Unit  (thread-safe; signals a running check to stop) */
LEAN_EXPORT lean_obj_res lean_z3_solver_interrupt(b_lean_obj_arg s, lean_obj_arg w) {
  (void)w; Z3_solver_interrupt(sctx(s), ssol(s)); return z3_io_unit();
}
```
Extern: `@[extern "lean_z3_solver_interrupt"] opaque Solver.interrupt : Solver → IO Unit`.

- [ ] **Step 2: Async check with cancel polling in Session**

Add to `Session.lean` a check that runs on a task and polls the cancel token:
```lean
def Z3Session.checkSatCancellable (sess : Z3Session)
    (cancelTk? : Option IO.CancelToken)
    (topVars : Array (List (SmtSymbol × Lean.Name))) (genCex : Bool) : IO Result := do
  let task ← IO.asTask (sess.solver.check)
  let rec loop : IO Result := do
    if ← IO.hasFinished task then
      match (← IO.ofExcept task.get) with
      | 0 => return .Valid
      | 2 => return .Falsified (← sess.getModel topVars genCex)
      | _ => return .Undetermined
    else
      if let some tk := cancelTk? then
        if ← tk.isSet then
          sess.solver.interrupt
          -- let the interrupted check finish and return unknown
          let _ ← IO.ofExcept task.get
          return .Undetermined
      IO.sleep 20
      loop
  loop
```
Route `checkSat`/`checkAssuming` in `Env.lean` to pass `(← readThe Core.Context).cancelTk?` into these cancellable variants when on the FFI backend. (For `checkAssuming`, add a parallel cancellable method.)

- [ ] **Step 3: Build + a non-cancel smoke (ensures the async path returns correctly)**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | tail -5`
Expected: success; existing tests still pass through the async check path.

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "feat(ffi): interrupt-based cancellation via async check + Z3_solver_interrupt"
```

---

## Task 19: getProof (only if used)

**Files:** conditional.

- [ ] **Step 1: Determine if getProof is exercised**

Run: `grep -rn "getProof\|produce-proofs\|getProof" Blaster Tests | grep -v "def getProof"`
- If no caller needs proof output for a real feature, **skip this task**: leave `getProof` unimplemented on the FFI backend with an explicit `throw (IO.userError "getProof: FFI backend does not implement proof extraction")`, and remove `setProduceProofs true` from the FFI option defaults.
- If it is needed, implement `Z3_solver_get_proof` + `Z3_ast_to_string` behind a `solverGetProofStr : Solver → IO String` shim and route `getProof`.

- [ ] **Step 2: Commit**

```bash
git add -A && git commit -m "chore(ffi): getProof handling (implemented/deferred per usage)"
```

---

## Task 20: Delete the dead string/process path

**Files:**
- Delete: `Blaster/Smt/EmitCommand.lean`
- Modify: `Blaster/Smt/Env.lean`, `Blaster/Optimize/Env.lean`, `Blaster/Command/Options.lean`
- Modify: any imports of `EmitCommand`

- [ ] **Step 1: Confirm the FFI backend is the only backend**

Decide: keep `backend` as a user option, or hard-remove `.smtlib`. Per spec (Z3-only, FFI), remove the `.smtlib` variant and the subprocess path.

- [ ] **Step 2: Remove subprocess machinery**

Delete from `Blaster/Smt/Env.lean`: `findZ3CmdAndVersion`, `createBlasterProcess`, `getOutputModel`, `getOutputProof`, `getErrorMsg`, `getOutputEval`, `getSatResult`, the process branch of `trySubmitCommand!`, and the legacy branches in `assertTerm`/`checkSat`/`checkSatAssuming`/`getModel`/`exitSmt`/option-setters. Remove `SmtEnv.smtProc` (`Blaster/Optimize/Env.lean:353`) and its uses in `throwEnvError`/`checkCancelTk?` (now go through the session/interrupt). Delete `Blaster/Smt/EmitCommand.lean` and its import in `Blaster/Smt/Env.lean`. Keep `SmtCommand.toString`/`storeCommand` for `dumpSmtLib`.

- [ ] **Step 3: Fix `checkCancelTk?`**

Reimplement to operate on the session (interrupt) rather than `p.kill`; or fold entirely into `checkSatCancellable` and remove the standalone reader-polling version.

- [ ] **Step 4: Build everything + full suite**

Run: `DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build 2>&1 | tail -5 && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake build Tests 2>&1 | grep -cE "❌|error:"`
Expected: library builds; test error count `0`.

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "refactor(ffi): remove legacy string/subprocess Z3 path"
```

---

## Task 21: CI + docs

**Files:**
- Modify: `.github/workflows/*.yml`
- Modify: `README.md` (build/runtime deps)

- [ ] **Step 1: Install libz3 in CI**

In the CI workflow, before `lake build`: macOS `brew install z3`; Linux `sudo apt-get install -y libz3-dev` (or download a Z3 release and set `Z3_LIB_PATH`/`Z3_INC_PATH`). Ensure the runtime step has libz3 on the loader path (`LD_LIBRARY_PATH`/`DYLD_LIBRARY_PATH`).

- [ ] **Step 2: Verify CI config locally as far as possible**

Run: `grep -rn "z3\|Z3" .github/workflows/`
Expected: install step present; version matches (≥ 4.15).

- [ ] **Step 3: Document build/runtime deps in README**

Add a "Building with the Z3 FFI backend" section: requires libz3 (4.15.x) + headers; `Z3_LIB_PATH`/`Z3_INC_PATH` overrides; note `lake build --reconfigure` after changing them.

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "ci,docs: install libz3 and document FFI build deps"
```

---

## Self-Review Notes (author)

- **Spec §5 memory model** → Tasks 1–2 (finalizers on Context/Solver only; ast/sort/funcdecl via `box_owned` no-finalizer). Invariant (context reachable while asts live) holds because `Z3Session` holds `ctx` for the session's lifetime and asts never escape the session.
- **Spec §6.1 define-fun** → Task 13 (inline default; rec-def only when `bodyReferences`).
- **Spec §6.2 quantifiers** → Task 10 (fresh consts, patterns).
- **Spec §6.3 let** → Task 11 (simultaneous binding fix).
- **Spec §6.4 datatypes** → Task 12 (single/non-recursive MVP; mutual flagged).
- **Spec §6.5 cancellation** → Task 18 (async + interrupt).
- **Spec §6.6 errors** → Task 1/2 (no-op handler; `errorCode`/`errorMsg` bindings; add per-command error polling where a shim can fail — a follow-up hardening pass may thread `Context.errorCode` checks into `buildTerm`).
- **Spec §7 options** → Task 17 (with the config/global-vs-solver placement resolved empirically).
- **Spec §8 build system** → Tasks 1, 21 (proven by spike).
- **Spec §9 testing** → existing `Tests/` as oracle (Task 16 gate); no differential harness.
- **Spec §10 phasing** → Phases 1/2/3 map to Tasks 1–9 / 10–16 / 17–21.
- **Deviation:** BitVec/Fin/SMTArray absent on `main` → not implemented; documented in "Scope Reconciliation".
- **Open risk carried into execution:** exact SMT symbol strings for string ops, `distinct`, and datatype recognizer naming — each task says "grep first" so the dispatch matches the real emitter.
