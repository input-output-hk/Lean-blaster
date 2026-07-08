# Z3 FFI Backend — Design Spec

**Date:** 2026-07-08
**Branch:** `feat/z3-ffi-migration`
**Status:** Approved design, pending implementation plan

## 1. Problem & Goal

Lean-blaster currently talks to Z3 by spawning a persistent `z3 -in -smt2`
subprocess and driving it *interactively over stdin/stdout*: every `SmtCommand`
is rendered to SMT-LIB text and streamed to the process, with a `success\n`
handshake read back after each declarative command; results are recovered by
line-based parsing of stdout (`sat\n`/`unsat\n`, paren-counting for
`(eval …)` values, CRLF normalization).

**Goal:** replace this with an **in-process binding to the Z3 C API** that
builds Z3 AST objects node-by-node and solves in-process — eliminating the
subprocess, the per-command IPC handshake, and the fragile text parsing.

**Motivation:** performance (no process spawn, no per-command round-trips) and
richer feature access (structured models/counterexamples, interrupts, and a
foundation for unsat cores / statistics later).

## 2. Scope

**In scope**
- Full **AST-building** backend: `SmtTerm`/`SortExpr` → `Z3_ast`/`Z3_sort` via
  `Z3_mk_*`; no SMT-LIB strings sent to the solver.
- Z3 only. Stay on Lean toolchain **v4.24.0**.
- A **self-contained C shim inside Lean-blaster** (not the external `~/Z3Lean`
  package), covering only the API surface the translator emits.

**Out of scope (YAGNI)**
- cvc5 / multi-solver support. The `feat/cvc5` branch is **parked**; no
  premature backend-abstraction typeclass is introduced.
- Full Z3 API coverage — only operators the translator actually emits.
- Reference-counted contexts / per-AST lifetime management.
- `push`/`pop` incremental solving — the translator uses assumption flags
  (`checkSatAssuming`), not push/pop.
- A differential test oracle (run-both-backends-and-compare). The existing
  `Tests/` suite already encodes the correct outcome for each `#blaster`
  (Valid / Falsified / Undetermined); that suite **is** the correctness oracle.

## 3. Key Facts Established (Phase 0)

A minimal FFI spike was built and run on **v4.24.0 against libz3 4.15.4**
(Homebrew `/opt/homebrew`). Results:

- FFI to Z3 works in a **compiled binary** *and* at **elaboration time**
  (the Lean interpreter — the exact mode `#blaster` runs in). Verified:
  scalar return, `String` marshalling (`Z3_ast_to_string`), and the
  **external-object + finalizer** ABI path (`del_context`). No segfault.
- `lake build` of an in-package module that imports a
  `precompileModules := true` library **auto-loads the shim dylib during
  elaboration**. (`lake env lean <file>` alone does **not** — it needs an
  explicit `--load-dynlib`.)
- Package-level `moreLinkArgs := #["-L…", "-lz3"]` is required so the Z3
  symbols reach the per-module dylibs; `extern_lib` alone does not propagate.

The `~/Z3Lean` package (full 39-group binding) is **not used**: it works on
v4.28 but segfaulted when retargeted to v4.24. The clean-v4.24 spike proves the
cause was Z3Lean's WIP lakefile rewrite, not the toolchain — but we build our
own minimal shim regardless (user decision).

## 4. Architecture

The existing Lean → `SmtCommand`/`SmtTerm` translation is **unchanged**. Only
the *consumer* of that AST changes: instead of rendering to text and streaming,
we interpret the AST against a live Z3 context.

### 4.1 Components

**C shim** — `Blaster/Smt/FFI/c/`
- `lean_z3.h` — box/unbox macros for external handles, `lean_io_result_mk_ok`
  wrappers, string marshalling helpers, a post-call error-check helper.
- `z3_shim_*.c`, grouped: context/error, sorts, numerals, bool/arith, bitvec,
  arrays, quantifiers, datatypes, funcdecl/apply, define/rec-def, solver,
  model, params, interrupt.

**Lean bindings** — `Blaster/Smt/FFI/*.lean`
- Opaque types `Z3Context`, `Z3Solver`, `Z3Sort`, `Z3Ast`, `Z3FuncDecl`,
  `Z3Model`, `Z3Symbol`, `Z3Params`, each an `@[extern]` declaration 1:1 with a
  shim function.

**Translation** — `Blaster/Smt/FFI/Build.lean` (the heart)
- `buildSort  : SortExpr → BuildM Z3Sort`
- `buildTerm  : SmtTerm  → BuildM Z3Ast`
- `runCommand : SmtCommand → BuildM Unit`
- `BuildM` carries a **build environment**: name → Z3 handle maps for declared
  sorts, constants, function decls, defined functions (as inlinable macros or
  rec-def decls), and datatype constructor/recognizer/accessor decls; plus a
  **scoped local env** for `let`- and quantifier-bound variables.

**Session** — `Blaster/Smt/FFI/Session.lean`
- `Z3Session := { ctx : Z3Context, solver : Z3Solver, buildEnv : IO.Ref …,
  topLevelVars : Array (SmtSymbol × Z3Ast) }`.
- Replaces `SmtEnv.smtProc : Option (IO.Process.Child …)`
  (`Blaster/Optimize/Env.lean:353`) with `Option Z3Session`.

### 4.2 The backend seam

Call sites (`Translate.main`, `StateMachine/BMC.lean`,
`StateMachine/KInduction.lean`, `StateMachine/StateMachine.lean`) keep their
shape; only the funnel functions they call are swapped:

| Today (string / process)                              | FFI replacement                                            |
|-------------------------------------------------------|------------------------------------------------------------|
| `setBlasterProcess` / `exitSmt`                       | `Session.create` / `Session.close` (or GC)                 |
| `submitCommand` + `.emit` (+ `success\n` handshake)   | `Session.runCommand` — build into session, **no handshake**|
| `getSatResult` (parse `sat\n`)                        | `Session.checkSat` → typed `Z3_lbool` → `Result`           |
| `getModel` / `evalTerm` (paren-counting)              | `Session.getModel` (`Z3_model_eval` + `ast_to_string`)     |
| `checkSatAssuming`                                    | `Session.checkAssumptions` (`Z3_solver_check_assumptions`) |
| `setTimeout` / `setMbqi` / …                          | `Z3_params` on the solver                                  |

`Result` keeps its shape (`Valid | Falsified (cex : List String) |
Undetermined`), and counterexamples remain `List String`, so downstream cex
display is untouched.

### 4.3 Data flow

1. A `#blaster` invocation reaches `Translate.main` (or a StateMachine driver).
2. `Session.create` makes a fresh `Z3_context` + `Z3_solver` (replacing
   `setBlasterProcess`).
3. The unchanged translation produces `SmtCommand`s. Each is interpreted by
   `Session.runCommand`, building Z3 objects into the session — no text, no
   handshake.
4. `checkSat` / `checkSatAssuming` invoke the solver in-process; the `Z3_lbool`
   maps directly to `Result`.
5. For a `Falsified` result, each `topLevelVar` is evaluated via
   `Z3_model_eval` + `Z3_ast_to_string`, producing the `List String` cex.
6. The context is released at end-of-query (GC finalizer or explicit close).

## 5. Memory Model

**Non-reference-counted context, one `Z3_context` per query.**

- Finalizers only on: `Z3Context` (`Z3_del_context`), `Z3Solver` and `Z3Model`
  (`Z3_solver_dec_ref` / `Z3_model_dec_ref`).
- `Z3Ast`, `Z3Sort`, `Z3FuncDecl`, `Z3Symbol` are **plain context-owned
  pointers with no finalizer**, valid until `del_context`.

**Invariants** (must be stated in code and upheld):
1. The `Z3Context` handle must remain reachable while any AST/sort/decl derived
   from it is live — these bare pointers do **not** retain the context, so an
   early GC of the context would dangle every derived handle.
2. With no per-AST `dec_ref`, every intermediate AST lives until `del_context`;
   peak memory holds the whole formula. Acceptable per-query, but relevant to
   the issue-#138 output-explosion cases — do not accumulate contexts across
   queries.

This deliberately avoids the full per-object refcounting of a general-purpose
binding; it is sound precisely because each query has a bounded lifetime and
ASTs never escape it.

## 6. Hard Parts (Designed Explicitly)

These are the places a hand-built binding most easily diverges; they are
scheduled **early** (see §9) rather than last.

### 6.1 `define-fun`
There is no `Z3_mk_define_fun`. Two mechanisms:
- **Inline by substitution (default).** Store the definition's parameters and a
  body-builder; at each `AppTerm` referencing the name, translate the arguments
  and build the body with parameters bound to those arguments (local env, or
  `Z3_substitute`). This matches SMT-LIB macro semantics (Z3 eliminates
  non-recursive `define-fun` by substitution). Covers the translator's helper
  wrappers: `@Int.ediv`, `@Int.emod`, `@Int.fdiv`, `@Int.fmod`, `@Int.tdiv`,
  `@Int.tmod`, `@Int.pow`, `@Int.toNat`, `@Nat.pow`, `@Nat.sub`, and the
  per-width BitVec `udiv`/`sdiv` wrappers.
- **Recursive definitions via `Z3_mk_rec_func_decl` + `Z3_add_rec_def`.** Used
  **only** when a definition (or a `defineFunsRec` group) genuinely references
  itself/the group. ⚠️ A rec-def is *axiomatized*, not eagerly unfolded, and can
  turn a currently-`unsat` query into `unknown`. Decision is per-definition:
  detect self/mutual reference in the body; non-recursive → inline.

### 6.2 Quantifiers
Use `Z3_mk_forall_const` / `Z3_mk_exists_const` / `Z3_mk_lambda_const` — bind an
array of **fresh constants** rather than De Bruijn indices (far simpler). For
each `SortedVar`: make a fresh `Z3_mk_const`, push into the local env, translate
the body, then bind. `Pattern` attributes → `Z3_mk_pattern`; weight / `:qid`
from `AnnotatedTerm` attributes.

### 6.3 `let`
`LetTerm` — translate the bindings, extend the local env, translate the body
with the bindings in scope (inline; loss of structural sharing is a perf detail,
not a correctness issue).

### 6.4 Datatypes
`declareDataType` / `declareMutualDataTypes` → `Z3_mk_constructor` +
`Z3_mk_datatype` / `Z3_mk_datatypes` (mutual). The returned constructor,
recognizer, and accessor `Z3_func_decl`s must be registered in the build env by
their SMT names. Fiddliest shim; required for the datatype-pair `SMTArray`
(data + size) model and any Lean inductive translation.

### 6.5 Cancellation
`Z3_solver_check` is a blocking C call, so the current "poll `cancelTk?` between
`getLine`s" cannot apply during it. Mirror the existing async structure: run the
check on `IO.asTask`, poll `Core.Context.cancelTk?` on the main thread, and on
cancellation call `Z3_solver_interrupt` (thread-safe) so the check returns
`undef`. Keep `:timeout` as a hard ceiling regardless.

### 6.6 Error handling
Register a **no-op Z3 error handler** (prevents Z3 from aborting the process —
verified in the spike), and poll `Z3_get_error_code` after build/solve steps,
converting a nonzero code to `IO.userError` via `Z3_get_error_msg`.

## 7. Options Mapping

`setOption` commands map onto a `Z3_params` object applied with
`Z3_solver_set_params`:

- `:timeout N` → `timeout` (uint, ms)
- random-seed → `random_seed`
- `:smt.mbqi`, `:smt.macro_finder`, `:auto_config`,
  `:smt.pull-nested-quantifiers` → corresponding module params
- `:produce-models` → moot (model fetched on demand)
- `:produce-proofs` → set at context/config time only if `getProof` is used
- `:print-success` → **removed entirely** (no handshake exists)

⚠️ Some module params (`auto_config`, `mbqi`, `macro_finder`,
`pull-nested-quantifiers`) historically must be set at config/global time or via
`Z3_global_param_set` *before* context creation, rather than on solver-level
`Z3_params`. Exact placement per option is a **phase-1 verification item**.

## 8. Build System

Proven by the phase-0 spike; to be reproduced in Blaster's `lakefile.lean`:

- `input_file` + per-file `target «*.o»` + one `extern_lib` bundling the shim
  `.o`s into a static lib.
- Package-level `moreLinkArgs := #["-L{Z3_LIB_PATH}", "-lz3"]`, with
  `Z3_LIB_PATH` resolved from the environment (default `/opt/homebrew/lib`) via
  the `implemented_by`/`opaque` pattern so the kernel sees a pure constant.
- C compile include flags: `-I {leanIncludeDir} -I {Z3_INC_PATH}` (default
  `/opt/homebrew/include`).
- `Blaster` already sets `precompileModules := true` — **required** so the
  elaborator auto-loads the shim dylib during `#blaster`.
- CI: install libz3 (brew on macOS; apt / release download on Linux) and ensure
  it is on the runtime dylib search path.

## 9. Migration & Testing

**Acceptance oracle:** the existing `Tests/` suite. Each `#blaster` test already
asserts its expected outcome (Valid / Falsified with a specific cex /
Undetermined). FFI parity for a feature = the tests exercising it pass under the
FFI backend. **No** separate run-both-and-compare harness is built.

**Keeping the tree green mid-migration:** the string/process backend remains the
working backend until the FFI backend passes the full suite; FFI is developed
behind the backend seam and switched on once complete. The dead
string/process/`.emit`/reader code is deleted in phase 3, after parity. The pure
`ToString` renderer is retained for the `dumpSmtLib` debug log (independent of
the solver path).

**Feature ordering:** land datatypes, `define-fun`/rec-def, and quantifier
binding **early** — that is where a hand-built binding quietly diverges.

## 10. Phasing

- **Phase 0 — De-risk. ✅ DONE.** FFI spike green on v4.24, compiled and at
  elaboration time; external-object/finalizer ABI confirmed.
- **Phase 1 — Infrastructure + core theory.** Shim build wired into Blaster's
  lakefile; `Z3Session`; sorts (Bool, Int, BitVec, Array, uninterpreted);
  numerals; bool/arith/bitvec/array operators; `declareConst`/`declareFun` +
  application; `assert`; `checkSat`; model eval. Replace the single-query flow
  (`Translate.main`). Verify **cross-package** consumption (a downstream
  `require` of Blaster auto-loads the shim dylib during its elaboration).
- **Phase 2 — Hard features.** Quantifiers (+ patterns / weight / qid); `let`;
  datatypes (including mutual); `define-fun` (inline) + rec-def; `defineSort`;
  `checkSatAssuming` for BMC / K-induction / StateMachine.
- **Phase 3 — Options, cancellation, cleanup.** Full options→params mapping;
  interrupt-based cancellation; `getProof` (if still needed); delete the dead
  string/process/`.emit`/reader code and the `wsl z3` PATH probe; update docs
  and CI.

## 11. Risks & Open Items

- **Options placement** (§7) — which params are solver-level vs. config/global.
  Resolve in phase 1.
- **Cross-package dylib auto-load** — proven in-package; the downstream
  `require` path is a standard Lake mechanism but must be confirmed in phase 1
  (Lean-blaster is consumed as a dependency by, e.g., the issue-#138 harness).
- **Datatype decl round-trip** — mapping Z3's generated constructor/accessor
  decls back to SMT names is error-prone; cover with focused tests first.
- **rec-def completeness regressions** (§6.1) — guard by defaulting to inline
  and only using rec-def for truly recursive definitions.
