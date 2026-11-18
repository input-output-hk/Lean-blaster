#include "lean_z3.h"
#include <stdlib.h>
extern void *ctx_ptr(lean_object *o);

LEAN_Z3_DECLARE_CLASS(solver)
/* The finalizer needs the Z3_context, and Lean does not guarantee an order
 * between a struct's field finalizers. So the box OWNS a reference to the
 * boxed Context (ctx_obj): it keeps the Z3_context alive until the solver's own
 * finalizer has run Z3_solver_dec_ref, then releases it. `ctx` is the raw
 * handle cached out of ctx_obj for fast access by sctx(). */
typedef struct { Z3_context ctx; lean_object *ctx_obj; Z3_solver s; } z3_solver_box;
static void solver_finalize(void *p) {
  z3_solver_box *b = (z3_solver_box *)p;
  if (b) { Z3_solver_dec_ref(b->ctx, b->s); lean_dec(b->ctx_obj); free(b); }
}

/* Extract the context / solver handle out of a boxed Solver. */
static Z3_context sctx(lean_object *o){ return ((z3_solver_box*)unbox_solver(o))->ctx; }
static Z3_solver  ssol(lean_object *o){ return ((z3_solver_box*)unbox_solver(o))->s; }

/* mkSolver : Context → IO Solver */
LEAN_EXPORT lean_obj_res lean_z3_mk_solver(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_solver base = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, base);
  /* The SMT-LIB backend installs `(set-simplifier recfun-finder)` before
   * asserting anything.  Attach the same native simplifier to the fresh solver. */
  Z3_simplifier simp = Z3_mk_simplifier(ctx, "recfun-finder");
  if (!simp) {
    Z3_error_code e = Z3_get_error_code(ctx);
    lean_object *msg = lean_mk_string(Z3_get_error_msg(ctx, e));
    Z3_solver_dec_ref(ctx, base);
    lean_dec(c);
    return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  }
  Z3_simplifier_inc_ref(ctx, simp);
  Z3_solver s = Z3_solver_add_simplifier(ctx, base, simp);
  if (!s) {
    Z3_error_code e = Z3_get_error_code(ctx);
    lean_object *msg = lean_mk_string(Z3_get_error_msg(ctx, e));
    Z3_simplifier_dec_ref(ctx, simp);
    Z3_solver_dec_ref(ctx, base);
    lean_dec(c);
    return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  }
  Z3_solver_inc_ref(ctx, s);
  Z3_simplifier_dec_ref(ctx, simp);
  Z3_solver_dec_ref(ctx, base);
  z3_solver_box *b = (z3_solver_box *)malloc(sizeof(z3_solver_box));
  if (!b) {
    Z3_solver_dec_ref(ctx, s);
    lean_dec(c);
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("out of memory boxing Z3 solver")));
  }
  /* Take ownership of the Context arg (do NOT dec it): the box holds it in
   * ctx_obj and releases it in solver_finalize, so the Z3_context outlives the
   * solver regardless of Lean's field-finalizer order. */
  b->ctx = ctx; b->ctx_obj = c; b->s = s;
  lean_object *res = box_solver(b);
  return z3_io_ok(res);
}

/* solverAssert : Solver → Ast → IO Unit */
LEAN_EXPORT lean_obj_res lean_z3_solver_assert(b_lean_obj_arg s, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_solver_assert(sctx(s), ssol(s), (Z3_ast)unbox_owned(a));
  lean_dec(s); lean_dec(a); return z3_io_unit();
}

/* solverCheck : Solver → IO UInt32 (2 sat / 0 unsat / 1 unknown) */
LEAN_EXPORT lean_obj_res lean_z3_solver_check(b_lean_obj_arg s, lean_obj_arg w) {
  (void)w; Z3_lbool r = Z3_solver_check(sctx(s), ssol(s));
  lean_dec(s);
  return z3_io_ok(lean_box_uint32((r==Z3_L_TRUE)?2u:(r==Z3_L_FALSE?0u:1u)));
}

/* solverEvalToString : Solver → Ast → IO String ("" if no model / eval fails) */
LEAN_EXPORT lean_obj_res lean_z3_solver_eval_str(b_lean_obj_arg s, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_solver sol=ssol(s);
  Z3_model m = Z3_solver_get_model(ctx, sol);
  lean_object *res;
  if (!m) { res = lean_mk_string(""); }
  else {
    Z3_model_inc_ref(ctx, m);
    Z3_ast v; const char *out = "";
    if (Z3_model_eval(ctx, m, (Z3_ast)unbox_owned(a), true, &v)) out = Z3_ast_to_string(ctx, v);
    res = lean_mk_string(out);
    Z3_model_dec_ref(ctx, m);
  }
  lean_dec(s); lean_dec(a); return z3_io_ok(res);
}

/* Diagnostic fallback for models with no top-level Lean variable to evaluate. */
LEAN_EXPORT lean_obj_res lean_z3_solver_model_str(b_lean_obj_arg s, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = sctx(s);
  Z3_model m = Z3_solver_get_model(ctx, ssol(s));
  if (!m) {
    lean_dec(s);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Z3 returned no model")));
  }
  Z3_model_inc_ref(ctx, m);
  lean_object *res = lean_mk_string(Z3_model_to_string(ctx, m));
  Z3_model_dec_ref(ctx, m);
  lean_dec(s);
  return z3_io_ok(res);
}

/* Return the evaluated Z3 AST itself. It is context-owned; callers keep the
 * session (and thus the context) alive while inspecting it. */
LEAN_EXPORT lean_obj_res lean_z3_solver_eval_ast(b_lean_obj_arg s, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = sctx(s);
  Z3_model m = Z3_solver_get_model(ctx, ssol(s));
  if (!m) {
    lean_dec(s); lean_dec(a);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Z3 returned no model")));
  }
  Z3_model_inc_ref(ctx, m);
  Z3_ast v = NULL;
  bool ok = Z3_model_eval(ctx, m, (Z3_ast)unbox_owned(a), true, &v);
  lean_object *res = ok && v ? box_owned(v) : NULL;
  Z3_model_dec_ref(ctx, m);
  lean_dec(s); lean_dec(a);
  if (!res)
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Z3 model evaluation failed")));
  return z3_io_ok(res);
}

/* solverCheckAssuming : Solver → Array Ast → IO UInt32 (2 sat / 0 unsat / 1 unknown).
 * The assumption Asts are read out of the array via lean_array_get_core, so they are
 * BORROWED: dec the ARRAY once, never the elements; dec the Solver; scalars/world never. */
LEAN_EXPORT lean_obj_res lean_z3_solver_check_assuming(b_lean_obj_arg s, b_lean_obj_arg assumps, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_solver sol=ssol(s);
  size_t n=lean_array_size(assumps);
  Z3_ast *as=(Z3_ast*)malloc(sizeof(Z3_ast)*(n?n:1));
  for (size_t i=0;i<n;i++) as[i]=(Z3_ast)unbox_owned(lean_array_get_core(assumps,i));
  Z3_lbool r=Z3_solver_check_assumptions(ctx, sol, (unsigned)n, as);
  free(as);
  lean_dec(s); lean_dec(assumps);
  return z3_io_ok(lean_box_uint32((r==Z3_L_TRUE)?2u:(r==Z3_L_FALSE?0u:1u)));
}

/* solverSetTimeout : Solver → UInt32(ms) → IO Unit.
 * Builds a one-key Z3_params ("timeout", uint, milliseconds) and installs it on
 * the solver. `Z3_solver_set_params` accumulates keys across calls (verified: a
 * later seed-only call does not drop an earlier timeout), so timeout and seed can
 * be set independently. Refcount: `s` is an owned OBJECT arg → lean_dec after use;
 * the scalar `ms` and `w` are never decremented. */
LEAN_EXPORT lean_obj_res lean_z3_solver_set_timeout(b_lean_obj_arg s, uint32_t ms, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_params p=Z3_mk_params(ctx); Z3_params_inc_ref(ctx,p);
  Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx,"timeout"), ms);
  Z3_solver_set_params(ctx, ssol(s), p);
  Z3_params_dec_ref(ctx,p); lean_dec(s); return z3_io_unit();
}

/* solverSetRandomSeed : Solver → UInt32 → IO Unit.
 * Builds a one-key Z3_params ("random_seed", uint) and installs it on the solver.
 * Refcount: `s` is an owned OBJECT arg → lean_dec after use; scalar/world never. */
LEAN_EXPORT lean_obj_res lean_z3_solver_set_seed(b_lean_obj_arg s, uint32_t seed, lean_obj_arg w) {
  (void)w; Z3_context ctx=sctx(s); Z3_params p=Z3_mk_params(ctx); Z3_params_inc_ref(ctx,p);
  Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx,"random_seed"), seed);
  Z3_solver_set_params(ctx, ssol(s), p);
  Z3_params_dec_ref(ctx,p); lean_dec(s); return z3_io_unit();
}

/* solverInterrupt : Solver → IO Unit  (thread-safe; signals a running check to stop).
 * Called from a poll thread WHILE another thread runs Z3_solver_check on the same
 * solver — Z3_solver_interrupt is the sanctioned cross-thread call for this. Refcount:
 * `s` is an owned OBJECT arg (a distinct reference from the one the check holds) →
 * lean_dec after use; scalar/world never. */
LEAN_EXPORT lean_obj_res lean_z3_solver_interrupt(b_lean_obj_arg s, lean_obj_arg w) {
  (void)w; Z3_solver_interrupt(sctx(s), ssol(s)); lean_dec(s); return z3_io_unit();
}
