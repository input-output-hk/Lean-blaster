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

/* globalParamSet : String → String → IO Unit.
 * Wraps Z3_global_param_set (process-global / module param store). Used to install
 * the engine defaults (auto_config / smt.mbqi / smt.macro_finder /
 * smt.pull_nested_quantifiers) BEFORE context+solver creation, mirroring the legacy
 * subprocess `(set-option …)` semantics. Z3 copies the strings into its param store,
 * so both String args may be released after the call. Refcount: `id`/`val` are owned
 * OBJECT args → lean_dec after use (read their C strings first); `w` is never
 * decremented. */
LEAN_EXPORT lean_obj_res lean_z3_global_param_set(b_lean_obj_arg id, b_lean_obj_arg val, lean_obj_arg w) {
  (void)w;
  Z3_global_param_set(lean_string_cstr(id), lean_string_cstr(val));
  lean_dec(id);
  lean_dec(val);
  return z3_io_unit();
}

/* mkContext : IO Context */
LEAN_EXPORT lean_obj_res lean_z3_mk_context(lean_obj_arg w) {
  (void)w;
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_set_error_handler(ctx, z3_err_noop);
  return z3_io_ok(box_context((void *)ctx));
}

/* Shared accessor so other translation units can unbox a Context. */
void *ctx_ptr(lean_object *o) { return unbox_context(o); }

/* ctxErrorCode : Context → IO UInt32 (0 == OK) */
LEAN_EXPORT lean_obj_res lean_z3_ctx_error_code(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w;
  uint32_t code = (uint32_t)Z3_get_error_code((Z3_context)unbox_context(c));
  lean_dec(c);
  return z3_io_ok(lean_box_uint32(code));
}

/* ctxErrorMsg : Context → UInt32 → IO String */
LEAN_EXPORT lean_obj_res lean_z3_ctx_error_msg(b_lean_obj_arg c, uint32_t code, lean_obj_arg w) {
  (void)w;
  Z3_string m = Z3_get_error_msg((Z3_context)unbox_context(c), (Z3_error_code)code);
  lean_object *r = lean_mk_string(m ? m : "");
  lean_dec(c);
  return z3_io_ok(r);
}
