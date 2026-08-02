#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkNumeral : Context → String(decimal) → Z3Sort → IO Ast */
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
/* mkStringLit : Context → String → IO Ast  (raw content, no surrounding quotes) */
LEAN_EXPORT lean_obj_res lean_z3_mk_string(b_lean_obj_arg c, b_lean_obj_arg s, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  return z3_io_ok(box_owned(Z3_mk_string(ctx, lean_string_cstr(s))));
}
