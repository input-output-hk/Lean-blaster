#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkNumeral : Context → String(decimal) → Z3Sort → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_numeral(b_lean_obj_arg c, b_lean_obj_arg num, b_lean_obj_arg srt, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  lean_object *r = box_owned(Z3_mk_numeral(ctx, lean_string_cstr(num), (Z3_sort)unbox_owned(srt)));
  lean_dec(c); lean_dec(num); lean_dec(srt); return z3_io_ok(r);
}
/* mkBool : Context → Bool → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_bool(b_lean_obj_arg c, uint8_t b, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  lean_object *r = box_owned(b ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
  lean_dec(c); return z3_io_ok(r);
}
/* mkStringLit : Context → String → IO Ast  (raw content, no surrounding quotes) */
LEAN_EXPORT lean_obj_res lean_z3_mk_string(b_lean_obj_arg c, b_lean_obj_arg s, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  lean_object *r = box_owned(Z3_mk_string(ctx, lean_string_cstr(s)));
  lean_dec(c); lean_dec(s); return z3_io_ok(r);
}
