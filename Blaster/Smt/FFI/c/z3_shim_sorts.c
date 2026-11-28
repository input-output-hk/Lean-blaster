#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkBoolSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_bool_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; lean_object *r = box_owned(Z3_mk_bool_sort((Z3_context)ctx_ptr(c)));
  lean_dec(c); return z3_io_ok(r);
}
/* mkIntSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; lean_object *r = box_owned(Z3_mk_int_sort((Z3_context)ctx_ptr(c)));
  lean_dec(c); return z3_io_ok(r);
}
/* mkRealSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_real_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; lean_object *r = box_owned(Z3_mk_real_sort((Z3_context)ctx_ptr(c)));
  lean_dec(c); return z3_io_ok(r);
}
/* mkStringSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_string_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; lean_object *r = box_owned(Z3_mk_string_sort((Z3_context)ctx_ptr(c)));
  lean_dec(c); return z3_io_ok(r);
}
/* mkBvSort : Context → UInt32 → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_bv_sort(b_lean_obj_arg c, uint32_t width, lean_obj_arg w) {
  (void)w;
  lean_object *r = box_owned(Z3_mk_bv_sort((Z3_context)ctx_ptr(c), width));
  lean_dec(c); return z3_io_ok(r);
}
/* mkArraySort : Context → Z3Sort(domain) → Z3Sort(range) → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_array_sort(b_lean_obj_arg c, b_lean_obj_arg d, b_lean_obj_arg r, lean_obj_arg w) {
  (void)w;
  lean_object *res = box_owned(Z3_mk_array_sort((Z3_context)ctx_ptr(c),
    (Z3_sort)unbox_owned(d), (Z3_sort)unbox_owned(r)));
  lean_dec(c); lean_dec(d); lean_dec(r); return z3_io_ok(res);
}
/* mkUninterpretedSort : Context → String → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_uninterp_sort(b_lean_obj_arg c, b_lean_obj_arg name, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  lean_object *r = box_owned(Z3_mk_uninterpreted_sort(ctx, sym));
  lean_dec(c); lean_dec(name); return z3_io_ok(r);
}
