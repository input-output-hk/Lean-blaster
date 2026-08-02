#include "lean_z3.h"
extern void *ctx_ptr(lean_object *o);

/* mkBoolSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_bool_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_bool_sort((Z3_context)ctx_ptr(c))));
}
/* mkIntSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_int_sort((Z3_context)ctx_ptr(c))));
}
/* mkStringSort : Context → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_string_sort(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w; return z3_io_ok(box_owned(Z3_mk_string_sort((Z3_context)ctx_ptr(c))));
}
/* mkArraySort : Context → Z3Sort(domain) → Z3Sort(range) → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_array_sort(b_lean_obj_arg c, b_lean_obj_arg d, b_lean_obj_arg r, lean_obj_arg w) {
  (void)w;
  return z3_io_ok(box_owned(Z3_mk_array_sort((Z3_context)ctx_ptr(c),
    (Z3_sort)unbox_owned(d), (Z3_sort)unbox_owned(r))));
}
/* mkUninterpretedSort : Context → String → IO Z3Sort */
LEAN_EXPORT lean_obj_res lean_z3_mk_uninterp_sort(b_lean_obj_arg c, b_lean_obj_arg name, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  return z3_io_ok(box_owned(Z3_mk_uninterpreted_sort(ctx, sym)));
}
