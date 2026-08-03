#include "lean_z3.h"
#include <stdlib.h>
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
/* mkConst : Context → String → Z3Sort → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_const(b_lean_obj_arg c, b_lean_obj_arg name, b_lean_obj_arg srt, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  lean_object *r = box_owned(Z3_mk_const(ctx, sym, (Z3_sort)unbox_owned(srt)));
  lean_dec(c); lean_dec(name); lean_dec(srt);
  return z3_io_ok(r);
}
/* mkFuncDecl : Context → String → Array Z3Sort(domain) → Z3Sort(range) → IO FuncDecl */
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
  lean_object *r = box_owned(fd);
  lean_dec(c); lean_dec(name); lean_dec(dom); lean_dec(rng);
  return z3_io_ok(r);
}
/* mkApp : Context → FuncDecl → Array Ast → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_app(b_lean_obj_arg c, b_lean_obj_arg fd, b_lean_obj_arg args, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  size_t n = lean_array_size(args);
  Z3_ast *as = (Z3_ast *)malloc(sizeof(Z3_ast) * (n ? n : 1));
  for (size_t i = 0; i < n; i++) as[i] = (Z3_ast)unbox_owned(lean_array_get_core(args, i));
  Z3_ast res = Z3_mk_app(ctx, (Z3_func_decl)unbox_owned(fd), (unsigned)n, as);
  free(as);
  lean_object *r = box_owned(res);
  lean_dec(c); lean_dec(fd); lean_dec(args);
  return z3_io_ok(r);
}
