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

/* ==== Task 7: built-in operator shims ===================================== *
 * Refcount rule: every OBJECT arg (Context/Ast/Array) is passed OWNED, so each
 * shim lean_dec's it after extracting the Z3 pointer. Array elements obtained
 * via lean_array_get_core are BORROWED, so we dec the ARRAY once, never the
 * elements. box_owned uses a no-op finalizer (ASTs are context-owned). */

/* Collect a Z3_ast array from a Lean `Array Ast` (elements borrowed). */
static Z3_ast *lz3_collect(lean_object *arr, size_t *out_n) {
  size_t n = lean_array_size(arr); *out_n = n;
  Z3_ast *as = (Z3_ast *)malloc(sizeof(Z3_ast) * (n ? n : 1));
  for (size_t i = 0; i < n; i++) as[i] = (Z3_ast)unbox_owned(lean_array_get_core(arr, i));
  return as;
}
#define LZ3_VARIADIC(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg arr, lean_obj_arg w) { \
    (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); size_t n; Z3_ast *as=lz3_collect(arr,&n); \
    lean_object *r=box_owned(z3fn(ctx,(unsigned)n,as)); free(as); \
    lean_dec(c); lean_dec(arr); return z3_io_ok(r); }
#define LZ3_BINOP(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg w) { \
    (void)w; lean_object *r=box_owned(z3fn((Z3_context)ctx_ptr(c),(Z3_ast)unbox_owned(a),(Z3_ast)unbox_owned(b))); \
    lean_dec(c); lean_dec(a); lean_dec(b); return z3_io_ok(r); }
#define LZ3_UNOP(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) { \
    (void)w; lean_object *r=box_owned(z3fn((Z3_context)ctx_ptr(c),(Z3_ast)unbox_owned(a))); \
    lean_dec(c); lean_dec(a); return z3_io_ok(r); }

LZ3_VARIADIC(lean_z3_mk_and,        Z3_mk_and)
LZ3_VARIADIC(lean_z3_mk_or,         Z3_mk_or)
LZ3_VARIADIC(lean_z3_mk_add,        Z3_mk_add)
LZ3_VARIADIC(lean_z3_mk_mul,        Z3_mk_mul)
LZ3_VARIADIC(lean_z3_mk_sub,        Z3_mk_sub)
LZ3_VARIADIC(lean_z3_mk_distinct,   Z3_mk_distinct)
LZ3_VARIADIC(lean_z3_mk_seq_concat, Z3_mk_seq_concat)   /* str.++ */
LZ3_BINOP(lean_z3_mk_eq,      Z3_mk_eq)
LZ3_BINOP(lean_z3_mk_implies, Z3_mk_implies)
LZ3_BINOP(lean_z3_mk_lt,      Z3_mk_lt)
LZ3_BINOP(lean_z3_mk_le,      Z3_mk_le)
LZ3_BINOP(lean_z3_mk_gt,      Z3_mk_gt)
LZ3_BINOP(lean_z3_mk_ge,      Z3_mk_ge)
LZ3_BINOP(lean_z3_mk_idiv,    Z3_mk_div)
LZ3_BINOP(lean_z3_mk_mod,     Z3_mk_mod)
LZ3_BINOP(lean_z3_mk_power,   Z3_mk_power)
LZ3_BINOP(lean_z3_mk_select,  Z3_mk_select)
LZ3_BINOP(lean_z3_mk_str_lt,  Z3_mk_str_lt)             /* str.<  */
LZ3_BINOP(lean_z3_mk_str_le,  Z3_mk_str_le)             /* str.<= */
LZ3_UNOP(lean_z3_mk_not,        Z3_mk_not)
LZ3_UNOP(lean_z3_mk_real2int,   Z3_mk_real2int)     /* to_int  */
LZ3_UNOP(lean_z3_mk_seq_length, Z3_mk_seq_length)   /* str.len */
LZ3_UNOP(lean_z3_mk_neg,        Z3_mk_unary_minus)  /* unary - */

/* ite : c → t → e  (all Ast) */
LEAN_EXPORT lean_obj_res lean_z3_mk_ite(b_lean_obj_arg c, b_lean_obj_arg i, b_lean_obj_arg t, b_lean_obj_arg e, lean_obj_arg w) {
  (void)w; lean_object *r=box_owned(Z3_mk_ite((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(i),(Z3_ast)unbox_owned(t),(Z3_ast)unbox_owned(e)));
  lean_dec(c); lean_dec(i); lean_dec(t); lean_dec(e); return z3_io_ok(r);
}
/* store : a → i → v */
LEAN_EXPORT lean_obj_res lean_z3_mk_store(b_lean_obj_arg c, b_lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg v, lean_obj_arg w) {
  (void)w; lean_object *r=box_owned(Z3_mk_store((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(a),(Z3_ast)unbox_owned(i),(Z3_ast)unbox_owned(v)));
  lean_dec(c); lean_dec(a); lean_dec(i); lean_dec(v); return z3_io_ok(r);
}
/* str.replace : s → src → dst  (replaces FIRST occurrence) */
LEAN_EXPORT lean_obj_res lean_z3_mk_seq_replace(b_lean_obj_arg c, b_lean_obj_arg s, b_lean_obj_arg src, b_lean_obj_arg dst, lean_obj_arg w) {
  (void)w; lean_object *r=box_owned(Z3_mk_seq_replace((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(s),(Z3_ast)unbox_owned(src),(Z3_ast)unbox_owned(dst)));
  lean_dec(c); lean_dec(s); lean_dec(src); lean_dec(dst); return z3_io_ok(r);
}
/* int abs = ite(x>=0, x, -x) */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_abs(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); Z3_ast x=(Z3_ast)unbox_owned(a);
  Z3_sort is=Z3_mk_int_sort(ctx); Z3_ast zero=Z3_mk_int(ctx,0,is);
  lean_object *r=box_owned(Z3_mk_ite(ctx, Z3_mk_ge(ctx,x,zero), x, Z3_mk_unary_minus(ctx,x)));
  lean_dec(c); lean_dec(a); return z3_io_ok(r);
}
