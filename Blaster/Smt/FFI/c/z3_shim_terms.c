#include "lean_z3.h"
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
extern void *ctx_ptr(lean_object *o);

/* Every array passed to Z3 has an unsigned element count. Keep the count and
 * allocation arithmetic checked before reading any Lean array element. */
static void *lz3_term_alloc(size_t n, size_t elem_size) {
  if (!elem_size || n > UINT_MAX || n > SIZE_MAX / elem_size) return NULL;
  return malloc((n ? n : 1) * elem_size);
}

static lean_obj_res lz3_term_error(const char *message) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/* Differential-test oracle only. The production backend builds every term
 * with constructors below; SMT-LIB parsing is used solely to compare ASTs. */
LEAN_EXPORT lean_obj_res lean_z3_parse_assert_for_test(b_lean_obj_arg c,
    b_lean_obj_arg script, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_ast_vector v = Z3_parse_smtlib2_string(ctx, lean_string_cstr(script),
      0, NULL, NULL, 0, NULL, NULL);
  Z3_error_code err = Z3_get_error_code(ctx);
  if (err != Z3_OK || !v) {
    lean_object *msg = lean_mk_string(Z3_get_error_msg(ctx, err));
    lean_dec(c); lean_dec(script);
    return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  }
  Z3_ast_vector_inc_ref(ctx, v);
  if (Z3_ast_vector_size(ctx, v) != 1) {
    Z3_ast_vector_dec_ref(ctx, v);
    lean_dec(c); lean_dec(script);
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("parity oracle expected exactly one assertion")));
  }
  lean_object *result = box_owned(Z3_ast_vector_get(ctx, v, 0));
  Z3_ast_vector_dec_ref(ctx, v);
  lean_dec(c); lean_dec(script);
  return z3_io_ok(result);
}

LEAN_EXPORT lean_obj_res lean_z3_ast_eq_for_test(b_lean_obj_arg c,
    b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg w) {
  (void)w;
  uint8_t equal = Z3_is_eq_ast((Z3_context)ctx_ptr(c),
      (Z3_ast)unbox_owned(a), (Z3_ast)unbox_owned(b));
  lean_dec(c); lean_dec(a); lean_dec(b);
  return z3_io_ok(lean_box(equal));
}

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
/* mkStringLit from Lean Unicode scalar values (no SMT-LIB escape decoding). */
LEAN_EXPORT lean_obj_res lean_z3_mk_u32_string(b_lean_obj_arg c, b_lean_obj_arg chars, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  size_t n = lean_array_size(chars);
  unsigned *codepoints = (unsigned *)lz3_term_alloc(n, sizeof(*codepoints));
  if (!codepoints) {
    lean_dec(c); lean_dec(chars);
    return lz3_term_error("too many Z3 string codepoints or out of memory");
  }
  for (size_t i = 0; i < n; ++i)
    codepoints[i] = lean_unbox_uint32(lean_array_get_core(chars, i));
  lean_object *r = box_owned(Z3_mk_u32string(ctx, (unsigned)n, codepoints));
  free(codepoints);
  lean_dec(c); lean_dec(chars); return z3_io_ok(r);
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
  Z3_sort *ds = (Z3_sort *)lz3_term_alloc(n, sizeof(*ds));
  if (!ds) {
    lean_dec(c); lean_dec(name); lean_dec(dom); lean_dec(rng);
    return lz3_term_error("too many Z3 function arguments or out of memory");
  }
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
  Z3_ast *as = (Z3_ast *)lz3_term_alloc(n, sizeof(*as));
  if (!as) {
    lean_dec(c); lean_dec(fd); lean_dec(args);
    return lz3_term_error("too many Z3 application arguments or out of memory");
  }
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
/*@ requires \valid_read(arr);
    requires \valid(out_n);
    requires \separated(out_n, arr);
    requires arr->size == 0 || \valid_read(arr->items + (0 .. arr->size-1));
    requires \forall size_t i; 0 <= i < arr->size ==> \valid_read(arr->items[i]);
    assigns *out_n;
    ensures *out_n == arr->size;
    ensures \result == \null || \valid(\result + (0 .. arr->size-1)); */
static Z3_ast *lz3_collect(lean_object *arr, size_t *out_n) {
  size_t n = lean_array_size(arr); *out_n = n;
  if (n > SIZE_MAX / sizeof(Z3_ast) || n > UINT_MAX) return NULL;
  Z3_ast *as = (Z3_ast *)malloc(sizeof(Z3_ast) * (n ? n : 1));
  if (!as) return NULL;
  /*@ loop invariant 0 <= i <= n;
      loop invariant \valid(as + (0 .. n-1));
      loop assigns i, as[0 .. n-1];
      loop variant n - i; */
  for (size_t i = 0; i < n; i++) as[i] = (Z3_ast)unbox_owned(lean_array_get_core(arr, i));
  return as;
}
#define LZ3_VARIADIC(fn, z3fn) \
  LEAN_EXPORT lean_obj_res fn(b_lean_obj_arg c, b_lean_obj_arg arr, lean_obj_arg w) { \
    (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); size_t n; Z3_ast *as=lz3_collect(arr,&n); \
    if (!as) { lean_dec(c); lean_dec(arr); return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("out of memory collecting Z3 terms"))); } \
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

/* Bit-vector operators use the same owned-handle convention as arithmetic. */
LZ3_BINOP(lean_z3_mk_bvadd,  Z3_mk_bvadd)
LZ3_BINOP(lean_z3_mk_bvsub,  Z3_mk_bvsub)
LZ3_BINOP(lean_z3_mk_bvmul,  Z3_mk_bvmul)
LZ3_BINOP(lean_z3_mk_bvudiv, Z3_mk_bvudiv)
LZ3_BINOP(lean_z3_mk_bvsdiv, Z3_mk_bvsdiv)
LZ3_BINOP(lean_z3_mk_bvurem, Z3_mk_bvurem)
LZ3_BINOP(lean_z3_mk_bvsrem, Z3_mk_bvsrem)
LZ3_BINOP(lean_z3_mk_bvsmod, Z3_mk_bvsmod)
LZ3_BINOP(lean_z3_mk_bvshl,  Z3_mk_bvshl)
LZ3_BINOP(lean_z3_mk_bvlshr, Z3_mk_bvlshr)
LZ3_BINOP(lean_z3_mk_bvashr, Z3_mk_bvashr)
LZ3_BINOP(lean_z3_mk_bvor,   Z3_mk_bvor)
LZ3_BINOP(lean_z3_mk_bvand,  Z3_mk_bvand)
LZ3_BINOP(lean_z3_mk_bvnand, Z3_mk_bvnand)
LZ3_BINOP(lean_z3_mk_bvnor,  Z3_mk_bvnor)
LZ3_BINOP(lean_z3_mk_bvxnor, Z3_mk_bvxnor)
LZ3_BINOP(lean_z3_mk_concat, Z3_mk_concat)
LZ3_BINOP(lean_z3_mk_bvule,  Z3_mk_bvule)
LZ3_BINOP(lean_z3_mk_bvult,  Z3_mk_bvult)
LZ3_BINOP(lean_z3_mk_bvuge,  Z3_mk_bvuge)
LZ3_BINOP(lean_z3_mk_bvugt,  Z3_mk_bvugt)
LZ3_BINOP(lean_z3_mk_bvsle,  Z3_mk_bvsle)
LZ3_BINOP(lean_z3_mk_bvslt,  Z3_mk_bvslt)
LZ3_BINOP(lean_z3_mk_bvsge,  Z3_mk_bvsge)
LZ3_BINOP(lean_z3_mk_bvsgt,  Z3_mk_bvsgt)
LZ3_UNOP(lean_z3_mk_bvneg,   Z3_mk_bvneg)
LZ3_UNOP(lean_z3_mk_bvnot,   Z3_mk_bvnot)

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
/* str.replace_all : s → src → dst */
LEAN_EXPORT lean_obj_res lean_z3_mk_seq_replace_all(b_lean_obj_arg c, b_lean_obj_arg s, b_lean_obj_arg src, b_lean_obj_arg dst, lean_obj_arg w) {
  (void)w; lean_object *r=box_owned(Z3_mk_seq_replace_all((Z3_context)ctx_ptr(c),
    (Z3_ast)unbox_owned(s),(Z3_ast)unbox_owned(src),(Z3_ast)unbox_owned(dst)));
  lean_dec(c); lean_dec(s); lean_dec(src); lean_dec(dst); return z3_io_ok(r);
}
/* Preserve SMT-LIB's native arithmetic abs node. */
LEAN_EXPORT lean_obj_res lean_z3_mk_int_abs(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c); Z3_ast x=(Z3_ast)unbox_owned(a);
  lean_object *r=box_owned(Z3_mk_abs(ctx,x));
  lean_dec(c); lean_dec(a); return z3_io_ok(r);
}

/* ==== Task 10: quantifier shims ========================================== *
 * Binders use Z3_mk_fresh_const (NOT Z3_mk_const): fresh consts are distinct,
 * so a bound var never hash-collides with a same-named top-level const or an
 * outer shadowed binder. Refcount rule as above: dec each OBJECT arg once
 * (arrays once; their elements from lean_array_get_core are borrowed). */

/* mkFreshConst : Context → String(prefix) → Z3Sort → IO Ast  (a distinct constant each call) */
LEAN_EXPORT lean_obj_res lean_z3_mk_fresh_const(b_lean_obj_arg c, b_lean_obj_arg prefix, b_lean_obj_arg srt, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  lean_object *r=box_owned(Z3_mk_fresh_const(ctx, lean_string_cstr(prefix), (Z3_sort)unbox_owned(srt)));
  lean_dec(c); lean_dec(prefix); lean_dec(srt); return z3_io_ok(r);
}
/* mkQuantConst : Context → isForall(Bool) → weight(UInt32) → qid(String)
 *   → Array String(source binder names) → Array Ast(fresh bound consts)
 *   → Array Ast(patterns) → Ast(body) → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_quant_const(b_lean_obj_arg c, uint8_t isForall, uint32_t weight,
    b_lean_obj_arg qid, b_lean_obj_arg names,
    b_lean_obj_arg bounds, b_lean_obj_arg pats, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t nb=lean_array_size(bounds);
  if (lean_array_size(names) != nb) {
    lean_dec(c); lean_dec(qid); lean_dec(names); lean_dec(bounds); lean_dec(pats); lean_dec(body);
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("quantifier binder names/terms length mismatch")));
  }
  size_t np=lean_array_size(pats);
  Z3_app *bs=(Z3_app*)lz3_term_alloc(nb, sizeof(*bs));
  Z3_pattern *ps=(Z3_pattern*)lz3_term_alloc(np, sizeof(*ps));
  Z3_sort *sorts=(Z3_sort*)lz3_term_alloc(nb, sizeof(*sorts));
  Z3_symbol *symbols=(Z3_symbol*)lz3_term_alloc(nb, sizeof(*symbols));
  Z3_pattern *qp=NULL;
  const char *allocation_error=NULL;
  if (!bs || !ps || !sorts || !symbols) {
    free(bs); free(ps); free(sorts); free(symbols);
    lean_dec(c); lean_dec(qid); lean_dec(names); lean_dec(bounds); lean_dec(pats); lean_dec(body);
    return lz3_term_error("too many Z3 quantifier binders/patterns or out of memory");
  }
  for (size_t i=0;i<nb;i++) bs[i]=Z3_to_app(ctx,(Z3_ast)unbox_owned(lean_array_get_core(bounds,i)));
  for (size_t i=0;i<np;i++){
    Z3_ast pt=(Z3_ast)unbox_owned(lean_array_get_core(pats,i));
    ps[i]=Z3_mk_pattern(ctx,1,&pt);
    if (Z3_get_error_code(ctx) == Z3_INVALID_PATTERN) { np=0; break; }
  }
  const char *qidStr = lean_string_cstr(qid);
  Z3_symbol qidSym = qidStr[0] ? Z3_mk_string_symbol(ctx, qidStr) : NULL;
  Z3_ast r=Z3_mk_quantifier_const_ex(ctx, isForall?true:false, weight, qidSym, NULL,
      (unsigned)nb, bs, (unsigned)np, ps, 0, NULL, (Z3_ast)unbox_owned(body));
  Z3_error_code err = Z3_get_error_code(ctx);
  if (err == Z3_INVALID_PATTERN) {
    /* The SMT-LIB parser warns and discards a pattern that does not cover all
     * quantified variables. Apply the same rule to the native constructor. */
    r=Z3_mk_quantifier_const_ex(ctx, isForall?true:false, weight, qidSym, NULL,
        (unsigned)nb, bs, 0, NULL, 0, NULL, (Z3_ast)unbox_owned(body));
    err=Z3_get_error_code(ctx);
  }
  if (err == Z3_OK && r) {
    /* Z3_mk_quantifier_const_ex abstracts the fresh constants safely, but
     * copies their generated names (x!0) into the quantifier. Rebuild from
     * that abstracted body and its abstracted patterns using the source names
     * so the AST matches the SMT-LIB parser without capturing outer terms. */
    for (size_t i=0;i<nb;i++) {
      sorts[i]=Z3_get_quantifier_bound_sort(ctx,r,(unsigned)i);
      symbols[i]=Z3_mk_string_symbol(ctx,
          lean_string_cstr(lean_array_get_core(names,i)));
    }
    unsigned nqp=Z3_get_quantifier_num_patterns(ctx,r);
    qp=(Z3_pattern*)lz3_term_alloc(nqp, sizeof(*qp));
    if (!qp) {
      allocation_error="out of memory collecting Z3 quantifier patterns";
      goto quantifier_cleanup;
    }
    for (unsigned i=0;i<nqp;i++) qp[i]=Z3_get_quantifier_pattern_ast(ctx,r,i);
    Z3_ast abstractBody=Z3_get_quantifier_body(ctx,r);
    r=Z3_mk_quantifier_ex(ctx,isForall?true:false,weight,qidSym,NULL,
        nqp,qp,0,NULL,(unsigned)nb,sorts,symbols,abstractBody);
    err=Z3_get_error_code(ctx);
  }
quantifier_cleanup:
  ;
  lean_object *msg = err == Z3_OK ? NULL : lean_mk_string(Z3_get_error_msg(ctx, err));
  if (allocation_error) msg=lean_mk_string(allocation_error);
  free(qp); free(bs); free(ps); free(sorts); free(symbols);
  lean_object *res = msg ? NULL : box_owned(r);
  lean_dec(c); lean_dec(qid); lean_dec(names); lean_dec(bounds); lean_dec(pats); lean_dec(body);
  if (msg) return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  return z3_io_ok(res);
}
/* mkLambdaConst : Context → Array Ast(bound) → Ast(body) → IO Ast */
LEAN_EXPORT lean_obj_res lean_z3_mk_lambda_const(b_lean_obj_arg c, b_lean_obj_arg bounds, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t nb=lean_array_size(bounds);
  Z3_app *bs=(Z3_app*)lz3_term_alloc(nb, sizeof(*bs));
  if (!bs) {
    lean_dec(c); lean_dec(bounds); lean_dec(body);
    return lz3_term_error("too many Z3 lambda binders or out of memory");
  }
  for (size_t i=0;i<nb;i++) bs[i]=Z3_to_app(ctx,(Z3_ast)unbox_owned(lean_array_get_core(bounds,i)));
  Z3_ast r=Z3_mk_lambda_const(ctx,(unsigned)nb,bs,(Z3_ast)unbox_owned(body));
  free(bs);
  lean_object *res=box_owned(r);
  lean_dec(c); lean_dec(bounds); lean_dec(body); return z3_io_ok(res);
}

/* ==== Task 13: recursive define-fun shims ================================= *
 * Refcount rule as above: dec each OBJECT arg once (arrays once; their elements
 * from lean_array_get_core are borrowed). Scalars/world are never dec'd. */

/* mkRecFuncDecl : Context → String → Array Z3Sort(dom) → Z3Sort(rng) → IO FuncDecl */
LEAN_EXPORT lean_obj_res lean_z3_mk_rec_func_decl(b_lean_obj_arg c, b_lean_obj_arg name,
    b_lean_obj_arg dom, b_lean_obj_arg rng, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t n=lean_array_size(dom);
  Z3_sort *ds=(Z3_sort*)lz3_term_alloc(n, sizeof(*ds));
  if (!ds) {
    lean_dec(c); lean_dec(name); lean_dec(dom); lean_dec(rng);
    return lz3_term_error("too many Z3 recursive function arguments or out of memory");
  }
  for (size_t i=0;i<n;i++) ds[i]=(Z3_sort)unbox_owned(lean_array_get_core(dom,i));
  Z3_symbol sym=Z3_mk_string_symbol(ctx, lean_string_cstr(name));
  Z3_func_decl fd=Z3_mk_rec_func_decl(ctx, sym, (unsigned)n, ds, (Z3_sort)unbox_owned(rng));
  free(ds);
  lean_object *r=box_owned(fd);
  lean_dec(c); lean_dec(name); lean_dec(dom); lean_dec(rng); return z3_io_ok(r);
}
/* addRecDef : Context → FuncDecl → Array Ast(args) → Ast(body) → IO Unit */
LEAN_EXPORT lean_obj_res lean_z3_add_rec_def(b_lean_obj_arg c, b_lean_obj_arg fd,
    b_lean_obj_arg args, b_lean_obj_arg body, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  size_t n=lean_array_size(args);
  Z3_ast *as=(Z3_ast*)lz3_term_alloc(n, sizeof(*as));
  if (!as) {
    lean_dec(c); lean_dec(fd); lean_dec(args); lean_dec(body);
    return lz3_term_error("too many Z3 recursive arguments or out of memory");
  }
  for (size_t i=0;i<n;i++) as[i]=(Z3_ast)unbox_owned(lean_array_get_core(args,i));
  Z3_add_rec_def(ctx, (Z3_func_decl)unbox_owned(fd), (unsigned)n, as, (Z3_ast)unbox_owned(body));
  Z3_error_code err = Z3_get_error_code(ctx);
  lean_object *msg = err == Z3_OK ? NULL : lean_mk_string(Z3_get_error_msg(ctx, err));
  free(as);
  lean_dec(c); lean_dec(fd); lean_dec(args); lean_dec(body);
  if (msg) return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  return z3_io_unit();
}

/* Native model AST inspection. No SMT-LIB serialization is involved except
 * astToString, which is retained only as a diagnostic fallback. */
LEAN_EXPORT lean_obj_res lean_z3_ast_to_string(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  const char *s = Z3_ast_to_string((Z3_context)ctx_ptr(c), (Z3_ast)unbox_owned(a));
  lean_object *r = lean_mk_string(s ? s : "");
  lean_dec(c); lean_dec(a); return z3_io_ok(r);
}
LEAN_EXPORT lean_obj_res lean_z3_ast_is_string(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  bool b = Z3_is_string((Z3_context)ctx_ptr(c), (Z3_ast)unbox_owned(a));
  lean_dec(c); lean_dec(a); return z3_io_ok(lean_box(b ? 1 : 0));
}
LEAN_EXPORT lean_obj_res lean_z3_ast_get_string_codepoints(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_ast ast = (Z3_ast)unbox_owned(a);
  unsigned n = Z3_get_string_length(ctx, ast);
  unsigned *contents = (unsigned *)lz3_term_alloc(n, sizeof(*contents));
  if (!contents) {
    lean_dec(c); lean_dec(a);
    return lz3_term_error("too many Z3 string codepoints or out of memory");
  }
  Z3_get_string_contents(ctx, ast, n, contents);
  lean_object *arr = lean_alloc_array(0, n);
  for (unsigned i = 0; i < n; ++i) arr = lean_array_push(arr, lean_box_uint32(contents[i]));
  free(contents);
  lean_dec(c); lean_dec(a); return z3_io_ok(arr);
}
LEAN_EXPORT lean_obj_res lean_z3_ast_is_numeral(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  bool b = Z3_get_ast_kind((Z3_context)ctx_ptr(c), (Z3_ast)unbox_owned(a)) == Z3_NUMERAL_AST;
  lean_dec(c); lean_dec(a); return z3_io_ok(lean_box(b ? 1 : 0));
}
LEAN_EXPORT lean_obj_res lean_z3_ast_get_numeral(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  const char *s = Z3_get_numeral_string((Z3_context)ctx_ptr(c), (Z3_ast)unbox_owned(a));
  lean_object *r = lean_mk_string(s ? s : "");
  lean_dec(c); lean_dec(a); return z3_io_ok(r);
}
LEAN_EXPORT lean_obj_res lean_z3_ast_is_app(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  bool b = Z3_get_ast_kind((Z3_context)ctx_ptr(c), (Z3_ast)unbox_owned(a)) == Z3_APP_AST;
  lean_dec(c); lean_dec(a); return z3_io_ok(lean_box(b ? 1 : 0));
}
LEAN_EXPORT lean_obj_res lean_z3_ast_get_decl_name(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, (Z3_ast)unbox_owned(a)));
  Z3_symbol sym = Z3_get_decl_name(ctx, d);
  lean_object *r;
  if (Z3_get_symbol_kind(ctx, sym) == Z3_STRING_SYMBOL)
    r = lean_mk_string(Z3_get_symbol_string(ctx, sym));
  else {
    char buf[32];
    snprintf(buf, sizeof(buf), "%d", Z3_get_symbol_int(ctx, sym));
    r = lean_mk_string(buf);
  }
  lean_dec(c); lean_dec(a); return z3_io_ok(r);
}
LEAN_EXPORT lean_obj_res lean_z3_ast_get_args(b_lean_obj_arg c, b_lean_obj_arg a, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_app app = Z3_to_app(ctx, (Z3_ast)unbox_owned(a));
  unsigned n = Z3_get_app_num_args(ctx, app);
  lean_object *arr = lean_alloc_array(0, n);
  for (unsigned i = 0; i < n; ++i)
    arr = lean_array_push(arr, box_owned(Z3_get_app_arg(ctx, app, i)));
  lean_dec(c); lean_dec(a); return z3_io_ok(arr);
}
