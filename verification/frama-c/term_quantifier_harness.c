/* Exercise the production quantifier shim with a failed allocation at each
 * temporary C buffer, including the pattern buffer allocated after Z3 work. */
#include <stdlib.h>
void *test_malloc(size_t n);
void test_free(void *p);
#define malloc test_malloc
#define free test_free
#include "../../Blaster/Smt/FFI/c/z3_shim_terms.c"
#undef malloc
#undef free

static lean_object context_obj, qid_obj, names_obj, bounds_obj, pats_obj, body_obj;
static lean_object name_obj, bound_obj, pattern_obj, boxed_obj, error_obj;
static lean_object *name_items[1], *bound_items[1], *pattern_items[1];
static char context_handle, symbol_handle, ast_handle, app_handle, pattern_handle;
static char sort_handle, class_handle;
static int fail_at, alloc_calls, allocations, frees, decs[6];
static int returned_error, quantifier_calls;

#ifndef LZ3_FAIL_AT
#define LZ3_FAIL_AT 0
#endif

void *test_malloc(size_t n) {
  ++alloc_calls;
  if (alloc_calls == fail_at) return NULL;
  ++allocations;
  return malloc(n);
}
void test_free(void *p) {
  if (p) ++frees;
  free(p);
}
void *ctx_ptr(lean_object *o) { return &context_handle; }
void *lean_get_external_data(lean_object *o) { return o->external_data; }
size_t lean_array_size(b_lean_obj_arg o) { return o->size; }
b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i) { return o->items[i]; }
const char *lean_string_cstr(b_lean_obj_arg o) { return o->string_data; }
void lean_dec(lean_object *o) {
  if (o == &context_obj) ++decs[0];
  if (o == &qid_obj) ++decs[1];
  if (o == &names_obj) ++decs[2];
  if (o == &bounds_obj) ++decs[3];
  if (o == &pats_obj) ++decs[4];
  if (o == &body_obj) ++decs[5];
}
lean_external_class *lean_register_external_class(
    lean_external_finalize_proc finalize, lean_external_foreach_proc foreach) {
  return (lean_external_class *)&class_handle;
}
lean_object *lean_alloc_external(lean_external_class *cls, void *data) {
  boxed_obj.external_data = data;
  return &boxed_obj;
}
lean_obj_res lean_mk_string(const char *s) { return &error_obj; }
lean_obj_res lean_mk_io_user_error(lean_obj_arg s) { return &error_obj; }
lean_obj_res lean_io_result_mk_error(lean_obj_arg e) {
  returned_error=1;
  return &error_obj;
}
lean_obj_res lean_io_result_mk_ok(lean_obj_arg v) { return v; }

Z3_app Z3_to_app(Z3_context c, Z3_ast a) { return (Z3_app)&app_handle; }
Z3_pattern Z3_mk_pattern(Z3_context c, unsigned n, Z3_ast const terms[]) {
  /*@ assert n == 1; */
  return (Z3_pattern)&pattern_handle;
}
Z3_error_code Z3_get_error_code(Z3_context c) { return Z3_OK; }
Z3_symbol Z3_mk_string_symbol(Z3_context c, Z3_string name) {
  return (Z3_symbol)&symbol_handle;
}
Z3_ast Z3_mk_quantifier_const_ex(Z3_context c, bool forall, unsigned weight,
    Z3_symbol qid, Z3_symbol skid, unsigned nb, Z3_app const bounds[],
    unsigned np, Z3_pattern const patterns[], unsigned nn,
    Z3_ast const no_patterns[], Z3_ast body) {
  /*@ assert nb == 1 && np == 1; */
  ++quantifier_calls;
  return (Z3_ast)&ast_handle;
}
Z3_sort Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned i) {
  return (Z3_sort)&sort_handle;
}
unsigned Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a) { return 1; }
Z3_pattern Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned i) {
  return (Z3_pattern)&pattern_handle;
}
Z3_ast Z3_get_quantifier_body(Z3_context c, Z3_ast a) { return (Z3_ast)&ast_handle; }
Z3_ast Z3_mk_quantifier_ex(Z3_context c, bool forall, unsigned weight,
    Z3_symbol qid, Z3_symbol skid, unsigned np, Z3_pattern const patterns[],
    unsigned nn, Z3_ast const no_patterns[], unsigned nb,
    Z3_sort const sorts[], Z3_symbol const names[], Z3_ast body) {
  /*@ assert nb == 1 && np == 1; */
  ++quantifier_calls;
  return (Z3_ast)&ast_handle;
}

int main(void) {
  name_items[0]=&name_obj;
  bound_items[0]=&bound_obj;
  pattern_items[0]=&pattern_obj;
  names_obj.size=bounds_obj.size=pats_obj.size=1;
  names_obj.items=name_items;
  bounds_obj.items=bound_items;
  pats_obj.items=pattern_items;
  qid_obj.string_data="q";
  name_obj.string_data="x";
  bound_obj.external_data=&ast_handle;
  pattern_obj.external_data=&ast_handle;
  body_obj.external_data=&ast_handle;
  fail_at=LZ3_FAIL_AT;
  lean_object *result=lean_z3_mk_quant_const(&context_obj,1,0,&qid_obj,
      &names_obj,&bounds_obj,&pats_obj,&body_obj,NULL);
  if (fail_at == 0) {
    /*@ assert allocations == 5 && frees == 5; */
  } else if (fail_at <= 4) {
    /*@ assert allocations == 3 && frees == 3; */
  } else {
    /*@ assert allocations == 4 && frees == 4; */
  }
  /*@ assert decs[0] == 1 && decs[1] == 1 && decs[2] == 1; */
  /*@ assert decs[3] == 1 && decs[4] == 1 && decs[5] == 1; */
  if (returned_error) {
    /*@ assert result == &error_obj; */
  } else {
    /*@ assert result == &boxed_obj && quantifier_calls == 2; */
  }
  return 0;
}
