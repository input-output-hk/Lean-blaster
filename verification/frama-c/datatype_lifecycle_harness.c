/* Bounded lifecycle check of the production single-datatype constructors.
 * The allocator can fail at each of its C allocations. Lean and Z3 are
 * modeled at their API boundary; this is not a model of their internals.
 * Build with LZ3_TEST_RECURSIVE or LZ3_TEST_POLY for the other entry points. */
#include <stdlib.h>
void *test_malloc(size_t n);
#define malloc test_malloc
#include "../../Blaster/Smt/FFI/c/z3_shim_datatypes.c"
#undef malloc

static lean_object context_obj, sort_name_obj, ctor_name_obj, recog_name_obj;
static lean_object field_name_obj, field_sort_obj;
static lean_object ctor_names_obj, recog_names_obj, field_names_obj, field_sorts_obj;
static lean_object field_names_inner, field_sorts_inner;
static lean_object field_refs_obj, field_refs_inner, field_ref_obj;
static lean_object typevars_obj, typevar_obj;
static lean_object result_array, result_pair, boxed_obj, error_obj;
static lean_object *ctor_name_items[1], *recog_name_items[1];
static lean_object *field_name_items[1], *field_sort_items[1];
static lean_object *outer_field_name_items[1], *outer_field_sort_items[1];
static lean_object *outer_field_ref_items[1], *field_ref_items[1], *typevar_items[1];
static lean_object *result_items[3], *pair_items[2];
static char context_handle, sort_handle, constructor_handle, symbol_handle;
static char func_handle, class_handle;
static int fail_at, alloc_calls, constructor_failure, datatype_failure, query_failure;
static int live_constructors, constructors_created, constructors_deleted;
static int query_calls, returned_error, decs[8];

/*@ requires min <= max;
    assigns \result \from min, max;
    ensures min <= \result <= max; */
extern int Frama_C_interval(int min, int max);

void *test_malloc(size_t n) {
  /*@ assert live_constructors == 0; */
  ++alloc_calls;
  if (alloc_calls == fail_at) return NULL;
  return malloc(n);
}

void *ctx_ptr(lean_object *o) { return &context_handle; }
void *lean_get_external_data(lean_object *o) { return o->external_data; }
size_t lean_array_size(b_lean_obj_arg o) { return o->size; }
b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i) { return o->items[i]; }
const char *lean_string_cstr(b_lean_obj_arg o) { return o->string_data; }
void lean_dec(lean_object *o) {
  if (o == &context_obj) ++decs[0];
  if (o == &sort_name_obj) ++decs[1];
  if (o == &ctor_names_obj) ++decs[2];
  if (o == &recog_names_obj) ++decs[3];
  if (o == &field_names_obj) ++decs[4];
  if (o == &field_sorts_obj) ++decs[5];
  if (o == &field_refs_obj) ++decs[6];
  if (o == &typevars_obj) ++decs[7];
}
unsigned lean_unbox_uint32(b_lean_obj_arg o) { return 1; }
lean_external_class *lean_register_external_class(
    lean_external_finalize_proc finalize, lean_external_foreach_proc foreach) {
  return (lean_external_class *)&class_handle;
}
lean_object *lean_alloc_external(lean_external_class *cls, void *data) {
  boxed_obj.external_data = data;
  return &boxed_obj;
}
lean_obj_res lean_alloc_array(size_t size, size_t capacity) {
  /*@ assert size == 3; */
  result_array.size = size;
  result_array.items = result_items;
  return &result_array;
}
void lean_array_set_core(u_lean_obj_arg o, size_t i, lean_obj_arg v) {
  o->items[i] = v;
}
lean_obj_res lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
  result_pair.items = pair_items;
  return &result_pair;
}
void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) {
  o->items[i] = v;
}
lean_obj_res lean_mk_string(const char *s) { return &error_obj; }
lean_obj_res lean_mk_io_user_error(lean_obj_arg s) { return &error_obj; }
lean_obj_res lean_io_result_mk_error(lean_obj_arg e) {
  returned_error = 1;
  return &error_obj;
}
lean_obj_res lean_io_result_mk_ok(lean_obj_arg v) { return v; }

Z3_symbol Z3_mk_string_symbol(Z3_context c, Z3_string s) {
  return (Z3_symbol)&symbol_handle;
}
Z3_constructor Z3_mk_constructor(Z3_context c, Z3_symbol name,
    Z3_symbol recognizer, unsigned n, Z3_symbol const names[],
    Z3_sort const sorts[], unsigned refs[]) {
  if (constructor_failure) return NULL;
  ++live_constructors;
  ++constructors_created;
  return (Z3_constructor)&constructor_handle;
}
void Z3_del_constructor(Z3_context c, Z3_constructor con) {
  /*@ assert live_constructors == 1; */
  --live_constructors;
  ++constructors_deleted;
}
Z3_sort Z3_mk_datatype(Z3_context c, Z3_symbol name, unsigned n,
                       Z3_constructor constructors[]) {
  /*@ assert live_constructors == 1; */
  return datatype_failure ? NULL : (Z3_sort)&sort_handle;
}
Z3_sort Z3_mk_polymorphic_datatype(Z3_context c, Z3_symbol name,
    unsigned num_params, Z3_sort params[], unsigned num_constructors,
    Z3_constructor constructors[]) {
  /*@ assert num_params == 1 && num_constructors == 1 && live_constructors == 1; */
  return datatype_failure ? NULL : (Z3_sort)&sort_handle;
}
Z3_error_code Z3_get_error_code(Z3_context c) {
  return query_calls && query_failure ? Z3_INVALID_ARG : Z3_OK;
}
void Z3_query_constructor(Z3_context c, Z3_constructor con, unsigned n,
    Z3_func_decl *constructor, Z3_func_decl *tester,
    Z3_func_decl accessors[]) {
  /*@ assert live_constructors == 1; */
  ++query_calls;
  if (query_failure) return;
  *constructor = (Z3_func_decl)&func_handle;
  *tester = (Z3_func_decl)&func_handle;
  accessors[0] = (Z3_func_decl)&func_handle;
}

int main(void) {
  ctor_name_items[0] = &ctor_name_obj;
  recog_name_items[0] = &recog_name_obj;
  field_name_items[0] = &field_name_obj;
  field_sort_items[0] = &field_sort_obj;
  outer_field_name_items[0] = &field_names_inner;
  outer_field_sort_items[0] = &field_sorts_inner;
  outer_field_ref_items[0] = &field_refs_inner;
  field_ref_items[0] = &field_ref_obj;
  typevar_items[0] = &typevar_obj;
  ctor_names_obj.size = recog_names_obj.size = 1;
  field_names_obj.size = field_sorts_obj.size = 1;
  field_names_inner.size = field_sorts_inner.size = 1;
  field_refs_obj.size = field_refs_inner.size = typevars_obj.size = 1;
  ctor_names_obj.items = ctor_name_items;
  recog_names_obj.items = recog_name_items;
  field_names_obj.items = outer_field_name_items;
  field_sorts_obj.items = outer_field_sort_items;
  field_refs_obj.items = outer_field_ref_items;
  field_refs_inner.items = field_ref_items;
  typevars_obj.items = typevar_items;
  field_names_inner.items = field_name_items;
  field_sorts_inner.items = field_sort_items;
  sort_name_obj.string_data = "HarnessType";
  ctor_name_obj.string_data = "HarnessCtor";
  recog_name_obj.string_data = "is-HarnessCtor";
  field_name_obj.string_data = "field";
  field_sort_obj.external_data = &sort_handle;
  typevar_obj.external_data = &sort_handle;

  fail_at = Frama_C_interval(0, 6);
  constructor_failure = Frama_C_interval(0, 1);
  datatype_failure = Frama_C_interval(0, 1);
  query_failure = Frama_C_interval(0, 1);
  lean_object *result;
#ifdef LZ3_TEST_POLY
  result = lean_z3_mk_poly_datatype(&context_obj, &sort_name_obj,
      &typevars_obj, &ctor_names_obj, &recog_names_obj, &field_names_obj,
      &field_sorts_obj, &field_refs_obj, NULL);
#elif defined(LZ3_TEST_RECURSIVE)
  result = lean_z3_mk_datatype_rec(&context_obj, &sort_name_obj,
      &ctor_names_obj, &recog_names_obj, &field_names_obj,
      &field_sorts_obj, &field_refs_obj, NULL);
#else
  result = lean_z3_mk_datatype(&context_obj, &sort_name_obj,
      &ctor_names_obj, &recog_names_obj, &field_names_obj,
      &field_sorts_obj, NULL);
#endif
  /*@ assert live_constructors == 0; */
  /*@ assert constructors_created == constructors_deleted; */
  /*@ assert decs[0] == 1 && decs[1] == 1 && decs[2] == 1; */
  /*@ assert decs[3] == 1 && decs[4] == 1 && decs[5] == 1; */
#if defined(LZ3_TEST_RECURSIVE) || defined(LZ3_TEST_POLY)
  /*@ assert decs[6] == 1; */
#endif
#ifdef LZ3_TEST_POLY
  /*@ assert decs[7] == 1; */
#endif
  if (returned_error) {
    /*@ assert result == &error_obj; */
    /*@ assert query_calls <= 1; */
  } else {
#ifdef LZ3_TEST_POLY
    /*@ assert result == &boxed_obj; */
    /*@ assert query_calls == 0; */
#else
    /*@ assert result == &result_pair; */
    /*@ assert query_calls == 1; */
#endif
  }
  return 0;
}
