/* Two-sort mutual datatype lifecycle with failures at every C allocation,
 * either constructor/list creation, or Z3_mk_datatypes. The production shim is
 * included unchanged apart from routing malloc through a fault injector. */
#include <stdlib.h>
void *test_malloc(size_t n);
#define malloc test_malloc
#include "../../Blaster/Smt/FFI/c/z3_shim_datatypes.c"
#undef malloc

static lean_object context_obj, sort_name_obj[2], ctor_name_obj[2], recog_name_obj[2];
static lean_object sort_names, ctor_names, recog_names, field_names;
static lean_object field_sorts, field_refs;
static lean_object ctor_names_per[2], recog_names_per[2], field_names_per[2];
static lean_object field_sorts_per[2], field_refs_per[2];
static lean_object empty_fields[2], empty_sorts[2], empty_refs[2];
static lean_object *sort_name_items[2], *ctor_name_outer[2], *recog_name_outer[2];
static lean_object *field_name_outer[2], *field_sort_outer[2], *field_ref_outer[2];
static lean_object *ctor_name_items[2][1], *recog_name_items[2][1];
static lean_object *field_name_items[2][1], *field_sort_items[2][1];
static lean_object *field_ref_items[2][1];
static lean_object result_arrays[4], pair_obj, boxed_obj, error_obj;
static lean_object *result_items[4][2], *pair_items[2];
static char context_handle, symbol_handle, sort_handles[2];
static char constructor_handles[2], list_handles[2], func_handle, class_handle;
static int fail_at, alloc_calls, fail_constructor_at, fail_list_at;
static int fail_datatypes, fail_query_at, query_failed, constructor_attempts, list_attempts;
static int live_constructors, constructors_created, constructors_deleted;
static int live_lists, lists_created, lists_deleted, query_calls;
static int returned_error, array_allocations, decs[7];

/*@ requires min <= max;
    assigns \result \from min, max;
    ensures min <= \result <= max; */
extern int Frama_C_interval(int min, int max);

void *test_malloc(size_t n) {
  /*@ assert live_constructors == 0 && live_lists == 0; */
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
  if (o == &sort_names) ++decs[1];
  if (o == &ctor_names) ++decs[2];
  if (o == &recog_names) ++decs[3];
  if (o == &field_names) ++decs[4];
  if (o == &field_sorts) ++decs[5];
  if (o == &field_refs) ++decs[6];
}
lean_external_class *lean_register_external_class(
    lean_external_finalize_proc finalize, lean_external_foreach_proc foreach) {
  return (lean_external_class *)&class_handle;
}
lean_object *lean_alloc_external(lean_external_class *cls, void *data) {
  boxed_obj.external_data = data;
  return &boxed_obj;
}
lean_obj_res lean_alloc_array(size_t size, size_t capacity) {
  /*@ assert size == 2 && capacity == 2; */
  /*@ assert array_allocations < 4; */
  int i = array_allocations++;
  result_arrays[i].size = size;
  result_arrays[i].items = result_items[i];
  return &result_arrays[i];
}
void lean_array_set_core(u_lean_obj_arg o, size_t i, lean_obj_arg v) {
  o->items[i] = v;
}
lean_obj_res lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
  pair_obj.items = pair_items;
  return &pair_obj;
}
void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) { o->items[i] = v; }
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
  /*@ assert n == 0; */
  ++constructor_attempts;
  if (constructor_attempts == fail_constructor_at) return NULL;
  ++live_constructors;
  ++constructors_created;
  return (Z3_constructor)&constructor_handles[constructor_attempts-1];
}
void Z3_del_constructor(Z3_context c, Z3_constructor con) {
  /*@ assert live_constructors > 0; */
  --live_constructors;
  ++constructors_deleted;
}
Z3_constructor_list Z3_mk_constructor_list(Z3_context c, unsigned n,
                                           Z3_constructor const constructors[]) {
  /*@ assert n == 1; */
  ++list_attempts;
  if (list_attempts == fail_list_at) return NULL;
  ++live_lists;
  ++lists_created;
  return (Z3_constructor_list)&list_handles[list_attempts-1];
}
void Z3_del_constructor_list(Z3_context c, Z3_constructor_list list) {
  /*@ assert live_lists > 0; */
  --live_lists;
  ++lists_deleted;
}
void Z3_mk_datatypes(Z3_context c, unsigned n, Z3_symbol const names[],
                     Z3_sort sorts[], Z3_constructor_list lists[]) {
  /*@ assert n == 2 && live_constructors == 2 && live_lists == 2; */
  sorts[0] = (Z3_sort)&sort_handles[0];
  sorts[1] = (Z3_sort)&sort_handles[1];
}
Z3_error_code Z3_get_error_code(Z3_context c) {
  return fail_datatypes || query_failed ? Z3_INVALID_ARG : Z3_OK;
}
void Z3_query_constructor(Z3_context c, Z3_constructor con, unsigned n,
    Z3_func_decl *constructor, Z3_func_decl *tester,
    Z3_func_decl accessors[]) {
  /*@ assert n == 0 && live_constructors == 2 && live_lists == 2; */
  ++query_calls;
  if (query_calls == fail_query_at) { query_failed=1; return; }
  *constructor = (Z3_func_decl)&func_handle;
  *tester = (Z3_func_decl)&func_handle;
}

int main(void) {
  lean_object *outers[6] = { &sort_names, &ctor_names, &recog_names,
      &field_names, &field_sorts, &field_refs };
  lean_object **outer_items[6] = { sort_name_items, ctor_name_outer,
      recog_name_outer, field_name_outer, field_sort_outer, field_ref_outer };
  for (int k=0; k<6; ++k) {
    outers[k]->size = 2;
    outers[k]->items = outer_items[k];
  }
  for (int s=0; s<2; ++s) {
    sort_name_obj[s].string_data = "Sort";
    ctor_name_obj[s].string_data = "Ctor";
    recog_name_obj[s].string_data = "is-Ctor";
    sort_name_items[s] = &sort_name_obj[s];
    ctor_name_outer[s] = &ctor_names_per[s];
    recog_name_outer[s] = &recog_names_per[s];
    field_name_outer[s] = &field_names_per[s];
    field_sort_outer[s] = &field_sorts_per[s];
    field_ref_outer[s] = &field_refs_per[s];
    ctor_name_items[s][0] = &ctor_name_obj[s];
    recog_name_items[s][0] = &recog_name_obj[s];
    field_name_items[s][0] = &empty_fields[s];
    field_sort_items[s][0] = &empty_sorts[s];
    field_ref_items[s][0] = &empty_refs[s];
    ctor_names_per[s].size = recog_names_per[s].size = 1;
    field_names_per[s].size = field_sorts_per[s].size = field_refs_per[s].size = 1;
    ctor_names_per[s].items = ctor_name_items[s];
    recog_names_per[s].items = recog_name_items[s];
    field_names_per[s].items = field_name_items[s];
    field_sorts_per[s].items = field_sort_items[s];
    field_refs_per[s].items = field_ref_items[s];
  }
  fail_at = Frama_C_interval(0, 13);
  fail_constructor_at = Frama_C_interval(0, 2);
  fail_list_at = Frama_C_interval(0, 2);
  fail_datatypes = Frama_C_interval(0, 1);
  fail_query_at = Frama_C_interval(0, 2);
  lean_object *result = lean_z3_mk_datatypes(&context_obj, &sort_names,
      &ctor_names, &recog_names, &field_names, &field_sorts, &field_refs, NULL);
  /*@ assert live_constructors == 0 && live_lists == 0; */
  /*@ assert constructors_created == constructors_deleted; */
  /*@ assert lists_created == lists_deleted; */
  /*@ assert decs[0] == 1 && decs[1] == 1 && decs[2] == 1; */
  /*@ assert decs[3] == 1 && decs[4] == 1 && decs[5] == 1 && decs[6] == 1; */
  if (returned_error) {
    /*@ assert result == &error_obj && query_calls <= 2; */
  } else {
    /*@ assert result == &pair_obj && query_calls == 2; */
  }
  return 0;
}
