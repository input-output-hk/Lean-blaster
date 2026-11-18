/* Exercise the production datatype shape preflight against well-formed and
 * malformed parallel Lean arrays. This models logical array contents, not the
 * physical Lean object layout or Z3 constructor semantics. */
#include "../../Blaster/Smt/FFI/c/z3_shim_datatypes.c"

static lean_object ctor_name, recog_name, field_name, field_sort, field_ref;
static lean_object ctor_names, recog_names, field_names, field_sorts, field_refs;
static lean_object one_ctor_fields, one_ctor_sorts, one_ctor_refs;
static lean_object sort_names, mutual_ctor_names, mutual_recog_names;
static lean_object mutual_field_names, mutual_field_sorts, mutual_field_refs;
static lean_object *one_ctor_name_items[1], *one_recog_name_items[1];
static lean_object *one_field_name_items[1], *one_field_sort_items[1];
static lean_object *one_field_ref_items[1];
static lean_object *one_ctor_field_items[1], *one_ctor_sort_items[1];
static lean_object *one_ctor_ref_items[1];
static lean_object *one_sort_name_items[1];
static lean_object *mutual_ctor_name_items[1], *mutual_recog_name_items[1];
static lean_object *mutual_field_name_items[1], *mutual_field_sort_items[1];
static lean_object *mutual_field_ref_items[1];

size_t lean_array_size(b_lean_obj_arg o) { return o->size; }
b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i) { return o->items[i]; }
unsigned lean_unbox_uint32(b_lean_obj_arg o) { return (unsigned)o->size; }

int main(void) {
  one_ctor_name_items[0] = &ctor_name;
  one_recog_name_items[0] = &recog_name;
  one_field_name_items[0] = &field_name;
  one_field_sort_items[0] = &field_sort;
  one_field_ref_items[0] = &field_ref;
  one_ctor_field_items[0] = &one_ctor_fields;
  one_ctor_sort_items[0] = &one_ctor_sorts;
  one_ctor_ref_items[0] = &one_ctor_refs;
  one_sort_name_items[0] = &ctor_name;
  mutual_ctor_name_items[0] = &ctor_names;
  mutual_recog_name_items[0] = &recog_names;
  mutual_field_name_items[0] = &field_names;
  mutual_field_sort_items[0] = &field_sorts;
  mutual_field_ref_items[0] = &field_refs;

  ctor_names.size = recog_names.size = field_names.size = field_sorts.size = 1;
  field_refs.size = 1;
  ctor_names.items = one_ctor_name_items;
  recog_names.items = one_recog_name_items;
  field_names.items = one_ctor_field_items;
  field_sorts.items = one_ctor_sort_items;
  field_refs.items = one_ctor_ref_items;
  one_ctor_fields.size = one_ctor_sorts.size = one_ctor_refs.size = 1;
  one_ctor_fields.items = one_field_name_items;
  one_ctor_sorts.items = one_field_sort_items;
  one_ctor_refs.items = one_field_ref_items;
  field_ref.size = 1; /* single-sort self-reference */

  bool valid = lz3_datatype_fields_valid(&ctor_names, &recog_names,
      &field_names, &field_sorts, &field_refs, 1);
  /*@ assert valid; */
  valid = lz3_datatype_fields_valid(&ctor_names, &recog_names,
      &field_names, &field_sorts, NULL, 0);
  /*@ assert valid; */

  sort_names.size = mutual_ctor_names.size = mutual_recog_names.size = 1;
  mutual_field_names.size = mutual_field_sorts.size = mutual_field_refs.size = 1;
  sort_names.items = one_sort_name_items;
  mutual_ctor_names.items = mutual_ctor_name_items;
  mutual_recog_names.items = mutual_recog_name_items;
  mutual_field_names.items = mutual_field_name_items;
  mutual_field_sorts.items = mutual_field_sort_items;
  mutual_field_refs.items = mutual_field_ref_items;
  valid = lz3_mutual_datatypes_valid(&sort_names, &mutual_ctor_names,
      &mutual_recog_names, &mutual_field_names, &mutual_field_sorts,
      &mutual_field_refs);
  /*@ assert valid; */

  one_ctor_sorts.size = 0; /* inner field-count mismatch */
  valid = lz3_datatype_fields_valid(&ctor_names, &recog_names,
      &field_names, &field_sorts, &field_refs, 1);
  /*@ assert !valid; */
  one_ctor_sorts.size = 1;
  field_ref.size = 2; /* out-of-group recursive reference */
  valid = lz3_mutual_datatypes_valid(&sort_names, &mutual_ctor_names,
      &mutual_recog_names, &mutual_field_names, &mutual_field_sorts,
      &mutual_field_refs);
  /*@ assert !valid; */
  field_ref.size = 1;
  mutual_field_refs.size = 0; /* outer sort-count mismatch */
  valid = lz3_mutual_datatypes_valid(&sort_names, &mutual_ctor_names,
      &mutual_recog_names, &mutual_field_names, &mutual_field_sorts,
      &mutual_field_refs);
  /*@ assert !valid; */
  mutual_field_refs.size = 1;
  ctor_names.size = SIZE_MAX; /* reject before any indexed read */
  valid = lz3_datatype_fields_valid(&ctor_names, &recog_names,
      &field_names, &field_sorts, &field_refs, 1);
  /*@ assert !valid; */
  return 0;
}
