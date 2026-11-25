/* Frama-C model of the Lean C API used by the Z3 shims.
 * This file is selected only by verification/run.sh. Production builds use
 * the actual Lean header. Keep signatures aligned with Lean 4.24.0. */
#ifndef BLASTER_FRAMAC_LEAN_H
#define BLASTER_FRAMAC_LEAN_H
#include <stddef.h>
#include <stdint.h>

#define LEAN_EXPORT

/* Semantic model for the APIs exercised by the array collector. This is not
 * Lean's physical object layout; shim code never accesses these fields. */
typedef struct lean_object {
  size_t size;
  struct lean_object **items;
  void *external_data;
  const char *string_data;
} lean_object;
typedef lean_object *lean_obj_arg;
typedef lean_object *b_lean_obj_arg;
typedef lean_object *u_lean_obj_arg;
typedef lean_object *lean_obj_res;
typedef lean_object *b_lean_obj_res;
typedef void (*lean_external_finalize_proc)(void *);
typedef void (*lean_external_foreach_proc)(void *, b_lean_obj_arg);
typedef struct lean_external_class lean_external_class;

lean_external_class *lean_register_external_class(
    lean_external_finalize_proc, lean_external_foreach_proc);
lean_object *lean_alloc_external(lean_external_class *cls, void *data);
/*@ requires \valid_read(o); assigns \result \from o->external_data;
    ensures \result == o->external_data; */
void *lean_get_external_data(lean_object *o);
lean_obj_res lean_box(size_t n);
lean_obj_res lean_box_uint32(uint32_t n);
unsigned lean_unbox_uint32(b_lean_obj_arg o);
void lean_dec(lean_object *o);
const char *lean_string_cstr(b_lean_obj_arg o);
lean_obj_res lean_mk_string(const char *s);
lean_obj_res lean_io_result_mk_ok(lean_obj_arg v);
lean_obj_res lean_io_result_mk_error(lean_obj_arg e);
lean_obj_res lean_mk_io_user_error(lean_obj_arg str);
/*@ requires \valid_read(o); assigns \result \from o->size;
    ensures \result == o->size; */
size_t lean_array_size(b_lean_obj_arg o);
/*@ requires \valid_read(o);
    requires i < o->size;
    requires \valid_read(o->items + (0 .. o->size-1));
    assigns \result \from o->items[i];
    ensures \result == o->items[i]; */
b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i);
lean_obj_res lean_alloc_array(size_t size, size_t capacity);
void lean_array_set_core(u_lean_obj_arg o, size_t i, lean_obj_arg v);
lean_object *lean_array_push(lean_obj_arg a, lean_obj_arg v);
lean_obj_res lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz);
void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v);

#endif
