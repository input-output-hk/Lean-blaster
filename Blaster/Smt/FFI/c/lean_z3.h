#ifndef LEAN_Z3_H
#define LEAN_Z3_H
#include <lean/lean.h>
#include <z3.h>

/* Declare a Lean external class + box/unbox for a Z3 handle type.
 * Handles wrapped this way carry a finalizer. AST/sort/funcdecl handles use
 * the no-finalizer variant (see box_owned). */
#define LEAN_Z3_DECLARE_CLASS(name) \
  static lean_external_class *g_##name##_class = NULL; \
  static void name##_finalize(void *p); \
  static void name##_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; } \
  static inline lean_object *box_##name(void *p) { \
    if (!g_##name##_class) g_##name##_class = lean_register_external_class(name##_finalize, name##_foreach); \
    return lean_alloc_external(g_##name##_class, p); \
  } \
  static inline void *unbox_##name(b_lean_obj_arg o) { return lean_get_external_data(o); }

/* No-finalizer external class for context-owned pointers (ast/sort/funcdecl). */
static lean_external_class *g_owned_class = NULL;
static void owned_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static inline lean_object *box_owned(void *p) {
  if (!g_owned_class) g_owned_class = lean_register_external_class(NULL, owned_foreach);
  return lean_alloc_external(g_owned_class, p);
}
static inline void *unbox_owned(b_lean_obj_arg o) { return lean_get_external_data(o); }

static inline lean_obj_res z3_io_ok(lean_object *v) { return lean_io_result_mk_ok(v); }
static inline lean_obj_res z3_io_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

#endif
