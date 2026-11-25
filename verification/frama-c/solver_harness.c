/* The actual solver constructor/finalizer, with controlled Lean/Z3 API stubs.
 * The stubs model reference-count effects, not Z3's solver semantics. */
#include "../../Blaster/Smt/FFI/c/z3_shim_solver.c"

static lean_object context_obj;
static lean_object boxed_obj;
static lean_object error_obj;
static char context_handle;
static char solver_handle;
static char simplifier_handle;
static char class_handle;
static int solver_refs;
static int simplifier_refs;
static int context_decs;
static int returned_error;

/*@ requires min <= max;
    assigns \result \from min, max;
    ensures min <= \result <= max; */
extern int Frama_C_interval(int min, int max);

void *ctx_ptr(lean_object *o) { return &context_handle; }
Z3_solver Z3_mk_solver(Z3_context c) { return (Z3_solver)&solver_handle; }
void Z3_solver_inc_ref(Z3_context c, Z3_solver s) { ++solver_refs; }
void Z3_solver_dec_ref(Z3_context c, Z3_solver s) { --solver_refs; }
Z3_simplifier Z3_mk_simplifier(Z3_context c, Z3_string name) {
  return Frama_C_interval(0, 1) ? (Z3_simplifier)&simplifier_handle : NULL;
}
void Z3_simplifier_inc_ref(Z3_context c, Z3_simplifier s) { ++simplifier_refs; }
void Z3_simplifier_dec_ref(Z3_context c, Z3_simplifier s) { --simplifier_refs; }
Z3_solver Z3_solver_add_simplifier(Z3_context c, Z3_solver s, Z3_simplifier simp) {
  return Frama_C_interval(0, 1) ? (Z3_solver)&solver_handle : NULL;
}
Z3_error_code Z3_get_error_code(Z3_context c) { return Z3_OK; }
Z3_string Z3_get_error_msg(Z3_context c, Z3_error_code e) { return "modeled error"; }

lean_external_class *lean_register_external_class(
    lean_external_finalize_proc finalize, lean_external_foreach_proc foreach) {
  return (lean_external_class *)&class_handle;
}
lean_object *lean_alloc_external(lean_external_class *cls, void *data) {
  boxed_obj.external_data = data;
  return &boxed_obj;
}
void *lean_get_external_data(lean_object *o) { return o->external_data; }
void lean_dec(lean_object *o) { if (o == &context_obj) ++context_decs; }
lean_obj_res lean_mk_string(const char *s) { return &error_obj; }
lean_obj_res lean_mk_io_user_error(lean_obj_arg s) { return &error_obj; }
lean_obj_res lean_io_result_mk_error(lean_obj_arg e) {
  returned_error = 1;
  return &error_obj;
}
lean_obj_res lean_io_result_mk_ok(lean_obj_arg v) { return v; }

int main(void) {
  lean_object *result = lean_z3_mk_solver(&context_obj, NULL);
  /*@ assert simplifier_refs == 0; */
  if (returned_error) {
    /*@ assert solver_refs == 0; */
    /*@ assert context_decs == 1; */
    /*@ assert result == &error_obj; */
  } else {
    /*@ assert solver_refs == 1; */
    /*@ assert context_decs == 0; */
    /*@ assert result == &boxed_obj; */
    solver_finalize(boxed_obj.external_data);
    /*@ assert solver_refs == 0; */
    /*@ assert context_decs == 1; */
  }
  return 0;
}
