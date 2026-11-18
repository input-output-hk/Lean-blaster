/* Exercise the production assumption collector with modeled Lean arrays and Z3.
 * Z3 checks the forwarded count and order; Lean stubs track owned arguments. */
#include "../../Blaster/Smt/FFI/c/z3_shim_solver.c"

static lean_object solver_obj;
static lean_object assumptions_obj;
static lean_object ast_obj[3];
static lean_object *items[3];
static lean_object error_obj;
static lean_object result_obj;
static char context_handle;
static char solver_handle;
static char ast_handles[3];
static int expected_count;
static int z3_calls;
static int solver_decs;
static int assumption_decs;
static int returned_error;
static uint32_t boxed_value;
static z3_solver_box solver_box;

void *lean_get_external_data(lean_object *o) { return o->external_data; }
size_t lean_array_size(b_lean_obj_arg o) { return o->size; }
b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i) { return o->items[i]; }
void lean_dec(lean_object *o) {
  if (o == &solver_obj) ++solver_decs;
  if (o == &assumptions_obj) ++assumption_decs;
}
lean_obj_res lean_mk_string(const char *s) { return &error_obj; }
lean_obj_res lean_mk_io_user_error(lean_obj_arg s) { return &error_obj; }
lean_obj_res lean_io_result_mk_error(lean_obj_arg e) {
  returned_error = 1;
  return &error_obj;
}
lean_obj_res lean_io_result_mk_ok(lean_obj_arg v) { return v; }
lean_obj_res lean_box_uint32(uint32_t n) { boxed_value = n; return &result_obj; }

Z3_lbool Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                     unsigned n, Z3_ast const as[]) {
  /*@ assert c == (Z3_context)&context_handle; */
  /*@ assert s == (Z3_solver)&solver_handle; */
  /*@ assert n == expected_count; */
  if (n > 0) { /*@ assert as[0] == (Z3_ast)&ast_handles[0]; */ }
  if (n > 1) { /*@ assert as[1] == (Z3_ast)&ast_handles[1]; */ }
  if (n > 2) { /*@ assert as[2] == (Z3_ast)&ast_handles[2]; */ }
  ++z3_calls;
  return Z3_L_TRUE;
}

static void check_case(size_t count) {
  assumptions_obj.size = count;
  expected_count = (int)count;
  z3_calls = solver_decs = assumption_decs = returned_error = 0;
  lean_object *result = lean_z3_solver_check_assuming(
      &solver_obj, &assumptions_obj, NULL);
  /*@ assert solver_decs == 1; */
  /*@ assert assumption_decs == 1; */
  if (returned_error) {
    /*@ assert z3_calls == 0; */
    /*@ assert result == &error_obj; */
  } else {
    /*@ assert z3_calls == 1; */
    /*@ assert boxed_value == 2; */
    /*@ assert result == &result_obj; */
  }
}

int main(void) {
  solver_box.ctx = (Z3_context)&context_handle;
  solver_box.s = (Z3_solver)&solver_handle;
  solver_obj.external_data = &solver_box;
  assumptions_obj.items = items;
  for (int i=0; i<3; ++i) {
    ast_obj[i].external_data = &ast_handles[i];
    items[i] = &ast_obj[i];
  }
  check_case(0);
  check_case(1);
  check_case(3);
  assumptions_obj.size = SIZE_MAX;
  z3_calls = solver_decs = assumption_decs = returned_error = 0;
  lean_object *result = lean_z3_solver_check_assuming(
      &solver_obj, &assumptions_obj, NULL);
  /*@ assert z3_calls == 0; */
  /*@ assert solver_decs == 1; */
  /*@ assert assumption_decs == 1; */
  /*@ assert returned_error == 1; */
  /*@ assert result == &error_obj; */
  return 0;
}
