#include "lean_z3.h"
#include <stdlib.h>
extern void *ctx_ptr(lean_object *o);

LEAN_Z3_DECLARE_CLASS(solver)
/* finalizer needs the context; store a {ctx,solver} pair. */
typedef struct { Z3_context ctx; Z3_solver s; } z3_solver_box;
static void solver_finalize(void *p) {
  z3_solver_box *b = (z3_solver_box *)p;
  if (b) { Z3_solver_dec_ref(b->ctx, b->s); free(b); }
}

/* mkSolver : Context → IO Solver */
LEAN_EXPORT lean_obj_res lean_z3_mk_solver(b_lean_obj_arg c, lean_obj_arg w) {
  (void)w;
  Z3_context ctx = (Z3_context)ctx_ptr(c);
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  z3_solver_box *b = (z3_solver_box *)malloc(sizeof(z3_solver_box));
  b->ctx = ctx; b->s = s;
  return z3_io_ok(box_solver(b));
}
