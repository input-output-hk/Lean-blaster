#include <z3.h>
#include <stdio.h>

/* Exercise the same native solver and recfun-finder setup used by Blaster. */
int main(void) {
  Z3_global_param_set("auto_config", "false");
  Z3_global_param_set("smt.mbqi", "true");
  Z3_global_param_set("smt.macro_finder", "true");
  Z3_global_param_set("smt.pull_nested_quantifiers", "true");
  Z3_global_param_set("smt.case_split_relevant_first", "true");
  Z3_global_param_set("smt.qi.persist_instances", "true");
  Z3_global_param_set("smt.arith.nl.grobner_expand_terms", "false");
  Z3_global_param_set("smt.arith.nl.reduce_pseudo_linear", "false");
  Z3_global_param_set("smt.arith.nl.grobner_exp_delay", "false");

  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_solver base = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, base);
  Z3_simplifier simp = Z3_mk_simplifier(ctx, "recfun-finder");
  if (!simp) return 2;
  Z3_simplifier_inc_ref(ctx, simp);
  Z3_solver solver = Z3_solver_add_simplifier(ctx, base, simp);
  if (!solver) return 3;
  Z3_solver_inc_ref(ctx, solver);
  Z3_simplifier_dec_ref(ctx, simp);
  Z3_solver_dec_ref(ctx, base);

  Z3_sort ints = Z3_mk_int_sort(ctx);
  Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), ints);
  Z3_ast one = Z3_mk_numeral(ctx, "1", ints);
  Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, one));
  Z3_lbool result = Z3_solver_check(ctx, solver);
  fprintf(stderr, "native Z3 check result: %d\n", (int)result);
  Z3_solver_dec_ref(ctx, solver);
  Z3_del_context(ctx);
  return result == Z3_L_TRUE ? 0 : 4;
}
