/* Exercise the actual collector body with four concrete Lean array sizes.
 * The model header supplies API contracts, not a replacement shim body. */
#include "../../Blaster/Smt/FFI/c/z3_shim_terms.c"

static lean_object first = {0, NULL, &first, NULL};
static lean_object second = {0, NULL, &second, NULL};
static lean_object third = {0, NULL, &third, NULL};
static lean_object *elements[3] = {&first, &second, &third};
static lean_object input = {0, elements, NULL, NULL};

static void check_empty(void) {
  input.size = 0;
  size_t n = 99;
  Z3_ast *result = lz3_collect(&input, &n);
  /*@ assert n == 0; */
  if (result) free(result);
}

static void check_single(void) {
  input.size = 1;
  size_t n = 99;
  Z3_ast *result = lz3_collect(&input, &n);
  /*@ assert n == 1; */
  if (result) {
    /*@ assert \valid(result); */
    /*@ assert result[0] == (Z3_ast)first.external_data; */
    free(result);
  }
}

static void check_pair(void) {
  input.size = 2;
  size_t n = 99;
  Z3_ast *result = lz3_collect(&input, &n);
  /*@ assert n == 2; */
  if (result) {
    /*@ assert \valid(result + (0 .. 1)); */
    /*@ assert result[0] == (Z3_ast)first.external_data; */
    /*@ assert result[1] == (Z3_ast)second.external_data; */
    /*@ assert result[0] != result[1]; */
    free(result);
  }
}

static void check_triple(void) {
  input.size = 3;
  size_t n = 99;
  Z3_ast *result = lz3_collect(&input, &n);
  /*@ assert n == 3; */
  if (result) {
    /*@ assert \valid(result + (0 .. 2)); */
    /*@ assert result[0] == (Z3_ast)first.external_data; */
    /*@ assert result[1] == (Z3_ast)second.external_data; */
    /*@ assert result[2] == (Z3_ast)third.external_data; */
    free(result);
  }
}

int main(void) {
  check_empty();
  check_single();
  check_pair();
  check_triple();
  return 0;
}
