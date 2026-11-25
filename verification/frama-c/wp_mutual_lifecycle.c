/* WP event model for the production mutual-constructor cleanup. Every Z3
 * destructor call increments a ghost-style audit counter. The model deliberately
 * does not claim to prove Z3's internal memory management or C free. */
#include <z3.h>
#include <limits.h>
#include <stdlib.h>

unsigned long long z3_wp_ctor_deletes;
unsigned long long z3_wp_list_deletes;
unsigned long long z3_wp_expected_deletes;

/*@ requires z3_wp_ctor_deletes < ULLONG_MAX;
    assigns z3_wp_ctor_deletes;
    ensures z3_wp_ctor_deletes == \old(z3_wp_ctor_deletes) + 1;
*/
void Z3_del_constructor(Z3_context c, Z3_constructor con) {
  (void)c; (void)con;
  ++z3_wp_ctor_deletes;
}
/*@ requires z3_wp_list_deletes < ULLONG_MAX;
    assigns z3_wp_list_deletes;
    ensures z3_wp_list_deletes == \old(z3_wp_list_deletes) + 1;
*/
void Z3_del_constructor_list(Z3_context c, Z3_constructor_list list) {
  (void)c; (void)list;
  ++z3_wp_list_deletes;
}

/*@ assigns \nothing; */
void lz3_wp_free(void *p) { (void)p; }
#define free lz3_wp_free
#define LZ3_WP_DELETE_COUNTS
#include "../../Blaster/Smt/FFI/c/z3_shim_datatypes.c"
#undef free
