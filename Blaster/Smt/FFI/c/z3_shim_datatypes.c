#include "lean_z3.h"
#include <stdlib.h>
extern void *ctx_ptr(lean_object *o);

/* mkDatatype :
 *   Context → sortName:String → ctorNames:Array String → recogNames:Array String
 *   → fieldNames:Array (Array String) → fieldSorts:Array (Array Z3Sort)
 *   → IO (Z3Sort × Array FuncDecl)
 *
 * MVP: single, non-recursive, non-mutual, non-parametric datatype. Field sorts
 * are already-built Z3 sorts (no self-references; the Lean side rejects those).
 *
 * FuncDecl array layout, per ctor i in order: [ctor_i, recog_i, acc_i0, acc_i1, ...].
 * The Lean side walks this flat layout to register each func_decl by SMT name.
 *
 * Refcount rule: every OBJECT arg is passed OWNED — dec Context, each of the two
 * outer String arrays, and each of the two OUTER nested arrays once. Elements read
 * via lean_array_get_core (including the inner arrays and their String/Z3Sort
 * elements) are BORROWED; deccing the OUTER array recursively releases them, so we
 * never dec inner arrays or elements individually. box_owned wraps context-owned
 * handles (Z3_sort/Z3_func_decl) with a no-op finalizer. */
LEAN_EXPORT lean_obj_res lean_z3_mk_datatype(b_lean_obj_arg c, b_lean_obj_arg sortName,
    b_lean_obj_arg ctorNames, b_lean_obj_arg recogNames,
    b_lean_obj_arg fieldNames, b_lean_obj_arg fieldSorts, lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  unsigned nc = (unsigned)lean_array_size(ctorNames);
  Z3_constructor *cons = (Z3_constructor*)malloc(sizeof(Z3_constructor)*(nc?nc:1));
  for (unsigned i=0;i<nc;i++){
    lean_object *fn = lean_array_get_core(fieldNames,i);
    lean_object *fs = lean_array_get_core(fieldSorts,i);
    unsigned nf = (unsigned)lean_array_size(fn);
    Z3_symbol *fnames=(Z3_symbol*)malloc(sizeof(Z3_symbol)*(nf?nf:1));
    Z3_sort   *fsorts=(Z3_sort*)malloc(sizeof(Z3_sort)*(nf?nf:1));
    unsigned  *refs  =(unsigned*)malloc(sizeof(unsigned)*(nf?nf:1));
    for (unsigned j=0;j<nf;j++){
      fnames[j]=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(fn,j)));
      fsorts[j]=(Z3_sort)unbox_owned(lean_array_get_core(fs,j));
      refs[j]=0; /* non-recursive: the field sort is fsorts[j] as given */
    }
    Z3_symbol cn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(ctorNames,i)));
    Z3_symbol rn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(recogNames,i)));
    cons[i]=Z3_mk_constructor(ctx, cn, rn, nf, fnames, fsorts, refs);
    free(fnames); free(fsorts); free(refs);
  }
  Z3_symbol sn=Z3_mk_string_symbol(ctx, lean_string_cstr(sortName));
  Z3_sort dt=Z3_mk_datatype(ctx, sn, nc, cons);
  /* count total decls and flatten: per ctor, 2 (ctor+recog) + nfields accessors */
  unsigned total=0;
  for (unsigned i=0;i<nc;i++) total += 2 + (unsigned)lean_array_size(lean_array_get_core(fieldNames,i));
  lean_object *arr = lean_alloc_array(total, total);
  unsigned k=0;
  for (unsigned i=0;i<nc;i++){
    unsigned nf=(unsigned)lean_array_size(lean_array_get_core(fieldNames,i));
    Z3_func_decl cf, rf; Z3_func_decl *accs=(Z3_func_decl*)malloc(sizeof(Z3_func_decl)*(nf?nf:1));
    Z3_query_constructor(ctx, cons[i], nf, &cf, &rf, accs);
    lean_array_set_core(arr, k++, box_owned(cf));
    lean_array_set_core(arr, k++, box_owned(rf));
    for (unsigned j=0;j<nf;j++) lean_array_set_core(arr, k++, box_owned(accs[j]));
    free(accs);
    Z3_del_constructor(ctx, cons[i]);
  }
  free(cons);
  lean_object *pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, box_owned(dt));
  lean_ctor_set(pair, 1, arr);
  /* refcount: release all owned object args */
  lean_dec(c); lean_dec(sortName); lean_dec(ctorNames); lean_dec(recogNames);
  lean_dec(fieldNames); lean_dec(fieldSorts);
  return z3_io_ok(pair);
}
