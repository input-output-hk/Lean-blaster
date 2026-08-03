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

/* mkDatatypeRec :
 *   Context → sortName:String → ctorNames:Array String → recogNames:Array String
 *   → fieldNames:Array (Array String) → fieldSorts:Array (Array Z3Sort)
 *   → fieldRefs:Array (Array UInt32)
 *   → IO (Z3Sort × Array FuncDecl)
 *
 * A SINGLE datatype that MAY be (self-)recursive. `fieldRefs[i][j]` is the
 * sort_ref for field j of ctor i: 0 ⇒ the field's sort is `fieldSorts[i][j]` as
 * given; k+1 ⇒ the field's sort is the k-th datatype defined in THIS group. For a
 * single datatype k is always 0, so a self-reference is ref==1. When ref>0 Z3
 * ignores `sorts[j]`, so we pass a bool-sort placeholder (the Lean side also sends
 * a placeholder in that slot, but building a fresh one here is self-contained).
 *
 * Identical flat FuncDecl layout and refcount discipline to lean_z3_mk_datatype,
 * plus a dec of the fieldRefs OUTER array (its inner arrays/UInt32 elements are
 * borrowed and released transitively). */
LEAN_EXPORT lean_obj_res lean_z3_mk_datatype_rec(b_lean_obj_arg c, b_lean_obj_arg sortName,
    b_lean_obj_arg ctorNames, b_lean_obj_arg recogNames,
    b_lean_obj_arg fieldNames, b_lean_obj_arg fieldSorts, b_lean_obj_arg fieldRefs,
    lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  unsigned nc = (unsigned)lean_array_size(ctorNames);
  Z3_constructor *cons = (Z3_constructor*)malloc(sizeof(Z3_constructor)*(nc?nc:1));
  for (unsigned i=0;i<nc;i++){
    lean_object *fn = lean_array_get_core(fieldNames,i);
    lean_object *fs = lean_array_get_core(fieldSorts,i);
    lean_object *fr = lean_array_get_core(fieldRefs,i);
    unsigned nf = (unsigned)lean_array_size(fn);
    Z3_symbol *fnames=(Z3_symbol*)malloc(sizeof(Z3_symbol)*(nf?nf:1));
    Z3_sort   *fsorts=(Z3_sort*)malloc(sizeof(Z3_sort)*(nf?nf:1));
    unsigned  *refs  =(unsigned*)malloc(sizeof(unsigned)*(nf?nf:1));
    for (unsigned j=0;j<nf;j++){
      fnames[j]=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(fn,j)));
      /* Z3 convention: a field is recursive iff its `sorts[]` entry is NULL, and then
       * `sort_refs[]` holds the 0-based index of the referenced datatype. The Lean
       * side encodes 0 = non-recursive, k+1 = the k-th datatype in the group, so we
       * translate k+1 → (NULL sort, ref=k). */
      unsigned ref_in=(unsigned)lean_unbox_uint32(lean_array_get_core(fr,j));
      if (ref_in==0){ fsorts[j]=(Z3_sort)unbox_owned(lean_array_get_core(fs,j)); refs[j]=0; }
      else          { fsorts[j]=(Z3_sort)0;                                     refs[j]=ref_in-1; }
    }
    Z3_symbol cn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(ctorNames,i)));
    Z3_symbol rn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(recogNames,i)));
    cons[i]=Z3_mk_constructor(ctx, cn, rn, nf, fnames, fsorts, refs);
    free(fnames); free(fsorts); free(refs);
  }
  Z3_symbol sn=Z3_mk_string_symbol(ctx, lean_string_cstr(sortName));
  Z3_sort dt=Z3_mk_datatype(ctx, sn, nc, cons);
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
  lean_dec(c); lean_dec(sortName); lean_dec(ctorNames); lean_dec(recogNames);
  lean_dec(fieldNames); lean_dec(fieldSorts); lean_dec(fieldRefs);
  return z3_io_ok(pair);
}

/* mkDatatypes (MUTUAL) :
 *   Context → sortNames:Array String
 *   → ctorNames :Array (Array String)          (per sort, per ctor)
 *   → recogNames:Array (Array String)
 *   → fieldNames:Array (Array (Array String))  (per sort, per ctor, per field)
 *   → fieldSorts:Array (Array (Array Z3Sort))
 *   → fieldRefs :Array (Array (Array UInt32))
 *   → IO (Array Z3Sort × Array (Array FuncDecl))
 *
 * `fieldRefs[s][i][j]`: 0 ⇒ use `fieldSorts[s][i][j]`; k+1 ⇒ the field's sort is
 * the k-th datatype (0-based) in the group — the mutual/self recursion mechanism.
 * Builds one Z3_constructor_list per sort, calls Z3_mk_datatypes, then queries each
 * constructor (which must stay live until after the query) to recover func_decls.
 * Returns the per-sort datatype sorts and, per sort, the flat func_decl layout
 * `[ctor, recog, acc...]` per ctor.
 *
 * Refcount: dec Context + all seven OUTER arrays once each; every inner array and
 * element (String / Z3Sort / UInt32) is borrowed and released transitively. */
LEAN_EXPORT lean_obj_res lean_z3_mk_datatypes(b_lean_obj_arg c, b_lean_obj_arg sortNames,
    b_lean_obj_arg ctorNames, b_lean_obj_arg recogNames,
    b_lean_obj_arg fieldNames, b_lean_obj_arg fieldSorts, b_lean_obj_arg fieldRefs,
    lean_obj_arg w) {
  (void)w; Z3_context ctx=(Z3_context)ctx_ptr(c);
  unsigned ns = (unsigned)lean_array_size(sortNames);
  Z3_constructor **all_cons = (Z3_constructor**)malloc(sizeof(Z3_constructor*)*(ns?ns:1));
  unsigned *nc_per = (unsigned*)malloc(sizeof(unsigned)*(ns?ns:1));
  Z3_constructor_list *clists = (Z3_constructor_list*)malloc(sizeof(Z3_constructor_list)*(ns?ns:1));
  Z3_symbol *snames = (Z3_symbol*)malloc(sizeof(Z3_symbol)*(ns?ns:1));
  Z3_sort   *osorts = (Z3_sort*)malloc(sizeof(Z3_sort)*(ns?ns:1));
  /* one constructor list per sort */
  for (unsigned s=0;s<ns;s++){
    lean_object *cn_s = lean_array_get_core(ctorNames,s);
    lean_object *rn_s = lean_array_get_core(recogNames,s);
    lean_object *fn_s = lean_array_get_core(fieldNames,s);
    lean_object *fs_s = lean_array_get_core(fieldSorts,s);
    lean_object *fr_s = lean_array_get_core(fieldRefs,s);
    unsigned nc = (unsigned)lean_array_size(cn_s);
    nc_per[s]=nc;
    all_cons[s]=(Z3_constructor*)malloc(sizeof(Z3_constructor)*(nc?nc:1));
    for (unsigned i=0;i<nc;i++){
      lean_object *fn = lean_array_get_core(fn_s,i);
      lean_object *fs = lean_array_get_core(fs_s,i);
      lean_object *fr = lean_array_get_core(fr_s,i);
      unsigned nf=(unsigned)lean_array_size(fn);
      Z3_symbol *fnames=(Z3_symbol*)malloc(sizeof(Z3_symbol)*(nf?nf:1));
      Z3_sort   *fsorts=(Z3_sort*)malloc(sizeof(Z3_sort)*(nf?nf:1));
      unsigned  *refs  =(unsigned*)malloc(sizeof(unsigned)*(nf?nf:1));
      for (unsigned j=0;j<nf;j++){
        fnames[j]=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(fn,j)));
        /* NULL sort ⇒ recursive field; sort_refs holds the 0-based datatype index.
         * Lean encodes 0 = non-recursive, k+1 = k-th datatype ⇒ (NULL, ref=k). */
        unsigned ref_in=(unsigned)lean_unbox_uint32(lean_array_get_core(fr,j));
        if (ref_in==0){ fsorts[j]=(Z3_sort)unbox_owned(lean_array_get_core(fs,j)); refs[j]=0; }
        else          { fsorts[j]=(Z3_sort)0;                                     refs[j]=ref_in-1; }
      }
      Z3_symbol cn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(cn_s,i)));
      Z3_symbol rn=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(rn_s,i)));
      all_cons[s][i]=Z3_mk_constructor(ctx, cn, rn, nf, fnames, fsorts, refs);
      free(fnames); free(fsorts); free(refs);
    }
    snames[s]=Z3_mk_string_symbol(ctx, lean_string_cstr(lean_array_get_core(sortNames,s)));
    clists[s]=Z3_mk_constructor_list(ctx, nc, all_cons[s]);
  }
  Z3_mk_datatypes(ctx, ns, snames, osorts, clists);
  /* recover func_decls + sorts, THEN free constructor containers */
  lean_object *outer    = lean_alloc_array(ns, ns);
  lean_object *sortsArr = lean_alloc_array(ns, ns);
  for (unsigned s=0;s<ns;s++){
    lean_object *fn_s = lean_array_get_core(fieldNames,s);
    unsigned nc = nc_per[s];
    unsigned total=0;
    for (unsigned i=0;i<nc;i++) total += 2 + (unsigned)lean_array_size(lean_array_get_core(fn_s,i));
    lean_object *inner = lean_alloc_array(total, total);
    unsigned k=0;
    for (unsigned i=0;i<nc;i++){
      unsigned nf=(unsigned)lean_array_size(lean_array_get_core(fn_s,i));
      Z3_func_decl cf, rf; Z3_func_decl *accs=(Z3_func_decl*)malloc(sizeof(Z3_func_decl)*(nf?nf:1));
      Z3_query_constructor(ctx, all_cons[s][i], nf, &cf, &rf, accs);
      lean_array_set_core(inner, k++, box_owned(cf));
      lean_array_set_core(inner, k++, box_owned(rf));
      for (unsigned j=0;j<nf;j++) lean_array_set_core(inner, k++, box_owned(accs[j]));
      free(accs);
      Z3_del_constructor(ctx, all_cons[s][i]);
    }
    lean_array_set_core(outer, s, inner);
    lean_array_set_core(sortsArr, s, box_owned(osorts[s]));
    Z3_del_constructor_list(ctx, clists[s]);
    free(all_cons[s]);
  }
  free(all_cons); free(nc_per); free(clists); free(snames); free(osorts);
  lean_object *pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, sortsArr);
  lean_ctor_set(pair, 1, outer);
  lean_dec(c); lean_dec(sortNames); lean_dec(ctorNames); lean_dec(recogNames);
  lean_dec(fieldNames); lean_dec(fieldSorts); lean_dec(fieldRefs);
  return z3_io_ok(pair);
}
