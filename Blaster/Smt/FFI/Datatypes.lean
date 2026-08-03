import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

/-- Construct a single non-recursive, non-mutual, non-parametric datatype sort.
    Returns the datatype `Z3Sort` and a FLAT `Array FuncDecl` whose layout is,
    per constructor `i` in order: `[ctor_i, recog_i, acc_i0, acc_i1, ...]`. -/
@[extern "lean_z3_mk_datatype"]
opaque Context.mkDatatype : Context → String → Array String → Array String
  → Array (Array String) → Array (Array Z3Sort) → IO (Z3Sort × Array FuncDecl)

/-- Construct a SINGLE, possibly (self-)recursive, non-parametric datatype.
    Like `mkDatatype`, but with an extra per-ctor/per-field `fieldRefs` array: a
    ref of `0` uses the given field sort; `k+1` means the field's sort is the k-th
    datatype in this group (for a single datatype k=0, so a self-reference is `1`).
    When a ref is nonzero the shim substitutes a NULL sort for the corresponding
    `fieldSorts` entry, because Z3 keys "this field is recursive" off a NULL slot in
    its `sorts[]` array (a NON-NULL sort there is used verbatim, which is what caused
    an early sort-mismatch bug). The Lean side may pass any placeholder in that slot;
    it is never read. Same flat `Array FuncDecl` layout as `mkDatatype`:
    `[ctor_i, recog_i, acc_i0, ...]` per ctor `i`. -/
@[extern "lean_z3_mk_datatype_rec"]
opaque Context.mkDatatypeRec : Context → String → Array String → Array String
  → Array (Array String) → Array (Array Z3Sort) → Array (Array UInt32)
  → IO (Z3Sort × Array FuncDecl)

/-- Construct a group of MUTUALLY recursive, non-parametric datatypes via
    `Z3_mk_datatypes`. All arrays are indexed per-sort first: `sortNames[s]`,
    `ctorNames[s]`, `recogNames[s]`, and the per-ctor/per-field `fieldNames[s]`,
    `fieldSorts[s]`, `fieldRefs[s]` (a `fieldRefs` entry `k+1` selects the k-th
    datatype in the group; `0` uses the given sort). Returns one `Z3Sort` per
    datatype and, per datatype, the same flat func_decl layout as `mkDatatype`. -/
@[extern "lean_z3_mk_datatypes"]
opaque Context.mkDatatypes : Context → Array String → Array (Array String) → Array (Array String)
  → Array (Array (Array String)) → Array (Array (Array Z3Sort)) → Array (Array (Array UInt32))
  → IO (Array Z3Sort × Array (Array FuncDecl))

end Blaster.Smt.FFI
