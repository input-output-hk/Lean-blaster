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

/-- Create a Z3 type variable from a name (e.g. `@α`), for a polymorphic datatype's params. -/
@[extern "lean_z3_mk_type_var"]
opaque Context.mkTypeVar : Context → String → IO Z3Sort

/-- Declare a PARAMETRIC datatype via `Z3_mk_polymorphic_datatype`. `typevars` are the
    type-variable params. Field arrays mirror `mkDatatypeRec`: a `fieldRefs` entry `0`
    uses `fieldSorts[i][j]` (a type-var for a `@α` field, or a real sort); `1` marks a
    self-recursive field ⇒ the shim substitutes a NULL sort with `sort_ref 0` (the field's
    slot in `fieldSorts` is then a never-read placeholder). Returns ONLY the polymorphic
    sort; the instantiated func_decls are recovered per-instantiation via the `dt*` calls. -/
@[extern "lean_z3_mk_poly_datatype"]
opaque Context.mkPolyDatatype : Context → String → Array Z3Sort → Array String → Array String
  → Array (Array String) → Array (Array Z3Sort) → Array (Array UInt32) → IO Z3Sort

/-- Instantiate a previously-declared datatype `name` at concrete `params`
    (e.g. `@List` at `[Int]` ⇒ `(@List Int)`) via `Z3_mk_datatype_sort`. -/
@[extern "lean_z3_mk_datatype_sort"]
opaque Context.mkDatatypeSort : Context → String → Array Z3Sort → IO Z3Sort

/-- Number of constructors of an (instantiated) datatype sort. -/
@[extern "lean_z3_dt_num_ctors"]
opaque Context.dtNumCtors : Context → Z3Sort → IO UInt32

/-- The `i`-th constructor func_decl of an instantiated datatype sort (monomorphized). -/
@[extern "lean_z3_dt_constructor"]
opaque Context.dtConstructor : Context → Z3Sort → UInt32 → IO FuncDecl

/-- The `i`-th recognizer (`is-<ctor>`) func_decl of an instantiated datatype sort. -/
@[extern "lean_z3_dt_recognizer"]
opaque Context.dtRecognizer : Context → Z3Sort → UInt32 → IO FuncDecl

/-- The `j`-th accessor of the `i`-th ctor of an instantiated datatype sort (monomorphized). -/
@[extern "lean_z3_dt_accessor"]
opaque Context.dtAccessor : Context → Z3Sort → UInt32 → UInt32 → IO FuncDecl

/-- The sort of a term (`Z3_get_sort`) — used to resolve accessor/recognizer arg sorts. -/
@[extern "lean_z3_ast_sort"]
opaque Context.astSort : Context → Ast → IO Z3Sort

end Blaster.Smt.FFI
