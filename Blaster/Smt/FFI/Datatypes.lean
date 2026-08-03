import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

/-- Construct a single non-recursive, non-mutual, non-parametric datatype sort.
    Returns the datatype `Z3Sort` and a FLAT `Array FuncDecl` whose layout is,
    per constructor `i` in order: `[ctor_i, recog_i, acc_i0, acc_i1, ...]`. -/
@[extern "lean_z3_mk_datatype"]
opaque Context.mkDatatype : Context → String → Array String → Array String
  → Array (Array String) → Array (Array Z3Sort) → IO (Z3Sort × Array FuncDecl)

end Blaster.Smt.FFI
