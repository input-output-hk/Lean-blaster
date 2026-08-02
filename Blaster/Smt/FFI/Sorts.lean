import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_bool_sort"]     opaque Context.mkBoolSort   : Context → IO Z3Sort
@[extern "lean_z3_mk_int_sort"]      opaque Context.mkIntSort    : Context → IO Z3Sort
@[extern "lean_z3_mk_string_sort"]   opaque Context.mkStringSort : Context → IO Z3Sort
@[extern "lean_z3_mk_array_sort"]    opaque Context.mkArraySort  : Context → Z3Sort → Z3Sort → IO Z3Sort
@[extern "lean_z3_mk_uninterp_sort"] opaque Context.mkUninterpSort : Context → String → IO Z3Sort

end Blaster.Smt.FFI
