import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_numeral"] opaque Context.mkNumeral   : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_bool"]    opaque Context.mkBool      : Context → Bool → IO Ast
@[extern "lean_z3_mk_string"]  opaque Context.mkStringLit : Context → String → IO Ast

end Blaster.Smt.FFI
