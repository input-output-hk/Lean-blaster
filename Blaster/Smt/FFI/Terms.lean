import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_numeral"] opaque Context.mkNumeral   : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_bool"]    opaque Context.mkBool      : Context → Bool → IO Ast
@[extern "lean_z3_mk_string"]  opaque Context.mkStringLit : Context → String → IO Ast

@[extern "lean_z3_mk_const"]     opaque Context.mkConst    : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_func_decl"] opaque Context.mkFuncDecl : Context → String → Array Z3Sort → Z3Sort → IO FuncDecl
@[extern "lean_z3_mk_app"]       opaque Context.mkApp      : Context → FuncDecl → Array Ast → IO Ast

end Blaster.Smt.FFI
