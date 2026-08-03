import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_numeral"] opaque Context.mkNumeral   : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_bool"]    opaque Context.mkBool      : Context → Bool → IO Ast
@[extern "lean_z3_mk_string"]  opaque Context.mkStringLit : Context → String → IO Ast

@[extern "lean_z3_mk_const"]     opaque Context.mkConst    : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_func_decl"] opaque Context.mkFuncDecl : Context → String → Array Z3Sort → Z3Sort → IO FuncDecl
@[extern "lean_z3_mk_app"]       opaque Context.mkApp      : Context → FuncDecl → Array Ast → IO Ast

/- Task 7: built-in operator constructors. -/
@[extern "lean_z3_mk_and"]        opaque Context.mkAnd       : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_or"]         opaque Context.mkOr        : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_add"]        opaque Context.mkAdd       : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_mul"]        opaque Context.mkMul       : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_sub"]        opaque Context.mkSub       : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_distinct"]   opaque Context.mkDistinct  : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_seq_concat"] opaque Context.mkStrConcat : Context → Array Ast → IO Ast
@[extern "lean_z3_mk_eq"]         opaque Context.mkEq        : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_implies"]    opaque Context.mkImplies   : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_lt"]         opaque Context.mkLt        : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_le"]         opaque Context.mkLe        : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_gt"]         opaque Context.mkGt        : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_ge"]         opaque Context.mkGe        : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_idiv"]       opaque Context.mkIDiv      : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_mod"]        opaque Context.mkMod       : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_power"]      opaque Context.mkPower     : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_select"]     opaque Context.mkSelect    : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_str_lt"]     opaque Context.mkStrLt     : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_str_le"]     opaque Context.mkStrLe     : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_not"]        opaque Context.mkNot       : Context → Ast → IO Ast
@[extern "lean_z3_mk_real2int"]   opaque Context.mkToInt     : Context → Ast → IO Ast
@[extern "lean_z3_mk_seq_length"] opaque Context.mkStrLen    : Context → Ast → IO Ast
@[extern "lean_z3_mk_neg"]        opaque Context.mkNeg       : Context → Ast → IO Ast
@[extern "lean_z3_mk_ite"]        opaque Context.mkIte       : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_store"]      opaque Context.mkStore     : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_seq_replace"] opaque Context.mkStrReplace : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_int_abs"]    opaque Context.mkIntAbs    : Context → Ast → IO Ast

end Blaster.Smt.FFI
