import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_numeral"] opaque Context.mkNumeral   : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_bool"]    opaque Context.mkBool      : Context → Bool → IO Ast
@[extern "lean_z3_mk_string"] private opaque Context.mkEscapedStringLit : Context → String → IO Ast
@[extern "lean_z3_mk_u32_string"] private opaque Context.mkU32StringLit : Context → Array UInt32 → IO Ast

/-- Create a Z3 string from actual Lean Unicode scalar values. -/
def Context.mkStringLit (ctx : Context) (s : String) : IO Ast :=
  ctx.mkU32StringLit (s.toList.toArray.map (UInt32.ofNat ∘ Char.toNat))

/-- Create a string from SMT-LIB escaped contents emitted by `strLitSmt`. -/
def Context.mkSmtStringLit (ctx : Context) (s : String) : IO Ast :=
  ctx.mkEscapedStringLit s

@[extern "lean_z3_mk_const"]     opaque Context.mkConst    : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_func_decl"] opaque Context.mkFuncDecl : Context → String → Array Z3Sort → Z3Sort → IO FuncDecl
@[extern "lean_z3_mk_app"]       opaque Context.mkApp      : Context → FuncDecl → Array Ast → IO Ast

/-- Structured model inspection. The AST remains owned by its context. -/
@[extern "lean_z3_ast_to_string"] opaque Context.astToString : Context → Ast → IO String
@[extern "lean_z3_ast_is_string"] opaque Context.astIsString : Context → Ast → IO Bool
@[extern "lean_z3_ast_get_string_codepoints"] opaque Context.astGetStringCodepoints : Context → Ast → IO (Array UInt32)
@[extern "lean_z3_ast_is_numeral"] opaque Context.astIsNumeral : Context → Ast → IO Bool
@[extern "lean_z3_ast_get_numeral"] opaque Context.astGetNumeral : Context → Ast → IO String
@[extern "lean_z3_ast_is_app"] opaque Context.astIsApp : Context → Ast → IO Bool
@[extern "lean_z3_ast_get_decl_name"] opaque Context.astGetDeclName : Context → Ast → IO String
@[extern "lean_z3_ast_get_args"] opaque Context.astGetArgs : Context → Ast → IO (Array Ast)

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
@[extern "lean_z3_mk_seq_replace_all"] opaque Context.mkStrReplaceAll : Context → Ast → Ast → Ast → IO Ast
@[extern "lean_z3_mk_int_abs"]    opaque Context.mkIntAbs    : Context → Ast → IO Ast

/- Native BitVec operations. -/
@[extern "lean_z3_mk_bvadd"]  opaque Context.mkBvAdd  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsub"]  opaque Context.mkBvSub  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvmul"]  opaque Context.mkBvMul  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvudiv"] opaque Context.mkBvUDiv : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsdiv"] opaque Context.mkBvSDiv : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvurem"] opaque Context.mkBvURem : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsrem"] opaque Context.mkBvSRem : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsmod"] opaque Context.mkBvSMod : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvshl"]  opaque Context.mkBvShl  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvlshr"] opaque Context.mkBvLShr : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvashr"] opaque Context.mkBvAShr : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvor"]   opaque Context.mkBvOr   : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvand"]  opaque Context.mkBvAnd  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvnand"] opaque Context.mkBvNand : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvnor"]  opaque Context.mkBvNor  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvxnor"] opaque Context.mkBvXnor : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_concat"] opaque Context.mkBvConcat : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvule"]  opaque Context.mkBvULe  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvult"]  opaque Context.mkBvULt  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvuge"]  opaque Context.mkBvUGe  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvugt"]  opaque Context.mkBvUGt  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsle"]  opaque Context.mkBvSLe  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvslt"]  opaque Context.mkBvSLt  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsge"]  opaque Context.mkBvSGe  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvsgt"]  opaque Context.mkBvSGt  : Context → Ast → Ast → IO Ast
@[extern "lean_z3_mk_bvneg"]  opaque Context.mkBvNeg  : Context → Ast → IO Ast
@[extern "lean_z3_mk_bvnot"]  opaque Context.mkBvNot  : Context → Ast → IO Ast

/- Task 10: quantifier + lambda constructors (fresh-const binders). -/
@[extern "lean_z3_mk_fresh_const"]  opaque Context.mkFreshConst  : Context → String → Z3Sort → IO Ast
@[extern "lean_z3_mk_quant_const"]  opaque Context.mkQuantConst  : Context → Bool → UInt32 → String → Array Ast → Array Ast → Ast → IO Ast
@[extern "lean_z3_mk_lambda_const"] opaque Context.mkLambdaConst : Context → Array Ast → Ast → IO Ast

/- Task 13: recursive define-fun (define-fun-rec / define-funs-rec). -/
@[extern "lean_z3_mk_rec_func_decl"] opaque Context.mkRecFuncDecl : Context → String → Array Z3Sort → Z3Sort → IO FuncDecl
@[extern "lean_z3_add_rec_def"]      opaque Context.addRecDef     : Context → FuncDecl → Array Ast → Ast → IO Unit

end Blaster.Smt.FFI
