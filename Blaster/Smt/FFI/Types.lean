namespace Blaster.Smt.FFI

opaque ContextPointed : NonemptyType
def Context : Type := ContextPointed.type
instance : Nonempty Context := ContextPointed.property

opaque SolverPointed : NonemptyType
def Solver : Type := SolverPointed.type
instance : Nonempty Solver := SolverPointed.property

opaque SortPointed : NonemptyType
def «Sort» : Type := SortPointed.type
instance : Nonempty «Sort» := SortPointed.property

opaque AstPointed : NonemptyType
def Ast : Type := AstPointed.type
instance : Nonempty Ast := AstPointed.property

opaque FuncDeclPointed : NonemptyType
def FuncDecl : Type := FuncDeclPointed.type
instance : Nonempty FuncDecl := FuncDeclPointed.property

@[extern "lean_z3_smoke_check_true"] opaque smokeCheckTrue : IO UInt32
@[extern "lean_z3_mk_context"]      opaque mkContext : IO Context
@[extern "lean_z3_ctx_error_code"]  opaque Context.errorCode : Context → IO UInt32
@[extern "lean_z3_ctx_error_msg"]   opaque Context.errorMsg : Context → UInt32 → IO String

end Blaster.Smt.FFI
