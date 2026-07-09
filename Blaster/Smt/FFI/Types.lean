namespace Blaster.Smt.FFI

opaque ContextPointed : NonemptyType
def Context : Type := ContextPointed.type
instance : Nonempty Context := ContextPointed.property

opaque SolverPointed : NonemptyType
def Solver : Type := SolverPointed.type
instance : Nonempty Solver := SolverPointed.property

@[extern "lean_z3_smoke_check_true"] opaque smokeCheckTrue : IO UInt32
@[extern "lean_z3_mk_context"]      opaque mkContext : IO Context
@[extern "lean_z3_ctx_error_code"]  opaque Context.errorCode : Context → IO UInt32
@[extern "lean_z3_ctx_error_msg"]   opaque Context.errorMsg : Context → UInt32 → IO String

end Blaster.Smt.FFI
