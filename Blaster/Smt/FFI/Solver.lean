import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_solver"] opaque Context.mkSolver : Context → IO Solver

@[extern "lean_z3_solver_assert"]   opaque Solver.assert  : Solver → Ast → IO Unit
@[extern "lean_z3_solver_check"]    opaque Solver.check   : Solver → IO UInt32
@[extern "lean_z3_solver_eval_str"] opaque Solver.evalStr : Solver → Ast → IO String
@[extern "lean_z3_solver_check_assuming"] opaque Solver.checkAssuming : Solver → Array Ast → IO UInt32

end Blaster.Smt.FFI
