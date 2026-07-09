import Blaster.Smt.FFI.Types
namespace Blaster.Smt.FFI

@[extern "lean_z3_mk_solver"] opaque Context.mkSolver : Context → IO Solver

end Blaster.Smt.FFI
