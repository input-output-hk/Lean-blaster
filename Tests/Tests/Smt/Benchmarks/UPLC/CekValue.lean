import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.Uplc

namespace UPLC.CekValue
open UPLC.Uplc
open UPLC.Builtins

mutual
  inductive CekValue
  | VCon     : Const → CekValue
  | VDelay   : Term → Environment → CekValue
  | VLam     : String → Term → Environment → CekValue
  | VConstr  : Nat → List CekValue  → CekValue
  | VBuiltin : UPLC.Uplc.BuiltinFun → List CekValue → UPLC.Builtins.ExpectedBuiltinArgs → CekValue
  deriving Repr

  inductive Environment
  | NonEmptyEvironment : Environment → String → CekValue → Environment
  | EmptyEnvironment : Environment
  deriving Repr

end

end UPLC.CekValue
