import PlutusCore.Bool
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc

namespace UPLC.CekValue

namespace PLC
  open PlutusCore.Bool
  export PlutusCore.Bool (ifThenElse)
end PLC

open UPLC.Uplc
open CekValue

-- Define ifThenElse
def ifThenElse (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Bool b), caseTrue, caseFalse] =>
        some (PLC.ifThenElse b caseTrue caseFalse)
  | _ => none

end UPLC.CekValue
