import PlutusCore.Unit
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.Unit
  export PlutusCore.Unit (
    chooseUnit
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define chooseUnit
def chooseUnit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon Const.Unit, v] => some (PLC.chooseUnit () v)
  | _ => none


end UPLC.CekValue
