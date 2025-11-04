import PlutusCore.Trace
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.Trace
  export PlutusCore.Trace (
    trace
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define trace
def trace (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.String s), v] => some (PLC.trace s v)
  | _ => none

end UPLC.CekValue
