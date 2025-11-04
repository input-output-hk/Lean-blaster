import PlutusCore.Pair
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.Pair
  export PlutusCore.Pair (
    fstPair
    sndPair
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define fstPair
def fstPair (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Pair p)] =>
       some (CekValue.VCon (PLC.fstPair p))
  | [CekValue.VCon (Const.PairData p)] =>
       -- case for PairData
       some (CekValue.VCon (Const.Data (PLC.fstPair p)))
  | _ => none

-- Define sndPair
def sndPair (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Pair p)] =>
       some (CekValue.VCon (PLC.sndPair p))
  | [CekValue.VCon (Const.PairData p)] =>
       -- case for PairData
       some (CekValue.VCon (Const.Data (PLC.sndPair p)))
  | _ => none

end UPLC.CekValue
