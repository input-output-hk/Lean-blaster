import PlutusCore.Data
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc
import Tests.Smt.Benchmarks.UPLC.BuiltinsFunctions.Utils

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.Data
  export PlutusCore.Data (
    -- macro_rules chooseData imported implicitly
    constrData
    mapData
    listData
    iData
    bData
    unConstrData
    unMapData
    unListData
    unIData
    unBData
    equalsData
    mkPairData
    mkNilData
    mkNilPairData
    -- TODO: export serialiseData
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define chooseData
def chooseData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d), constrCase, mapCase, listCase, iCase, bCase] =>
      some (UPLC.chooseData d constrCase mapCase listCase iCase bCase)
  | _ => none

-- Define constrData
def constrData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer i), CekValue.VCon (Const.ConstDataList xs)] =>
      some (CekValue.VCon (Const.Data (PLC.constrData i xs)))
  | _ => none

-- Define mapData
def mapData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      some (CekValue.VCon (Const.Data (PLC.mapData xs)))
  | _ => none

-- Define listData
def listData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstDataList xs)] =>
      some (CekValue.VCon (Const.Data (PLC.listData xs)))
  | _ => none

-- Define iData
def iData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer i)] =>
      some (CekValue.VCon (Const.Data (PLC.iData i)))
  | _ => none

-- Define bData
def bData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString b)] =>
      some (CekValue.VCon (Const.Data (PLC.bData b)))
  | _ => none

-- Define unConstrData
def unConstrData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d)] =>
      tryCatchSome (PLC.unConstrData d)
      (fun (i, xs) =>
        CekValue.VCon $ Const.Pair ((Const.Integer i), Const.ConstDataList xs))
  | _ => none

-- Define unMapData
def unMapData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d)] =>
      tryCatchSome (PLC.unMapData d) (CekValue.VCon ∘ Const.ConstPairDataList)
  | _ => none

-- Define unListData
def unListData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d)] =>
      tryCatchSome (PLC.unListData d) (CekValue.VCon ∘ Const.ConstDataList)
  | _ => none

-- Define unIData
def unIData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d)] =>
      tryCatchSome (PLC.unIData d) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define unBData
def unBData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d)] =>
      tryCatchSome (PLC.unBData d) (CekValue.VCon ∘ Const.ByteString)
  | _ => none


-- Define equalsData
def equalsData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data d1), CekValue.VCon (Const.Data d2)] =>
      CekValue.VCon $ Const.Bool (PLC.equalsData d1 d2)
  | _ => none

-- Define mkPairData
def mkPairData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Data f), CekValue.VCon (Const.Data s)] =>
      CekValue.VCon $ Const.PairData (PLC.mkPairData f s)
  | _ => none

-- Define mkNilData
def mkNilData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon Const.Unit] =>
      CekValue.VCon $ Const.ConstDataList (PLC.mkNilData ())
  | _ => none

-- Define mkNilPairData
def mkNilPairData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon Const.Unit] =>
      CekValue.VCon $ Const.ConstPairDataList (PLC.mkNilPairData ())
  | _ => none



end UPLC.CekValue
