import PlutusCore.List
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc
import Tests.Smt.Benchmarks.UPLC.BuiltinsFunctions.Utils

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.List
  export PlutusCore.List (
    -- macro_rules chooseList imported implicitly
    mkCons
    headList
    tailList
    nullList
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define chooseList
def chooseList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList l), nullCase, listCase]
  | [CekValue.VCon (Const.ConstDataList l), nullCase, listCase]
  | [CekValue.VCon (Const.ConstPairDataList l), nullCase, listCase] =>
    -- TODO: Need to check how we can enforce that nullCase and
    -- listCase are of the same type
      some (UPLC.chooseList l nullCase listCase)
  | _ => none

-- Define mkCons
def mkCons (Vs : List CekValue) : Option CekValue :=
  -- TODO: Need to check how we can enforce that x and xs are of the same type.
  -- With this current version we can built heterogeneous list,
  -- which does not correspond to what the specification says.
  match Vs with
  | [CekValue.VCon x, CekValue.VCon (Const.ConstList xs)] =>
      some (CekValue.VCon (Const.ConstList (PLC.mkCons x xs)))

  | [CekValue.VCon (Const.Data x), CekValue.VCon (Const.ConstDataList xs)] =>
      -- case for ConstDataList
      some (CekValue.VCon (Const.ConstDataList (PLC.mkCons x xs)))

  | [CekValue.VCon (Const.PairData p), CekValue.VCon (Const.ConstPairDataList xs)] =>
      -- case for ConsPairDataList
      some (CekValue.VCon (Const.ConstPairDataList (PLC.mkCons p xs)))
  | _ => none

-- Define headList
def headList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)] =>
      tryCatchSome (PLC.headList xs) (CekValue.VCon)

  | [CekValue.VCon (Const.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.headList xs) (CekValue.VCon ∘ Const.Data)

  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.headList xs) (CekValue.VCon ∘ Const.PairData)

  | _ => none

-- Define tailList
def tailList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)] =>
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstList)

  | [CekValue.VCon (Const.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstDataList)

  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstPairDataList)
  | _ => none

-- Define nullList
def nullList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)]
  | [CekValue.VCon (Const.ConstDataList xs)]
  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      some (CekValue.VCon (Const.Bool (PLC.nullList xs)))
  | _ => none

end UPLC.CekValue
