import PlutusCore.Integer
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc
import Tests.Smt.Benchmarks.UPLC.BuiltinsFunctions.Utils

namespace UPLC.CekValue
namespace PLC
  open PlutusCore.Integer
  export PlutusCore.Integer (
    addInteger
    subtractInteger
    multiplyInteger
    divideInteger
    modInteger
    quotientInteger
    remainderInteger
    equalsInteger
    lessThanInteger
    lessThanInteger
    lessThanEqualsInteger
  )
end PLC
open UPLC.Uplc
open CekValue

-- Define addInteger
def addInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Integer (PLC.addInteger x y)))
  | _ => none

-- Define subtractInteger
def subtractInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Integer (PLC.subtractInteger x y)))
  | _ => none

-- Define multiplyInteger
def multiplyInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Integer (PLC.multiplyInteger x y)))
  | _ => none

-- Define divideInteger (truncates towards negative infinity)
def divideInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
       tryCatchSome (PLC.divideInteger x y) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define modInteger (truncates towards negative infinity)
def modInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      tryCatchSome (PLC.modInteger x y) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define quotientInteger (truncates towards zero)
def quotientInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      tryCatchSome (PLC.quotientInteger x y) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define remainderInteger (truncates towards zero)
def remainderInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      tryCatchSome (PLC.remainderInteger x y) (CekValue.VCon ∘ Const.Integer)
  | _ => none


-- Define equalsInteger
def equalsInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Bool (PLC.equalsInteger x y)))
  | _ => none

-- Define lessThanInteger
def lessThanInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanInteger x y)))
  | _ => none

-- Define lessThanEqualsInteger
def lessThanEqualsInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.Integer y)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanEqualsInteger x y)))
  | _ => none

end UPLC.CekValue
