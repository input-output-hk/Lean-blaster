import Lean
import Blaster

namespace Ratio

/-- Arbitrary-precision ratio. NaN models a zero denominator. -/
structure Ratio where
  numerator   : Int
  denominator : Int
  isNaN       : Bool
deriving BEq, Repr

def R_NaN : Ratio := { numerator := 0, denominator := 0, isNaN := true }

/-- Ensure the denominator is positive by pushing the sign onto the numerator. -/
def normalizeRatio (num denum : Int) : Ratio :=
  if denum < 0 then { numerator := -num, denominator := -denum, isNaN := false }
  else { numerator := num, denominator := denum, isNaN := false }

/-- Constructor: NaN when the denominator is zero, otherwise normalized. -/
def ratio (num denum : Int) : Ratio :=
  if denum == 0 then R_NaN else normalizeRatio num denum

/-- Addition of two ratios; NaN propagates. -/
def addRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator + b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

end Ratio
