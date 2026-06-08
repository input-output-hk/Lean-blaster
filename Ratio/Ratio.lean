import Lean
import Blaster

namespace Ratio

/-- Arbitrary-precision ratio. NaN models a zero denominator. -/
structure Ratio where
  numerator   : Int
  denominator : Int
  isNaN       : Bool
deriving BEq, Repr

-- Constants
def R_ZERO : Ratio := { numerator := 0, denominator := 1, isNaN := false }
def R_ONE  : Ratio := { numerator := 1, denominator := 1, isNaN := false }
def R_HALF : Ratio := { numerator := 1, denominator := 2, isNaN := false }
def R_NaN  : Ratio := { numerator := 0, denominator := 0, isNaN := true }

/-- Absolute value on Int. -/
def absInt (a : Int) : Int := if a < 0 then -a else a

/-- Ensure the denominator is positive by pushing the sign onto the numerator. -/
def normalizeRatio (num denum : Int) : Ratio :=
  if denum < 0 then { numerator := -num, denominator := -denum, isNaN := false }
  else { numerator := num, denominator := denum, isNaN := false }

/-- Build a ratio from a single integer (denominator 1). -/
def fromInteger (a : Int) : Ratio := { numerator := a, denominator := 1, isNaN := false }

/-- Constructor: NaN when the denominator is zero, otherwise normalized. -/
def ratio (num denum : Int) : Ratio :=
  if denum == 0 then R_NaN else normalizeRatio num denum

/-- Ratio (cross-multiplication) equality. False if either operand is NaN. -/
def eqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else a.numerator * b.denominator == b.numerator * a.denominator

/-- Strict less-than. False if either operand is NaN. -/
def ltRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator < b.numerator * a.denominator)

/-- Less-than-or-equal. False if either operand is NaN. -/
def leqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator ≤ b.numerator * a.denominator)

/-- Strict greater-than. False if either operand is NaN. -/
def gtRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator > b.numerator * a.denominator)

/-- Greater-than-or-equal. False if either operand is NaN. -/
def geqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator ≥ b.numerator * a.denominator)

/-- Addition; NaN propagates. -/
def addRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator + b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Subtraction; NaN propagates. -/
def subRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator - b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Multiplication; NaN propagates. -/
def mulRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.numerator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Negation; NaN propagates. -/
def negate (a : Ratio) : Ratio :=
  if a.isNaN then R_NaN
  else { numerator := -a.numerator, denominator := a.denominator, isNaN := false }

/-- A ratio is valid when it is not NaN. -/
def isValidRatio (a : Ratio) : Bool := !a.isNaN

/-- A ratio is valid and normalized when not NaN and the denominator is positive. -/
def isValidAndNormalizedRatio (a : Ratio) : Bool :=
  !a.isNaN && decide (a.denominator > 0)

end Ratio
