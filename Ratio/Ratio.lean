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

/-- Absolute value on ratio; NaN propagates. -/
def absRatio (a : Ratio) : Ratio :=
  if a.isNaN then R_NaN
  else if a.numerator < 0 then { numerator := -a.numerator, denominator := a.denominator, isNaN := false }
  else a

/-- Reciprocal; NaN when the numerator is zero (this also covers a NaN input). -/
def recip (a : Ratio) : Ratio :=
  if a.numerator == 0 then R_NaN
  else normalizeRatio a.denominator a.numerator

/-- Integer division rounding toward zero (Lustre `div` = Euclidean = `Int.ediv`).
    Undefined when `b = 0`. -/
def quotient (a b : Int) : Int :=
  let t_div := Int.ediv (absInt a) b
  if a < 0 then -t_div else t_div

/-- Truncate a ratio toward zero. Undefined when NaN. -/
def truncate (a : Ratio) : Int := quotient a.numerator a.denominator

/-- Ceiling of a ratio (rounds toward +∞). Uses `(num + den - 1) ediv den`. -/
def ceil (a : Ratio) : Int := Int.ediv (a.numerator + a.denominator - 1) a.denominator

/-- Divide an integer by a ratio, rounding toward zero. -/
def truncateRecipRatio (a : Int) (b : Ratio) : Int := quotient (a * b.denominator) b.numerator

/-- Multiply an integer by a ratio; NaN propagates. -/
def integerMulRatio (a : Int) (b : Ratio) : Ratio :=
  if b.isNaN then R_NaN
  else { numerator := b.numerator * a, denominator := b.denominator, isNaN := false }

/-- Multiply a ratio by the reciprocal of an integer; NaN when ratio is NaN or a = 0. -/
def recipMulRatio (a : Int) (b : Ratio) : Ratio :=
  if b.isNaN || a == 0 then R_NaN
  else normalizeRatio b.numerator (b.denominator * a)

/-- Add an integer to a ratio; NaN propagates. -/
def integerAddRatio (a : Int) (b : Ratio) : Ratio :=
  if b.isNaN then R_NaN
  else { numerator := a * b.denominator + b.numerator, denominator := b.denominator, isNaN := false }

/-- Subtract a ratio from an integer; NaN propagates. -/
def integerSubRatio (a : Int) (b : Ratio) : Ratio :=
  if b.isNaN then R_NaN
  else { numerator := a * b.denominator - b.numerator, denominator := b.denominator, isNaN := false }

/-- Integer < ratio. False if the ratio is NaN. -/
def integerLtRatio (a : Int) (b : Ratio) : Bool :=
  if b.isNaN then false else decide (b.denominator * a < b.numerator)

/-- Integer ≤ ratio. False if the ratio is NaN. -/
def integerLeqRatio (a : Int) (b : Ratio) : Bool :=
  if b.isNaN then false else decide (b.denominator * a ≤ b.numerator)

/-- Integer > ratio. False if the ratio is NaN. -/
def integerGtRatio (a : Int) (b : Ratio) : Bool :=
  if b.isNaN then false else decide (b.denominator * a > b.numerator)

/-- Integer ≥ ratio. False if the ratio is NaN. -/
def integerGeqRatio (a : Int) (b : Ratio) : Bool :=
  if b.isNaN then false else decide (b.denominator * a ≥ b.numerator)

/-- Ratio > integer. False if the ratio is NaN. -/
def ratioGtInteger (a : Ratio) (b : Int) : Bool :=
  if a.isNaN then false else decide (a.numerator > a.denominator * b)

/-- Ratio ≥ integer. False if the ratio is NaN. -/
def ratioGeqInteger (a : Ratio) (b : Int) : Bool :=
  if a.isNaN then false else decide (a.numerator ≥ a.denominator * b)

/-- Ratio < integer. False if the ratio is NaN. -/
def ratioLtInteger (a : Ratio) (b : Int) : Bool :=
  if a.isNaN then false else decide (a.numerator < a.denominator * b)

/-- Ratio ≤ integer. False if the ratio is NaN. -/
def ratioLeqInteger (a : Ratio) (b : Int) : Bool :=
  if a.isNaN then false else decide (a.numerator ≤ a.denominator * b)

/-- Minimum of two ratios; NaN if either is NaN. -/
def minRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else if a.numerator * b.denominator < b.numerator * a.denominator then a else b

/-- Maximum of two ratios; NaN if either is NaN. -/
def maxRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else if a.numerator * b.denominator < b.numerator * a.denominator then b else a

end Ratio
