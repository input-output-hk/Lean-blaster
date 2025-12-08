import Lean

open Lean Meta

namespace Blaster.Optimize

structure MatcherRecInfo where
  /-- MatcherInfo for match -/
  mInfo : MatcherInfo
  /-- Flag set to true only when match is a casesOn --/
  isCasesOn : Bool

instance : Repr MatcherInfo where
  reprPrec _ _ := "<MatcherInfo>"

instance : Repr MatcherRecInfo where
  reprPrec _ _ := "<MatcherRecInfo>"

structure MatchInfo where
  /-- Name of match -/
  name : Name
  /-- Name expression of match -/
  nameExpr : Expr
  /-- match generic optimized instance (see InitOptimizeMatchInfo case) -/
  instApp : Expr
  /-- MatcherInfo for match -/
  recInfo : MatcherRecInfo
deriving Repr

@[always_inline, inline]
def MatchInfo.numParams (minfo : MatchInfo) : Nat :=
  minfo.recInfo.mInfo.numParams

@[always_inline, inline]
def MatchInfo.numAlts (minfo : MatchInfo) : Nat :=
  minfo.recInfo.mInfo.altNumParams.size

@[always_inline, inline]
def MatchInfo.numDiscrs (minfo : MatchInfo) : Nat :=
  minfo.recInfo.mInfo.numDiscrs

@[always_inline, inline]
def MatchInfo.arity (minfo : MatchInfo) : Nat :=
  minfo.numParams + 1 + minfo.numDiscrs + minfo.numAlts

@[always_inline, inline]
def MatchInfo.getFirstDiscrPos (info : MatchInfo) : Nat :=
  info.numParams + 1

@[always_inline, inline]
def MatchInfo.getDiscrRange (info : MatchInfo) : Std.Range :=
  [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs]

@[always_inline, inline]
def MatchInfo.getFirstAltPos (info : MatchInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs

@[always_inline, inline]
def MatchInfo.isCasesOn (info : MatchInfo) : Bool :=
  info.recInfo.isCasesOn

end Blaster.Optimize
