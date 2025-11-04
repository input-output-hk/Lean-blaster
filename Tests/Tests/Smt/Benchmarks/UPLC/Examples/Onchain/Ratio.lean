import Tests.Smt.Benchmarks.UPLC.CekMachine

namespace Tests.Uplc.Onchain

open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open UPLC.CekMachine
open UPLC.Uplc

structure Ratio where
  numerator : Integer
  denominator : Integer

instance : Inhabited Ratio where
  default := { numerator := 0, denominator := 0}

def mkRatio (n : Integer) (d : Integer) : Ratio :=
  {numerator := n, denominator := d}

def validRatio (x : Ratio) : Prop := x.denominator > 0

def Ratio.lt (x : Ratio) (y : Ratio) : Bool :=
  x.numerator * y.denominator < y.numerator * x.denominator

def lessThanRatio (x : Ratio) (y : Ratio) : Prop := Ratio.lt x y

def Ratio.le (x : Ratio) (y : Ratio) : Bool :=
  x.numerator * y.denominator ≤ y.numerator * x.denominator

def lessThanEqualsRatio (x : Ratio) (y : Ratio) : Prop := Ratio.le x y

instance : LT Ratio where
  lt := lessThanRatio

instance : LE Ratio where
  le := lessThanEqualsRatio


def truncate (x : Ratio) : Integer := Int.tdiv x.numerator x.denominator

def ceil (x : Ratio) : Integer :=
  let r := truncate x
  if x.denominator * r < x.numerator
  then r + 1 else r

def mulRatio (x : Ratio) (y : Ratio) : Ratio :=
  { numerator := x.numerator * y.numerator, denominator := x.denominator * y.denominator }

def addRatio (x : Ratio) (y : Ratio) : Ratio :=
  { numerator := x.numerator * y.denominator + y.numerator * x.denominator,
    denominator := x.denominator * y.denominator
  }

def subRatio (x : Ratio) (y : Ratio) : Ratio :=
  { numerator := x.numerator * y.denominator - y.numerator * x.denominator,
    denominator := x.denominator * y.denominator
  }

instance : Add Ratio where
  add := addRatio

instance : Sub Ratio where
  sub := subRatio

instance : Mul Ratio where
  mul := mulRatio

def normalizedRatio (n : Integer) (d : Integer) : Ratio :=
  if d < 0
  then { numerator := -n, denominator := -d}
  else { numerator := n, denominator := d}

def recip (x : Ratio) : Ratio :=
  if x.numerator == 0 then panic "recip: zero numerator !!!"
  else normalizedRatio x.denominator x.numerator

def unsafeRecip (x : Ratio) : Ratio :=
  { numerator := x.denominator, denominator := x.numerator }


def zeroRatio : Ratio := { numerator := 0, denominator := 1 }
def oneRatio : Ratio := { numerator := 1, denominator := 1 }
def fromInteger (x : Integer) : Ratio := { numerator := x, denominator := 1 }

def ratioToConstr (x : Ratio) : Term :=
  Term.Constr 0 [ Term.Const (Const.Integer x.numerator),
                  Term.Const (Const.Integer x.denominator) ]

def ratioToData (x : Ratio) : Term :=
  Term.Const $
  Const.Data $
  Data.Constr 0 [ Data.I x.numerator, Data.I x.denominator ]

end Tests.Uplc.Onchain
