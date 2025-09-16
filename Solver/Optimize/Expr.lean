import Lean

open Lean Meta Declaration

namespace Solver.Optimize

/-- Return `true` if e contains free / bounded variables. -/
def hasVars (e : Expr) : Bool := e.hasFVar || e.hasLooseBVars


/-- Return `true` if `v` occurs at least once in `e`. -/
def fVarInExpr (v : FVarId) (e : Expr) : Bool :=
 if e.hasFVar
 then e.containsFVar v
 else false


/-- If the `e` is a sequence of lambda `fun x₁ => fun x₂ => ... fun xₙ => b`,
    return `b`. Otherwise return `e`.
-/
def getLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getLambdaBody b
 | _ => e

/-- Determine if `e` is a boolean `not` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolNot? (e: Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``not _) n => some n
  | _ => none

/-- Determine if `e` is a boolean `and` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolAnd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a boolean `or` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[inline] def boolOr? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Bool` literal expression b and return `some b`.
    Otherwise `none`
-/
def isBoolValue? (e : Expr) : Option Bool :=
 match e with
 | Expr.const ``true _ => some true
 | Expr.const ``false _ => some false
 | _ => none

/-- Return `true` only when `e` is a `Bool` literal`.
    Otherwise `false`
-/
def isBoolCtor (e : Expr) : Bool :=
 match e with
 | Expr.const ``true _
 | Expr.const ``false _ => true
 | _ => false

/-- Determine if `e` is an boolean `==` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def beq? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) psort) pdecide) e1) e2 =>
      some (psort, pdecide, e1, e2)
  | _ => none


/-- Determine if `e` is an `Eq` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def eq? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) psort) e1) e2 =>
      some (psort, e1, e2)
  | _ => none


/-- Determine if `e` is an `LE.le` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def le? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``LE.le _) psort) pinst) e1) e2 =>
      some (psort, pinst, e1, e2)
  | _ => none

/-- Determine if `e` is an `LT.lt` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def lt? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``LT.lt _) psort) pinst) e1) e2 =>
      some (psort, pinst, e1, e2)
  | _ => none


/-- Determine if `e` is an `Not` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[inline] def propNot? (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) n => some n
  | _ => none


/-- Determine if `e` is an `And` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def propAnd? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is an `Or` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def propOr? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) op1) op2 => some (op1, op2)
  | _ => none


/-- Return `true` if the given expression is of the form `const ``Bool`. -/
def isBoolType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Bool _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Nat`. -/
def isNatType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Nat _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Int`. -/
def isIntType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Int _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``String`. -/
def isStringType (e : Expr) : Bool :=
  match e with
  | Expr.const ``String _ => true
  | _ => false

/-- Determine if `e` is an `autoParam` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def autoParam? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``autoParam _) t) tac => some (t, tac)
  | _ => none

/-- Return `true` only when `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
-/
@[always_inline, inline]
def isNatValue (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.natVal _) => true
  | _ => false

/-- Determine if `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
    and return `some n` as result. Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
@[always_inline, inline]
def isNatValue? (e : Expr) : Option Nat :=
  match e with
  | Expr.lit (Literal.natVal n) => some n
  | _ => none

/-- Determine if `e` is a `String` literal expression `Expr.lit (Literal.strVal s)`
    and return `some s` as result. Otherwise return `none`.
-/
def isStrValue? (e : Expr) : Option String :=
  match e with
  | Expr.lit (Literal.strVal s) => some s
  | _ => none

/-- Determine if `e` is a `UInt32` literal expression `UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some n` only when n < UInt32.size.
    Otherwise return `none`
-/
def isUInt32Value? (e : Expr) : Option Nat :=
  match e with
  | Expr.app (Expr.const ``UInt32.ofBitVec _) fn1 =>
     match fn1 with
     | Expr.app (Expr.app (Expr.const ``BitVec.ofFin _) _) fn2 =>
        match fn2 with
        | Expr.app (Expr.app (Expr.app (Expr.const ``Fin.mk _)
            (Expr.lit (Literal.natVal s))) (Expr.lit (Literal.natVal n))) _ =>
            if s != UInt32.size || Nat.ble UInt32.size n
            then none
            else some n
        | _ => none
     | _ => none
  | _ => none


/-- Determine if `e` is a `Char` literal expression `Char.mk (UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some Char.ofNat n)` only when `Nat.isValidChar n`.
    Otherwise return `none`
-/
def isCharValue? (e : Expr) : Option Char :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Char.mk _) ui) _ =>
      match isUInt32Value? ui with
      | some n => if Nat.isValidChar n then some (Char.ofNat n) else none
      | _ => none
  | _ => none


/-- Return `true` if `e := Nat.add e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.add expression.
-/
def isNatAddExpr (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) _) _ => true
  | _ => false


/-- Return `true` if `e := Nat.sub e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.sub expression.
-/
def isNatSubExpr (e: Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) _) _ => true
  | _ => false


/-- Return `true` if `e := Nat.pow e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.pow expression.
-/
def isNatPowExpr (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.pow _) _) _ => true
  | _ => false

/-- Determine if `e` is a `Nat.mul` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natMul? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a `Nat.add` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natAdd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Nat.sub` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natSub? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Nat.pow` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def natPow? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.pow _) op1) op2 => some (op1, op2)
  | _ => none


/-- Return `some (f, op1, op2)` when `e` is a binary operator. Otherwise `none`. -/
@[inline] def binOp? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app f op1) op2 =>
       if f.isApp then none
       else some (f, op1, op2)
  | _ => none

/-- Determine if `e` is an Int.neg expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[inline] def intNeg? (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Int.neg _) n => some n
  | _ => none

/-- Determine if `e` is a `Int.add` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def intAdd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.add _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a `Int.mul` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def intMul? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.mul _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Int.tdiv` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def intTDiv? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.tdiv _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Decidable.decide` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def decide? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Decidable.decide _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is an `ite` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def ite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``ite _) psort) pcond) pdecide) e1) e2 =>
      some (psort, pcond, pdecide, e1, e2)
  | _ => none


/-- Determine if `e` is an `dite` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[inline] def dite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``dite _) psort) pcond) pdecide) e1) e2 =>
      some (psort, pcond, pdecide, e1, e2)
  | _ => none

/-- Return `true` only when `e := Expr.const ``ite _`
    Otherwise `false`.
-/
def isIteConst (e : Expr) : Bool :=
  match e with
  | Expr.const ``ite _ => true
  | _ => false

/-- Return `true` only when `e := Expr.const ``dite _`
    Otherwise `false`.
-/
def isDiteConst (e : Expr) : Bool :=
  match e with
  | Expr.const ``dite _ => true
  | _ => false

/-- Return `true` only when `e := if c then e1 else e2`.
    Otherwise `false`.
-/
@[inline] def isIte (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``ite _) _) _) _) _) _ => true
  | _ => false

/-- Return `true` only when `e := dite c (h : c => e1) (h : ¬ c => e2)`.
    Otherwise `false`.
-/
@[inline] def isDite (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``dite _) _) _) _) _) _ => true
  | _ => false


/-- Return `true` only when `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
-/
@[always_inline, inline]
def isIntValue (e : Expr) : Bool :=
  match e with
  | Expr.app f a =>
    if isNatValue a then
      match f with
      | Expr.const ``Int.ofNat _
      | Expr.const ``Int.negSucc _ => true
      | _ => false
    else false
  | _ => false

/-- Determine if `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
    Return either `some (Int.ofNat n)` or `some (Int.negSucc n)` as result.
    Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
def isIntValue? (e : Expr) : Option Int :=
  match e with
  | Expr.app f a =>
    match isNatValue? a with
    | some n =>
        match f with
        | Expr.const ``Int.ofNat _ => Int.ofNat n
        | Expr.const ``Int.negSucc _ => Int.negSucc n
        | _ => none
    | none => none
  | _ => none


/-- Given `e` of the form `∀ (a₁ : A₁) ... (aₙ : Aₙ), B[a₁, ..., aₙ]`
    and `p₁ : A₁, ... pₘ : Aₙ`, return `B[p₁, ..., pₘ]`.
-/
partial def betaForAll (e : Expr) (args : Array Expr) : Expr :=
  let rec visit (i : Nat) (e : Expr) : Expr :=
    if h : i < args.size then
       match e with
       | Expr.forallE _ _ b _ => visit (i + 1) (b.instantiate1 args[i])
       | _ => e
    else e
  visit 0 e

/-- Given `e` of the form `λ (a₁ : A₁) ... (aₙ : Aₙ) => B[a₁, ..., aₙ]`
    and `p₁ : A₁, ... pₘ : Aₙ`, return `B[p₁, ..., pₘ]`.
-/
partial def betaLambda (e : Expr) (args : Array Expr) : Expr :=
  let rec visit (i : Nat) (e : Expr) : Expr :=
    if h : i < args.size then
       match e with
       | Expr.lam _ _ b _ => visit (i + 1) (b.instantiate1 args[i])
       | _ => e
    else e
  visit 0 e

/-- Return `true` only when e is a FVar of type `∀ α₀ → ... → αₙ`. -/
def isQuantifiedFun (e : Expr) : MetaM Bool :=
  match e with
  | Expr.fvar v => return (← v.getType).isForall
  | _ => return false

end Solver.Optimize
