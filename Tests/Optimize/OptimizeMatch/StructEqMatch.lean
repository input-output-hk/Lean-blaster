import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.StructEqMatch

/-! ## Test objectives to validate structural equivalence on match expressions -/

/-! Test cases to validate when structural equivalence must be applied. -/

def discrAbstract (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [], _ => false
  | _, _ => true

def discrAbstractInt (x : List α) (y : Option α) : Int :=
  match x, y with
  | [], none => 1
  | _, none => 0
  | [], _ => 0
  | _, _ => 1

 -- ∀ (α : Type) (x : List α) (y : Option α), discrAbstract x y → discrAbstractInt x y = 1 ===> True
 -- Test case to ensure that structural equivalence on match expression
 -- can be performed across instances, e.g. using the same match function
 -- with different instantiations.
 -- NOTE: Test case reduce to True due to match over fun propagation rule
#testOptimize ["MatchStructEq_1"]
  ∀ (α : Type) (x : List α) (y : Option α), discrAbstract x y → discrAbstractInt x y = 1 ===> True

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | yellow : Color → Color
  | black : Color
  | green : Color → Color
  | white : Color

-- ∀ (x : List Color) (y : Option Color), discrAbstract x y → discrAbstractInt x y = 1 ===> True
-- ∀ (x : List Color) (y : Option Color),
--   true = ( discrAbstract.match_1 (fun (_ : List Color) (_ : Option Color) => Bool) x y
--            (fun (_ : PUnit) => true)
--            (fun (_ : List Color) => false)
--            (fun (_ : Option Color) => false)
--            (fun (_ : List Color) (_ : Option Color) => true) ) →
--   1 = ( discrAbstract.match_1 (fun (_ : List Color) (_ : Option Color) => Int) x y
--         (fun (_ : PUnit) => 1)
--         (fun (_ : List Color) => 0)
--         (fun (_ : Option Color) => 0)
--         (fun (_ : List Color) (_ : Option Color) => 1) )
-- Test case to ensure that structural equivalence on match expression
-- can be performed across instances, e.g. using the same match function
-- with different instantiations.
-- NOTE: Test case reduced to True due to match over fun propagation rule
#testOptimize ["MatchStructEq_2"]
  ∀ (x : List Color) (y : Option Color), discrAbstract x y → discrAbstractInt x y = 1 ===> True


-- ∀ (x : List Color) (y : Option Color)
--   (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (y = Option.none) = (w = Option.none) →
--   discrAbstract x y → discrAbstractInt v w = 1 ===>
-- ∀ (x : List Color) (y : Option Color)
--   (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (Option.none = y) = (Option.none = w) →
-- ( discrAbstract.match_1 (fun (_ : List Color) (_ : Option Color) => Prop) x y
--   (fun (_ : PUnit) => True)
--   (fun (_ : List Color) => False)
--   (fun (_ : Option Color) => False)
--   (fun (_ : List Color) (_ : Option Color) => True) ) →
-- ( discrAbstract.match_1 (fun (_ : List Purpose) (_ : Option Purpose) => Prop) v w
--   (fun (_ : PUnit) => True)
--   (fun (_ : List Purpose) => False)
--   (fun (_ : Option Purpose) => False)
--   (fun (_ : List Purpose) (_ : Option Purpose) => True) )
-- Test cases to ensure that structural equivalence on match expression
-- can be performed across instances, e.g. using the same match function
-- with different instantiations.
inductive Purpose
 | Minting
 | Spending
 | Rewarding
deriving BEq

#testOptimize ["MatchStructEq_3"] (norm-result: 1)
  ∀ (x : List Color) (y : Option Color)
    (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (y = Option.none) = (w = Option.none) →
    discrAbstract x y → discrAbstractInt v w = 1 ===>
  ∀ (x : List Color) (y : Option Color)
    (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (Option.none = y) = (Option.none = w) →
    ( discrAbstract.match_1 (fun (_ : List Color) (_ : Option Color) => Prop) x y
      (fun (_ : PUnit) => True)
      (fun (_ : List Color) => False)
      (fun (_ : Option Color) => False)
      (fun (_ : List Color) (_ : Option Color) => True) ) →
    ( discrAbstract.match_1 (fun (_ : List Purpose) (_ : Option Purpose) => Prop) v w
      (fun (_ : PUnit) => True)
      (fun (_ : List Purpose) => False)
      (fun (_ : Option Purpose) => False)
      (fun (_ : List Purpose) (_ : Option Purpose) => True) )


/-! Test cases to validate when structural equivalence must not be applied. -/

inductive BuiltinArg
| ArgV : BuiltinArg
| ArgQ : BuiltinArg

def ifArgVOtherwiseError (x : Nat) (l : BuiltinArg) : Option Nat :=
 match l with
 | .ArgV => some x
 | .ArgQ => none

def ifArgQOtherwiseError (x : Nat) (l : BuiltinArg) : Option Nat :=
 match l with
 | .ArgQ => some x
 | .ArgV => none

instance : BEq BuiltinArg where
  beq
  | .ArgV, .ArgV => true
  | .ArgQ, .ArgQ => true
  | _, _ => false

theorem BuiltinArg.beq_true_imp_eq : ∀ (x y : BuiltinArg), x == y → x = y := by
  intro x y;
  cases x <;> cases y <;> simp

theorem BuiltinArg.beq_false_imp_not_eq : ∀ (x y : BuiltinArg), ((x == y) = false) → x ≠ y := by
  intro x y;
  cases x <;> cases y <;> simp

def BuiltinArg.decEq (x y : BuiltinArg) : Decidable (Eq x y) :=
  match h:(x == y) with
  | true => isTrue (BuiltinArg.beq_true_imp_eq _ _ h)
  | false => isFalse (BuiltinArg.beq_false_imp_not_eq _ _ h)

-- NOTE: providing decidableEq instance to favor match to ite normalization
instance : DecidableEq BuiltinArg := BuiltinArg.decEq

-- ∀ (x : Nat) (l : BuiltinArg), ifArgVOtherwiseError x l ≠ ifArgQOtherwiseError x l ===>
-- ∀ (x : Nat) (l : BuiltinArg),
--  ¬ ( (¬ BuiltinArg.ArgQ = l → ¬ BuiltinArg.ArgV = l) ∧
--      (BuiltinArg.ArgQ = l → BuiltinArg.ArgV = l) )
-- Test case to ensure that we are not wrongly performing structural equivalence on match
-- NOTE: Reduction due to ite over function propagation rule
#testOptimize [ "MatchStructEqUnchanged_1" ]
  ∀ (x : Nat) (l : BuiltinArg), ifArgVOtherwiseError x l ≠ ifArgQOtherwiseError x l ===>
  ∀ (l : BuiltinArg),
    ¬ ( (¬ BuiltinArg.ArgQ = l → ¬ BuiltinArg.ArgV = l) ∧
        (BuiltinArg.ArgQ = l → BuiltinArg.ArgV = l) )


def discrAbstractInversed (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | [], _ => false
  | _, none => false
  | _, _ => true


-- ∀ (α : Type) (x : List α) (y : Option α), discrAbstract x y ≠ discrAbstractInversed x y ===>
-- ∀ (α : Type) (x : List α) (y : Option α),
--   ¬ ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--        (fun (_ : PUnit) => True)
--        (fun (_ : List α) =>
--          ( discrAbstractInversed.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--            (fun (_ : PUnit) => False)
--            (fun (_ : Option α) => True)
--            (fun (_ : List α) => True)
--            (fun (_ : List α) (_ : Option α) => False) ) )
--        (fun (_ : Option α) =>
--          ( discrAbstractInversed.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--            (fun (_ : PUnit) => False)
--            (fun (_ : Option α) => True)
--            (fun (_ : List α) => True)
--            (fun (_ : List α) (_ : Option α) => False) ) )
--        (fun (_ : List α) (_ : Option α) => True))
-- Test case to ensure that we are not wrongly performing structural equivalence on match
-- NOTE: some match cases reduce to True due to elimMatch optimization rules.
#testOptimize [ "MatchStructEqUnchanged_2" ]
  ∀ (α : Type) (x : List α) (y : Option α), discrAbstract x y ≠ discrAbstractInversed x y ===>
  ∀ (α : Type) (x : List α) (y : Option α),
    ¬ ( discrAbstract.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
         (fun (_ : PUnit) => True)
         (fun (_ : List α) =>
           ( discrAbstractInversed.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
             (fun (_ : PUnit) => False)
             (fun (_ : Option α) => True)
             (fun (_ : List α) => True)
             (fun (_ : List α) (_ : Option α) => False) ) )
         (fun (_ : Option α) =>
           ( discrAbstractInversed.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
             (fun (_ : PUnit) => False)
             (fun (_ : Option α) => True)
             (fun (_ : List α) => True)
             (fun (_ : List α) (_ : Option α) => False) ) )
         (fun (_ : List α) (_ : Option α) => True))


end Tests.StructEqMatch
