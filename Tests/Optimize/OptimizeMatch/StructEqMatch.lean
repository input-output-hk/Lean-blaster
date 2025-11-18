import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.StructEqMatch

/-! ## Test objectives to validate structural equivalence on match expressions -/

/-! Test cases to validate when structural equivalence must be applied. -/

def discrAbstractOne (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [], _ => false
  | _, _ => true

def discrAbstractIntOne (x : List α) (y : Option α) : Int :=
  match x, y with
  | [], none => 1
  | _, none => 0
  | [], _ => 0
  | _, _ => 1

 -- ∀ (α : Type) (x : List α) (y : Option α), discrAbstractOne x y → discrAbstractInt x y = 1 ===> True
 -- Test case to ensure that structural equivalence on match expression
 -- can be performed across instances, e.g. using the same match function
 -- with different instantiations.
 -- NOTE: Test case reduce to True due to match over fun propagation rule
#testOptimize ["MatchStructEq_1"]
  ∀ (α : Type) (x : List α) (y : Option α), discrAbstractOne x y → discrAbstractIntOne x y = 1 ===> True

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | yellow : Color → Color
  | black : Color
  | green : Color → Color
  | white : Color

-- ∀ (x : List Color) (y : Option Color), discrAbstractOne x y → discrAbstractInt x y = 1 ===> True
-- Test case to ensure that structural equivalence on match expression
-- can be performed across instances, e.g. using the same match function
-- with different instantiations.
-- NOTE: Test case reduced to True due to match over fun propagation rule
#testOptimize ["MatchStructEq_2"]
  ∀ (x : List Color) (y : Option Color), discrAbstractOne x y → discrAbstractIntOne x y = 1 ===> True


-- ∀ (x : List Color) (y : Option Color)
--   (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (y = Option.none) = (w = Option.none) →
--   discrAbstract x y → discrAbstractInt v w = 1 ===>
-- ∀ (x : List Color) (y : Option Color) (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (Option.none = y) = (Option.none = w) →
--   (¬ ([] = x ∧ Option.none = y) → ¬ [] = x ∧ ¬ Option.none = y) →
--     ¬ ([] = v ∧ Option.none = w) → ¬ [] = v ∧ ¬ Option.none = w
-- NOTE: match is now normalized to ite since we are no more constrained
-- with the decidable instance for Eq.
-- Test cases to ensure that structural equivalence on match expression
-- can be performed across instances, e.g. using the same match function
-- with different instantiations.
inductive Purpose
 | Minting
 | Spending
 | Rewarding
deriving BEq

#testOptimize ["MatchStructEq_3"]
  ∀ (x : List Color) (y : Option Color)
    (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (y = Option.none) = (w = Option.none) →
    discrAbstractOne x y → discrAbstractIntOne v w = 1 ===>
  ∀ (x : List Color) (y : Option Color) (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (Option.none = y) = (Option.none = w) →
    (¬ ([] = x ∧ Option.none = y) → ¬ [] = x ∧ ¬ Option.none = y) →
      ¬ ([] = v ∧ Option.none = w) → ¬ [] = v ∧ ¬ Option.none = w


def discrAbstractTwo (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], some _ => true
  | _, none => false
  | _, _ => true

def discrAbstractIntTwo (x : List α) (y : Option α) : Int :=
  match x, y with
  | [], some _ => 1
  | _, none => 0
  | _, _ => 1

-- ∀ (x : List Color) (y : Option Color)
--   (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (y = Option.none) = (w = Option.none) →
--   discrAbstractTwo x y → discrAbstractIntTwo v w = 1 ===>
-- ∀ (x : List Color) (y : Option Color)
--   (v : List Purpose) (w : Option Purpose),
--   List.length x = List.length v →
--   (Option.none = y) = (Option.none = w) →
--   ( discrAbstractTwo.match_1 (fun (_ : List Color) (_ : Option Color) => Prop) x y
--     (fun (_ : Color) => True)
--     (fun (_ : List Color) => False)
--     (fun (_ : List Color) (_ : Option Color) => True) ) →
--   ( discrAbstractTwo.match_1 (fun (_ : List Purpose) (_ : Option Purpose) => Prop) v w
--     (fun (_ : Purpose) => True)
--     (fun (_ : List Purpose) => False)
--     (fun (_ : List Purpose) (_ : Option Purpose) => True) )
-- Test cases to ensure that structural equivalence on match expression
-- can be performed across instances, e.g. using the same match function
-- with different instantiations.
#testOptimize ["MatchStructEq_4"] (norm-result: 1)
  ∀ (x : List Color) (y : Option Color)
    (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (y = Option.none) = (w = Option.none) →
    discrAbstractTwo x y → discrAbstractIntTwo v w = 1 ===>
  ∀ (x : List Color) (y : Option Color)
    (v : List Purpose) (w : Option Purpose),
    List.length x = List.length v →
    (Option.none = y) = (Option.none = w) →
    ( discrAbstractTwo.match_1 (fun (_ : List Color) (_ : Option Color) => Prop) x y
      (fun (_ : Color) => True)
      (fun (_ : List Color) => False)
      (fun (_ : List Color) (_ : Option Color) => True) ) →
    ( discrAbstractTwo.match_1 (fun (_ : List Purpose) (_ : Option Purpose) => Prop) v w
      (fun (_ : Purpose) => True)
      (fun (_ : List Purpose) => False)
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


def discrAbstractInversedOne (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | [], _ => false
  | _, none => false
  | _, _ => true

-- ∀ (α : Type) (x : List α) (y : Option α), discrAbstract x y ≠ discrAbstractInversed x y ===> False
-- NOTE: match is now normalized to ite since we are no more constrained with the decidable instance for Eq
-- Test case to ensure that we are not wrongly performing structural equivalence on match
#testOptimize [ "MatchStructEqUnchanged_2" ]
  ∀ (α : Type) (x : List α) (y : Option α), discrAbstractOne x y ≠ discrAbstractInversedOne x y ===> False


def discrAbstractInversedTwo (x : List α) (y : Option α) : Bool :=
  match x, y with
  | _ , none => false
  | [], some _ => true
  | _, _ => true

-- ∀ (α : Type) (x : List α) (y : Option α), discrAbstractTwo x y ≠ discrAbstractInversedTwo x y ===>
-- ∀ (α : Type) (x : List α) (y : Option α),
--   ¬  ( discrAbstractInversedTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--        (fun (_ : List α) =>
--          ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--            (fun (_ : α) => False)
--            (fun (_ : List α) => True)
--            (fun (_ : List α) (_ : Option α) => False)))
--        (fun (_ : α) => True)
--        (fun (_ : List α) (_ : Option α) =>
--          ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
--            (fun (_ : α) => True)
--            (fun (_ : List α) => False)
--            (fun (_ : List α) (_ : Option α) => True))))
-- Test case to ensure that we are not wrongly performing structural equivalence on match
-- NOTE: some match cases reduce to True due to elimMatch optimization rules.
#testOptimize [ "MatchStructEqUnchanged_3" ]
  ∀ (α : Type) (x : List α) (y : Option α), discrAbstractTwo x y ≠ discrAbstractInversedTwo x y ===>
  ∀ (α : Type) (x : List α) (y : Option α),
    ¬  ( discrAbstractInversedTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
         (fun (_ : List α) =>
           ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
             (fun (_ : α) => False)
             (fun (_ : List α) => True)
             (fun (_ : List α) (_ : Option α) => False)))
         (fun (_ : α) => True)
         (fun (_ : List α) (_ : Option α) =>
           ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x y
             (fun (_ : α) => True)
             (fun (_ : List α) => False)
             (fun (_ : List α) (_ : Option α) => True))))

end Tests.StructEqMatch
