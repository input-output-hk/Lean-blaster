import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.COIForAll
/-! ## Test objectives to validate COI reduction on `∀` and `→`. -/

/-! Test cases for COI reduction rule:
     - `∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)`.
-/

-- ∀ (a b : Prop), (a ∧ (b ∨ ¬ b)) ===> ∀ (a : Prop), a
#testOptimize [ "ForallCOI_1" ] ∀ (a b : Prop), (a ∧ (b ∨ ¬ b)) ===> ∀ (a : Prop), a

-- ∀ (a b : Bool), (a || (b && ! b)) ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallCOI_2" ] ∀ (a b : Bool), (a || (b && ! b)) ===> ∀ (a : Bool), true = a

-- ∀ (w x y z : Nat), (((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y
#testOptimize [ "ForallCOI_3" ] ∀ (w x y z : Nat), (((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y


-- ∀ (w x y z : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y
#testOptimize [ "ForallCOI_4" ]
  ∀ (w x y z : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Repr

-- ∀ (a b c : Bool) (x y z : Color),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
--  ∀ (x z : Color), x = z
-- Test case: COI reduction applies when inductive type has at least one nullary constructor.
#testOptimize [ "ForallCOI_5" ]
  ∀ (a b c : Bool) (x y z : Color),
    let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
    (if cond then x else y) = z ===>
  ∀ (x z : Color), x = z

-- ∀ (a b c : Bool) (x y z : List Nat),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (y z : List Nat), y = z
-- Test case: COI reduction applies on parametric inductive types.
#testOptimize [ "ForallCOI_6" ] ∀ (a b c : Bool) (x y z : List Nat),
                                  let cond := !((!a || ((b || c) && !(c || b))) || a);
                                  (if cond then x else y) = z ===>
                                ∀ (y z : List Nat), y = z

-- ∀ (α : Type) (a b c : Bool) (x y z : List α),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (α : Type) (y z : List α), y = z
-- Test case: COI reduction applies on polymorphic inductive type having an Inhabited instance.
#testOptimize [ "ForallCOI_7" ] ∀ (α : Type) (a b c : Bool) (x y z : List α),
                                     let cond := !((!a || ((b || c) && !(c || b))) || a);
                                     (if cond then x else y) = z ===>
                                ∀ (α : Type) (y z : List α), y = z


-- ∀ (α : Type) (a b c : Bool) (x y : List α),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  ¬ ((if cond then x else y) = y) ===> False
-- Test case: COI reduction also applies on sort type.
#testOptimize [ "ForallCOI_8" ]
  ∀ (α : Type) (a b c : Bool) (x y : List α),
    let cond := !((!a || ((b || c) && !(c || b))) || a); ¬ (if cond then x else y) = y ===> False


-- ∀ (α : Type) (a b c : Bool) (x y : α) (xs ys : List α), [LT α] → [Decidable (x < y)] →
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
-- ∀ (α : Type) (xs ys : List α), ys = xs
-- Test case: COI reduction rule also removes unused constraints.
#testOptimize [ "ForallCOI_9" ]
  ∀ (α : Type) (a b c : Bool) (x y : α) (xs ys : List α), [LT α] → [Decidable (x < y)] →
      let cond := !((!a || ((b || c) && !(c || b))) || a);
      (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
  ∀ (α : Type) (xs ys : List α), xs = ys

-- ∀ (α : Type) (β : Type) (f : α → β) (x : α) (y z : β) (a b c : Bool),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then f x else y) = z ===>
-- ∀ (β : Type) (y z : β), y = z
-- Test case: COI reduction rules removes unused quantified functions.
#testOptimize [ "ForallCOI_10" ]
  ∀ (α : Type) (β : Type) (f : α → β) (x : α) (y z : β) (a b c : Bool),
    let cond := !((!a || ((b || c) && !(c || b))) || a); (if cond then f x else y) = z ===>
  ∀ (β : Type) (y z : β), y = z

-- ∀ (α : Type) (a b c : Bool) (x y : α) (xs ys : List α), [LT α] → [Decidable (x < y)] →
--  let cond := ((!a || ((b || c) && !(c || b))) || a);
--  (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
-- ∀ (α : Type) (x y : α) (xs : List α), [LT α] → [Decidable (x < y)] →
--  xs = if x < y then [x, y] else [y, x
#testOptimize [ "ForallCOI_11" ]
  ∀ (α : Type) (a b c : Bool) (x y : α) (xs ys : List α), [LT α] → [Decidable (x < y)] →
    let cond := ((!a || ((b || c) && !(c || b))) || a);
    (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
  ∀ (α : Type) (x y : α) (xs : List α), [LT α] → [Decidable (x < y)] →
    xs = if x < y then [x, y] else [y, x]


/-! Test cases to ensure when the following COI reduction rule must not be applied:
     - `∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)`.
-/

-- ∀ (x y : Nat) (a b : Prop), x > y → (a ∧ (b ∨ ¬ b)) ===> ∀ (x y : Nat) (a : Prop), y < x → a
-- Test case: COI reduction rule not applicable on implication
#testOptimize [ "ForallCOIUnchanged_1" ]
  ∀ (x y : Nat) (a b : Prop), x > y → (a ∧ (b ∨ ¬ b)) ===>
  ∀ (x y : Nat) (a : Prop), y < x → a

-- ∀ (x y : Nat) (a b : Prop) (h : x > y), (a ∧ (b ∨ ¬ b)) ===> ∀ (x y : Nat) (a : Prop) (h : y < x), a
-- Test case: COI reduction rule not applicable on implication
#testOptimize [ "ForallCOIUnchanged_2" ]
  ∀ (x y : Nat) (a b : Prop) (_h : x > y), (a ∧ (b ∨ ¬ b)) ===>
  ∀ (x y : Nat) (a : Prop) (_h : y < x), a


-- ∀ (α : Type) (β : Type) (f : α → β) (x y : α), x = y → f x = f y ===>
-- ∀ (α : Type) (β : Type) (f : α → β) (x y : α), x = y → f x = f y
-- Test case: COI reduction rules not applicable on arrow types.
#testOptimize [ "ForallCOIUnchanged_3" ]
  ∀ (α : Type) (β : Type) (f : α → β) (x y : α), x = y → f x = f y ===>
  ∀ (α : Type) (β : Type) (f : α → β) (x y : α), x = y → f x = f y


-- ∀ (a b c : Prop), (a ∧ (b ∨ ¬ c)) ===> ∀ (a b c : Prop), (a ∧ (b ∨ ¬ c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ForallCOIUnchanged_4" ]
  ∀ (a b c : Prop), (a ∧ (b ∨ ¬ c)) ===> ∀ (a b c : Prop), (a ∧ (b ∨ ¬ c))

-- ∀ (a b c : Bool), (a || (b && ! c)) ===> ∀ (a b c : Bool), true = (a || (b && !c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ForallCOIUnchanged_5" ]
  ∀ (a b c : Bool), (a || (b && ! c)) ===> ∀ (a b c : Bool), true = (a || (b && !c))

-- ∀ (w x y z : Nat), (((100 - x) - 120) + x * z) + w < y ===>
-- ∀ (w x y z : Nat), Nat.add w (Nat.mul x z) < y
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ForallCOIUnchanged_6" ]
  ∀ (w x y z : Nat), ((((100 - x) - 120) + x) * z) + w < y ===>
  ∀ (w x y z : Nat), Nat.add w (Nat.mul x z) < y

inductive ColorDegree (α : Type u) where
  | transparent : α -> ColorDegree α
  | red : Color → ColorDegree α
  | blue : Color → ColorDegree α
  | yellow : Color → ColorDegree α
 deriving Repr

-- ∀ (α : Type) (a b c : Bool) (x y z : ColorDegree α),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
-- ∀ (α : Type) (x y z : ColorDegree α), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor.
#testOptimize [ "ForallCOIUnchanged_7" ]
  ∀ (α : Type) (a b c : Bool) (x y z : ColorDegree α),
    let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
    (if cond then x else y) = z ===>
  ∀ (α : Type) (x _y z : ColorDegree α), x = z

inductive NoInstance where
 | first (n : Nat) (h : n < 0) : NoInstance
 | next : NoInstance → NoInstance

-- ∀ (a b c : Bool) (x y z : NoInstance),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
-- ∀ (x y z : NoInstance), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor
-- or an appropriate Inhabited instance.
#testOptimize [ "ForallCOIUnchanged_8" ]
  ∀ (a b c : Bool) (x y z : NoInstance),
    let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
    (if cond then x else y) = z ===>
  ∀ (x _y z : NoInstance), x = z

-- ∀ (x : Empty) (a b c : Bool), !((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===>
-- ∀ (x : Empty), False
-- Test case: COI reduction rules not applicable on Empty.
#testOptimize [ "ForallCOIUnchanged_9" ]
  ∀ (_x : Empty) (a b c : Bool), !((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===>
  ∀ (_x : Empty), False

-- ∀ (α : Type) (β : Type) (f : α → β) (x : α) (y z : β) (a b c : Bool),
--  let cond := ((!a || ((b || c) && !(c || b))) || a);
--  (if cond then f x else y) = z ===>
-- ∀ (α : Type) (β : Type) (f : α → β) (x : α) (z : β), z = f x
-- Test case: COI reduction rules not removing still referenced quantified function.
#testOptimize [ "ForallCOIUnchanged_10" ]
  ∀ (α : Type) (β : Type) (f : α → β) (x : α) (y z : β) (a b c : Bool),
    let cond := ((!a || ((b || c) && !(c || b))) || a); (if cond then f x else y) = z ===>
  ∀ (α : Type) (β : Type) (f : α → β) (x : α) (z : β), z = f x

end Test.COIForAll
