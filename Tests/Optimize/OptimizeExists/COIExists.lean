import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.COIExists
/-! ## Test objectives to validate COI reduction on `∃`. -/

/-! Test cases for COI reduction rule:
     - `∃ (n : t), e ===> e (if isSortOrInhabited t ∧ ¬ e.hasLooseBVar e 0)`.
-/

-- ∀ (a : Prop), ∃ (b : Prop), (a ∧ (b ∨ ¬ b)) ===> ∀ (a : Prop), a
#testOptimize [ "ExistsCOI_1" ] ∀ (a : Prop), ∃ (b : Prop), (a ∧ (b ∨ ¬ b)) ===> ∀ (a : Prop), a

-- ∀ (a : Bool), ∃ (b : Bool), (a || (b && ! b)) ===> ∀ (a : Bool), true = a
#testOptimize [ "ExistsCOI_2" ] ∀ (a : Bool), ∃ (b : Bool), (a || (b && ! b)) ===> ∀ (a : Bool), true = a

-- ∀ (w y : Nat), ∃ (x z : Nat), (((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y
#testOptimize [ "ExistsCOI_3" ] ∀ (w y : Nat), ∃ (x z : Nat),(((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y


-- ∀ (w y : Int), ∃ (x z : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y
#testOptimize [ "ExistsCOI_4" ] ∀ (w y : Int), ∃ (x z : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y


-- ∃ (x z : Nat), ∀ (w y : Nat), (((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y
#testOptimize [ "ExistsCOI_5" ] ∃ (x z : Nat), ∀ (w y : Nat), (((100 - x) - 120) * z) + w < y ===> ∀ (w y : Nat), w < y


-- ∃ (x z : Int), ∀ (w y : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y
#testOptimize [ "ExistsCOI_6" ] ∃ (x z : Int), ∀ (w y : Int), ((((100 - x) - 100) + x) * z) + w < y ===> ∀ (w y : Int), w < y


inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Repr

-- ∀ (a b c : Bool) (x z : Color), ∃ (y : Color),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
--  ∀ (x z : Color), x = z
-- Test case: COI reduction applies when inductive type has at least one nullary constructor.
#testOptimize [ "ExistsCOI_7" ] ∀ (a b c : Bool) (x z : Color), ∃ (y : Color),
                                  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                  (if cond then x else y) = z ===>
                                ∀ (x z : Color), x = z

-- ∃ (y : Color), ∀ (a b c : Bool) (x z : Color),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
--  ∀ (x z : Color), x = z
-- Test case: COI reduction applies when inductive type has at least one nullary constructor.
#testOptimize [ "ExistsCOI_8" ] ∃ (y : Color), ∀ (a b c : Bool) (x z : Color),
                                  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                  (if cond then x else y) = z ===>
                                ∀ (x z : Color), x = z

-- ∀ (a b c : Bool) (y z : List Nat), ∃ (x : List Nat),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (y z : List Nat), y = z
-- Test case: COI reduction applies on parametric inductive types.
#testOptimize [ "ExistsCOI_9" ] ∀ (a b c : Bool) (y z : List Nat), ∃ (x : List Nat),
                                  let cond := !((!a || ((b || c) && !(c || b))) || a);
                                  (if cond then x else y) = z ===>
                                ∀ (y z : List Nat), y = z

-- ∃ (x : List Nat), ∀ (a b c : Bool) (y z : List Nat),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (y z : List Nat), y = z
-- Test case: COI reduction applies on parametric inductive types.
#testOptimize [ "ExistsCOI_10" ] ∃ (x : List Nat), ∀ (a b c : Bool) (y z : List Nat),
                                  let cond := !((!a || ((b || c) && !(c || b))) || a);
                                  (if cond then x else y) = z ===>
                                 ∀ (y z : List Nat), y = z

-- ∀ (α : Type) (a b c : Bool) (y z : List α), ∃ (x : List α),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (α : Type) (y z : List α), y = z
-- Test case: COI reduction applies on polymorphic inductive type having an Inhabited instance.
#testOptimize [ "ExistsCOI_11" ] ∀ (α : Type) (a b c : Bool) (y z : List α), ∃ (x : List α),
                                     let cond := !((!a || ((b || c) && !(c || b))) || a);
                                     (if cond then x else y) = z ===>
                                 ∀ (α : Type) (y z : List α), y = z

-- ∀ (α : Type), ∃ (x : List α), ∀ (a b c : Bool) (y z : List α),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then x else y) = z ===>
-- ∀ (α : Type) (y z : List α), y = z
-- Test case: COI reduction applies on polymorphic inductive type having an Inhabited instance.
#testOptimize [ "ExistsCOI_12" ] ∀ (α : Type), ∃ (x : List α), ∀ (a b c : Bool) (y z : List α),
                                     let cond := !((!a || ((b || c) && !(c || b))) || a);
                                     (if cond then x else y) = z ===>
                                 ∀ (α : Type) (y z : List α), y = z


-- ∀ (α : Type) (a b c : Bool), ∃ (x y : List α),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  ¬ ((if cond then x else y) = y) ===> False
-- Test case: COI reduction also applies on sort type.
#testOptimize [ "ExistsCOI_13" ] ∀ (α : Type) (a b c : Bool), ∃ (x y : List α),
                                  let cond := !((!a || ((b || c) && !(c || b))) || a); ¬ (if cond then x else y) = y ===> False


-- ∀ (α : Type) ∃ (x y : List α), ∀ (a b c : Bool),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  ¬ ((if cond then x else y) = y) ===> False
-- Test case: COI reduction also applies on sort type.
#testOptimize [ "ExistsCOI_14" ] ∀ (α : Type), ∃ (x y : List α), ∀ (a b c : Bool),
                                  let cond := !((!a || ((b || c) && !(c || b))) || a); ¬ (if cond then x else y) = y ===> False


-- ∀ (α : Type) (a b c : Bool) (xs ys : List α), ∃ (x y : α), [LT α] → [Decidable (x < y)] →
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
-- ∀ (α : Type) (xs ys : List α), ys = xs
-- Test case: COI reduction rule also removes unused constraints.
#testOptimize [ "ExistsCOI_15" ] ∀ (α : Type) (a b c : Bool) (xs ys : List α), ∃ (x y : α), [LT α] → [Decidable (x < y)] →
                                     let cond := !((!a || ((b || c) && !(c || b))) || a);
                                     (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
                                 ∀ (α : Type) (xs ys : List α), xs = ys


-- ∀ (α : Type), ∃ (x y : α), ∀ (a b c : Bool) (xs ys : List α), [LT α] → [Decidable (x < y)] →
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
-- ∀ (α : Type) (xs ys : List α), ys = xs
-- Test case: COI reduction rule also removes unused constraints.
#testOptimize [ "ExistsCOI_16" ]  ∀ (α : Type), ∃ (x y : α), ∀ (a b c : Bool) (xs ys : List α), [LT α] → [Decidable (x < y)] →
                                     let cond := !((!a || ((b || c) && !(c || b))) || a);
                                     (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
                                  ∀ (α : Type) (xs ys : List α), xs = ys

-- ∀ (α : Type) (β : Type) (x : α) (y z : β), ∃ (f : α → β), ∃ (a b c : Bool),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then f x else y) = z ===>
-- ∀ (β : Type) (y z : β), y = z
-- Test case: COI reduction rules removes unused quantified functions.
#testOptimize [ "ExistsCOI_17" ] ∀ (α : Type) (β : Type) (x : α) (y z : β), ∃ (f : α → β), ∃ (a b c : Bool),
                                   let cond := !((!a || ((b || c) && !(c || b))) || a);
                                   (if cond then f x else y) = z ===>
                                 ∀ (β : Type) (y z : β), y = z

-- ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (a b c : Bool), ∀ (x : α) (y z : β),
--  let cond := !((!a || ((b || c) && !(c || b))) || a);
--  (if cond then f x else y) = z ===>
-- ∀ (β : Type) (y z : β), y = z
-- Test case: COI reduction rules removes unused quantified functions.
#testOptimize [ "ExistsCOI_18" ] ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (a b c : Bool), ∀ (x : α) (y z : β),
                                   let cond := !((!a || ((b || c) && !(c || b))) || a);
                                   (if cond then f x else y) = z ===>
                                 ∀ (β : Type) (y z : β), y = z

-- ∀ (α : Type), ∃ (x y : α), ∃ (ys : List α), ∀ (a b c : Bool) (xs : List α), [LT α] → [Decidable (x < y)] →
--  let cond := ((!a || ((b || c) && !(c || b))) || a);
--  (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
-- ∀ (α : Type), ∃ (x y : α), ∀ (xs : List α), [LT α] →
--   xs = Blaster.dite' (x < y) (fun _ : x < y => [x, y]) (fun _ : ¬ x < y => [y, x])
#testOptimize [ "ExistsCOI_19" ]
  ∀ (α : Type), ∃ (x y : α), ∃ (ys : List α),
  ∀ (a b c : Bool) (xs : List α), [LT α] → [Decidable (x < y)] →
    let cond := ((!a || ((b || c) && !(c || b))) || a);
    (if cond then if x < y then [x, y] else [y, x] else ys) = xs ===>
  ∀ (α : Type), ∃ (x y : α), ∀ (xs : List α), [LT α] →
    xs = Blaster.dite' (x < y) (fun _ : x < y => [x, y]) (fun _ : ¬ x < y => [y, x])

/-! Test cases to ensure when the following COI reduction rule must not be applied:
     - `∃ (n : t), e ===> e (if isSortOrInhabited t ∧ ¬ e.hasLooseBVar e 0)`.
-/

-- ∃ (x y : Nat), ∃ (a b : Prop), x > y → (a ∧ (b ∨ ¬ b)) ===> ∃ (x y : Nat), ∃ (a : Prop), y < x → a
-- Test case: COI reduction rule not applicable on implication
#testOptimize [ "ExistsCOIUnchanged_1" ] ∃ (x y : Nat), ∃ (a b : Prop), x > y → (a ∧ (b ∨ ¬ b)) ===>
                                         ∃ (x y : Nat), ∃ (a : Prop), y < x → a

-- ∃ (x y : Nat), ∃ (a b : Prop), ∀ (h : x > y), (a ∧ (b ∨ ¬ b)) ===> ∃ (x y : Nat), ∃ (a : Prop), ∀ (h : y < x), a
-- Test case: COI reduction rule not applicable on implication
#testOptimize [ "ExistsCOIUnchanged_2" ] ∃ (x y : Nat), ∃ (a b : Prop), ∀ (_h : x > y), (a ∧ (b ∨ ¬ b)) ===>
                                         ∃ (x y : Nat), ∃ (a : Prop), ∀ (_h : y < x), a


-- ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (x y : α), x = y → f x = f y ===>
-- ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (x y : α), x = y → f x = f y
#testOptimize [ "ExistsCOIUnchanged_3" ] ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (x y : α), x = y → f x = f y ===>
                                         ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (x y : α), x = y → f x = f y



-- ∀ (a : Prop), ∃ (b c : Prop), (a ∧ (b ∨ ¬ c)) ===> ∀ (a : Prop), ∃ (b c : Prop), (a ∧ (b ∨ ¬ c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_4" ] ∀ (a : Prop), ∃ (b c : Prop), (a ∧ (b ∨ ¬ c)) ===>
                                         ∀ (a : Prop), ∃ (b c : Prop), (a ∧ (b ∨ ¬ c))

-- ∃ (b c : Prop), ∀ (a : Prop), (a ∧ (b ∨ ¬ c)) ===> ∃ (b c : Prop), ∀ (a : Prop), (a ∧ (b ∨ ¬ c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_5" ] ∃ (b c : Prop), ∀ (a : Prop), (a ∧ (b ∨ ¬ c)) ===>
                                         ∃ (b c : Prop), ∀ (a : Prop), (a ∧ (b ∨ ¬ c))

-- ∀ (a : Bool), ∃ (b c : Bool), (a || (b && ! c)) ===> ∀ (a : Bool), ∃ (b c : Bool), true = (a || (b && ! c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_6" ] ∀ (a : Bool), ∃ (b c : Bool), (a || (b && ! c)) ===>
                                         ∀ (a : Bool), ∃ (b c : Bool), true = (a || (b && ! c))

-- ∃ (b c : Bool), ∀ (a : Bool), (a || (b && ! c)) ===> ∃ (b c : Bool), ∀ (a : Bool), true = (a || (b && ! c))
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_7" ] ∃ (b c : Bool), ∀ (a : Bool), (a || (b && ! c)) ===>
                                         ∃ (b c : Bool), ∀ (a : Bool), true = (a || (b && ! c))

-- ∀ (w y : Nat), ∃ (x z : Nat), (((100 - x) - 120) + x * z) + w < y ===>
-- ∀ (w y : Nat), ∃ (x z : Nat), Nat.add w (Nat.mul x z) < y
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_8" ] ∀ (w y : Nat), ∃ (x z : Nat), (((100 - x) - 120) + x * z) + w < y ===>
                                         ∀ (w y : Nat), ∃ (x z : Nat), Nat.add w (Nat.mul x z) < y

-- ∃ (x z : Nat), ∀ (w y : Nat), (((100 - x) - 120) + x * z) + w < y ===>
-- ∃ (x z : Nat), ∀ (w y : Nat),  Nat.add w (Nat.mul x z) < y
-- Test case: COI reduction rules not applicable if all quantifiers are still referenced.
#testOptimize [ "ExistsCOIUnchanged_9" ] ∃ (x z : Nat), ∀ (w y : Nat), (((100 - x) - 120) + x * z) + w < y ===>
                                         ∃ (x z : Nat), ∀ (w y : Nat), Nat.add w (Nat.mul x z) < y

inductive ColorDegree (α : Type u) where
  | transparent : α -> ColorDegree α
  | red : Color → ColorDegree α
  | blue : Color → ColorDegree α
  | yellow : Color → ColorDegree α
 deriving Repr

-- ∀ (α : Type) (a b c : Bool) (x z : ColorDegree α), ∃ (y : ColorDegree α)
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
--  ∀ (α : Type) (x z : ColorDegree α), ∃ (y : ColorDegree α), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor.
#testOptimize [ "ExistsCOIUnchanged_10" ] ∀ (α : Type) (a b c : Bool) (x z : ColorDegree α), ∃ (y : ColorDegree α),
                                            let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                            (if cond then x else y) = z ===>
                                          ∀ (α : Type) (x z : ColorDegree α), ∃ (_y : ColorDegree α), x = z

-- ∀ (α : Type) ∃ (y : ColorDegree α), ∀ (a b c : Bool) (x z : ColorDegree α),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
--  ∀ (α : Type) ∃ (y : ColorDegree α), ∀ (x z : ColorDegree α), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor.
#testOptimize [ "ExistsCOIUnchanged_11" ] ∀ (α : Type), ∃ (y : ColorDegree α), ∀ (a b c : Bool) (x z : ColorDegree α),
                                            let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                            (if cond then x else y) = z ===>
                                          ∀ (α : Type), ∃ (_y : ColorDegree α), ∀ (x z : ColorDegree α), x = z

inductive NoInstance where
 | first (n : Nat) (h : n < 0) : NoInstance
 | next : NoInstance → NoInstance

-- ∀ (a b c : Bool) (x z : NoInstance), ∃ (y : NoInstance),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
-- ∀ (x y z : NoInstance), ∃ (y : NoInstance), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor
-- or an appropriate Inhabited instance.
#testOptimize [ "ExistsCOIUnchanged_12" ] ∀ (a b c : Bool) (x z : NoInstance), ∃ (y : NoInstance),
                                           let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                           (if cond then x else y) = z ===>
                                         ∀ (x z : NoInstance), ∃ (_y : NoInstance), x = z

-- ∃ (y : NoInstance), ∀ (a b c : Bool) (x z : NoInstance),
--  let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
--  (if cond then x else y) = z ===>
-- ∃ (y : NoInstance), ∀ (x y z : NoInstance), x = z
-- Test case: COI reduction rules not applicable when inductive type does not have at least one nullary constructor
-- or an appropriate Inhabited instance.
#testOptimize [ "ExistsCOIUnchanged_13" ] ∃ (y : NoInstance), ∀ (a b c : Bool) (x z : NoInstance),
                                           let cond := ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b));
                                           (if cond then x else y) = z ===>
                                         ∃ (_y : NoInstance), ∀ (x z : NoInstance), x = z

-- ∃ (x : Empty) (a b c : Bool), !((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===>
-- ∃ (x : Empty), False
-- Test case: COI reduction rules not applicable on Empty.
#testOptimize [ "ExistsCOIUnchanged_14" ] ∃ (_x : Empty) (a b c : Bool), !((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===>
                                          ∃ (_x : Empty), False

-- ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (a b c : Bool), ∀ (x : α) (y z : β),
--  let cond := ((!a || ((b || c) && !(c || b))) || a);
--  (if cond then f x else y) = z ===>
-- ∀ (α : Type) (β : Type), ∃ (f : α → β), ∀ (x : α) (z : β), z = f x
-- Test case: COI reduction rules not removing still referenced quantified function.
#testOptimize [ "ExistsCOIUnchanged_15" ] ∀ (α : Type) (β : Type), ∃ (f : α → β), ∃ (a b c : Bool), ∀ (x : α) (y z : β),
                                             let cond := ((!a || ((b || c) && !(c || b))) || a);
                                             (if cond then f x else y) = z ===>
                                          ∀ (α : Type) (β : Type), ∃ (f : α → β), ∀ (x : α) (z : β), z = f x

end Test.COIExists
