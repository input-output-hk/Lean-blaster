import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.NormHOF

/-! ## Test objectives to validate normalization rules on functions passed as arguments (i.e., HOF)  -/


/-! Test cases to ensure that non-recursive function passed as arguments are properly inlined. -/

def f1 (a: Nat) (b : Nat) : Nat := a + b

-- ∀ (x : Nat) (xs : List Nat), List.foldr f1 x xs ≥ x ===>
-- ∀ (x : Nat) (xs : List Nat),
--  x ≤ List.foldr (λ (a : Nat) (b : Nat) => Nat.add a b) x xs
#testOptimize [ "ConstNonRecFunArg_1" ] ∀ (x : Nat) (xs : List Nat), List.foldr f1 x xs ≥ x ===>
                                        ∀ (x : Nat) (xs : List Nat),
                                          x ≤ List.foldr (λ (a : Nat) (b : Nat) => Nat.add a b) x xs

def g1 (a: Nat) (b : Nat) : Nat := b + a

-- ∀ (x : Nat) (xs : List Nat), List.foldr f1 x xs = List.foldr g1 x xs ===> True
#testOptimize [ "ConstNonRecFunArg_2" ] ∀ (x : Nat) (xs : List Nat),
                                         List.foldr f1 x xs = List.foldr g1 x xs ===> True

def f2 (a : Nat) (b : Nat) (c : Nat) := c + g1 a b

-- ∀ (x : Nat) (xs : List Nat), List.foldr (f2 x) x xs = List.foldr (g2 x) x xs ===> True
#testOptimize [ "ConstNonRecFunArg_3" ] ∀ (x : Nat) (xs : List Nat), List.foldr (f2 x) x xs ≥ x ===>
                                        ∀ (x : Nat) (xs : List Nat),
                                          x ≤ List.foldr (λ (b : Nat) (c : Nat) => Nat.add c (Nat.add x b)) x xs

def g2 (a : Nat) (b : Nat) (c : Nat) := f1 a b + c

-- ∀ (x : Nat) (xs : List Nat), List.foldr (f2 x) x xs = List.foldr (g2 x) x xs ===> True
#testOptimize [ "ConstNonRecFunArg_4" ] ∀ (x : Nat) (xs : List Nat),
                                         List.foldr (f2 x) x xs = List.foldr (g2 x) x xs ===> True

def f3 := f1
def g3 := g1

-- ∀ (x : Nat) (xs : List Nat), List.foldr f3 x xs ≥ x ===>
-- ∀ (x : Nat) (xs : List Nat),
--  x ≤ List.foldr (λ (a : Nat) (b : Nat) => Nat.add a b) x xs
#testOptimize [ "ConstNonRecFunArg_5" ] ∀ (x : Nat) (xs : List Nat), List.foldr f3 x xs ≥ x ===>
                                        ∀ (x : Nat) (xs : List Nat),
                                          x ≤ List.foldr (λ (a : Nat) (b : Nat) => Nat.add a b) x xs

-- ∀ (x : Nat) (xs : List Nat), List.foldr f3 x xs = List.foldr g3 x xs ===> True
#testOptimize [ "ConstNonRecFunArg_6" ] ∀ (x : Nat) (xs : List Nat),
                                         List.foldr f3 x xs = List.foldr g3 x xs ===> True

/-! Test cases to ensure that structural equivalence are properly performed on recursive functions passed as arguments. -/

def addNat (a : Nat) (b : Nat) : Nat :=
 match a, b with
 | _, Nat.zero => a
 | _, Nat.succ b => Nat.succ (addNat a b)

-- (∀ (x : Nat) (xs : List Nat), List.foldr addNat x xs ≥ x) →
-- ∀ (y : Nat) (ys: List Nat), List.foldr Nat.add y ys ≥ y ===> True
#testOptimize [ "ConstRecFunArg_1" ] (∀ (x : Nat) (xs : List Nat), List.foldr addNat x xs ≥ x) →
                                      ∀ (y : Nat) (ys: List Nat), List.foldr Nat.add y ys ≥ y ===> True

-- ∀ (x : Nat) (xs : List Nat),
--   List.foldr addNat x xs ≥ x → List.foldr Nat.add x xs ≥ x ===> True
#testOptimize [ "ConstRecFunArg_2" ] ∀ (x : Nat) (xs : List Nat),
                                       List.foldr addNat x xs ≥ x → List.foldr Nat.add x xs ≥ x ===> True

-- ∀ (x : Nat) (xs : List Nat), (List.foldr addNat x xs ≥ x) = (List.foldr Nat.add x xs ≥ x) ===> True
#testOptimize [ "ConstRecFunArg_3" ] ∀ (x : Nat) (xs : List Nat),
                                       (List.foldr addNat x xs ≥ x) = (List.foldr Nat.add x xs ≥ x) ===> True

-- ∀ (x : Nat) (xs : List Nat), List.foldr addNat x xs ≥ x ===>
-- ∀ (x : Nat) (xs : List Nat), x ≤ List.foldr Nat.add x xs
#testOptimize [ "ConstRecFunArg_4" ] ∀ (x : Nat) (xs : List Nat), List.foldr addNat x xs ≥ x ===>
                                     ∀ (x : Nat) (xs : List Nat), x ≤ List.foldr Nat.add x xs

def addAlias (x : Nat) (y : Nat) : Nat := addNat x y

def mulNat (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | _, Nat.zero => 0
 | _, Nat.succ b => addAlias x (mulNat x b)

def mulAlias := mulNat

-- (∀ (x : Nat) (xs : List Nat), List.foldr mulAlias x xs ≥ x) →
-- ∀ (y : Nat) (ys: List Nat), List.foldr Nat.mul y ys ≥ y ===> True
#testOptimize [ "ConstRecFunArg_5" ] (∀ (x : Nat) (xs : List Nat), List.foldr mulAlias x xs ≥ x) →
                                      ∀ (y : Nat) (ys: List Nat), List.foldr Nat.mul y ys ≥ y ===> True

-- ∀ (x : Nat) (xs : List Nat),
--   List.foldr mulAlias x xs ≥ x → List.foldr Nat.mul x xs ≥ x ===> True
#testOptimize [ "ConstRecFunArg_6" ] ∀ (x : Nat) (xs : List Nat),
                                       List.foldr mulAlias x xs ≥ x → List.foldr Nat.mul x xs ≥ x ===> True

-- ∀ (x : Nat) (xs : List Nat), (List.foldr mulAlias x xs ≥ x) = (List.foldr Nat.mul x xs ≥ x) ===> True
#testOptimize [ "ConstRecFunArg_7" ] ∀ (x : Nat) (xs : List Nat),
                                       (List.foldr mulAlias x xs ≥ x) = (List.foldr Nat.mul x xs ≥ x) ===> True

-- ∀ (x : Nat) (xs : List Nat), List.foldr mulAlias x xs ≥ x ===>
-- ∀ (x : Nat) (xs : List Nat), x ≤ List.foldr Nat.mul x xs
#testOptimize [ "ConstRecFunArg_8" ] ∀ (x : Nat) (xs : List Nat), List.foldr mulAlias x xs ≥ x ===>
                                     ∀ (x : Nat) (xs : List Nat), x ≤ List.foldr Nat.mul x xs


/-! Test cases to ensure that non-recursive opaque function passed as arguments are not inlined. -/

-- ∀ (x : Int) (xs : List Int), List.foldr Int.add x xs ≥ x ===>
-- ∀ (x : Int) (xs : List Int), x ≤ List.foldr Int.add x xs
-- NOTE: Int.add is not a recursive function.
#testOptimize [ "ConstNonRecOpaqueFunArg_1" ] ∀ (x : Int) (xs : List Int), List.foldr Int.add x xs ≥ x ===>
                                              ∀ (x : Int) (xs : List Int), x ≤ List.foldr Int.add x xs

-- ∀ (x : Int) (xs : List Int), List.foldr Int.mul x xs ≥ x ===>
-- ∀ (x : Int) (xs : List Int), x ≤ List.foldr Int.mul x xs
-- NOTE: Int.mul is not a recursive function.
#testOptimize [ "ConstNonRecOpaqueFunArg_2" ] ∀ (x : Int) (xs : List Int), List.foldr Int.mul x xs ≥ x ===>
                                              ∀ (x : Int) (xs : List Int), x ≤ List.foldr Int.mul x xs

-- ∀ (x : Int) (xs : List Int), List.foldr Int.add x (List.map Int.neg xs) ≤ x ===>
-- ∀ (x : Int) (xs : List Int), List.foldr Int.add x (List.map Int.neg xs) ≤ x
-- NOTE: Int.neg is not a recursive function.
#testOptimize [ "ConstNonRecOpaqueFunArg_3" ] ∀ (x : Int) (xs : List Int), List.foldr Int.add x (List.map Int.neg xs) ≤ x ===>
                                              ∀ (x : Int) (xs : List Int), List.foldr Int.add x (List.map Int.neg xs) ≤ x


-- ∀ (x : Int) (xs : List Int), List.foldr Nat.add (Int.toNat x) (List.map Int.toNat xs) ≤ (Int.toNat x) ===>
-- ∀ (x : Int) (xs : List Int), List.foldr Nat.add (Int.toNat x) (List.map Int.toNat xs) ≤ (Int.toNat x) ===>
-- NOTE: Int.toNat is not a recursive function.
#testOptimize [ "ConstNonRecOpaqueFunArg_4" ] ∀ (x : Int) (xs : List Int),
                                                List.foldr Nat.add (Int.toNat x) (List.map Int.toNat xs) ≤ (Int.toNat x) ===>
                                              ∀ (x : Int) (xs : List Int),
                                                List.foldr Nat.add (Int.toNat x) (List.map Int.toNat xs) ≤ (Int.toNat x)

-- ∀ (xs : List Bool), List.foldr and true xs = List.all xs id ===>
-- ∀ (xs : List Bool), List.all xs (λ x => x) = List.foldr and true xs
-- NOTE: May be resolved to true when specializing recursive function with fun arguments
#testOptimize [ "ConstNonRecOpaqueFunArg_5" ] ∀ (xs : List Bool), List.foldr and true xs = List.all xs id ===>
                                              ∀ (xs : List Bool), List.all xs (λ x => x) = List.foldr and true xs

-- ∀ (xs : List Bool), List.foldr or true xs = List.any xs id ===>
-- ∀ (xs : List Bool), List.any xs (λ x => x) = List.foldr or true xs
-- NOTE: May be resolved to true when specializing recursive function with fun arguments
#testOptimize [ "ConstNonRecOpaqueFunArg_6" ] ∀ (xs : List Bool), List.foldr or true xs = List.any xs id ===>
                                              ∀ (xs : List Bool), List.any xs (λ x => x) = List.foldr or true xs

-- ∀ (xs : List Bool), List.any xs id = !(List.any (List.map not xs) id) ===>
-- ∀ (xs : List Bool), (!(List.any (List.map not xs) (λ x => x))) = List.any xs (λ x => x)
#testOptimize [ "ConstNonRecOpaqueFunArg_7" ] ∀ (xs : List Bool), List.any xs id = !(List.any (List.map not xs) id) ===>
                                              ∀ (xs : List Bool),
                                                (!(List.any (List.map not xs) (λ x => x))) = List.any xs (λ x => x)


/-! Test cases to ensure that undeclared functions passed as arguments are handled properly. -/

-- ∀ (f : Int → Int) (x : Int) (xs : List Int),
--  List.foldr (λ a acc => Int.add (f a) acc) x xs =
--  List.foldr Int.add x (List.map f xs) ===>
-- ∀ (f : Int → Int) (x : Int) (xs : List Int),
--  List.foldr Int.add x (List.map f xs) =
--  List.foldr (λ a acc => Int.add acc (f a)) x xs
-- NOTE: Test case for quantified functions
#testOptimize [ "ConstUndeclaredFunArg_1" ] ∀ (f : Int → Int) (x : Int) (xs : List Int),
                                              List.foldr (λ a acc => Int.add (f a) acc) x xs =
                                              List.foldr Int.add x (List.map f xs) ===>
                                            ∀ (f : Int → Int) (x : Int) (xs : List Int),
                                              List.foldr Int.add x (List.map f xs) =
                                              List.foldr (λ a acc => Int.add acc (f a)) x xs

variable (fg : Int → Int)

-- ∀ (x : Int) (xs : List Int),
--  List.foldr (λ a acc => Int.add (fg a) acc) x xs =
--  List.foldr Int.add x (List.map fg xs) ===>
-- ∀ (x : Int) (xs : List Int),
--  List.foldr Int.add x (List.map fg xs) =
--  List.foldr (λ a acc => Int.add acc (fg a)) x xs
-- NOTE: Test case for global free variable
#testOptimize [ "ConstUndeclaredFunArg_2" ] ∀ (x : Int) (xs : List Int),
                                              List.foldr (λ a acc => Int.add (fg a) acc) x xs =
                                              List.foldr Int.add x (List.map fg xs) ===>
                                            ∀ (x : Int) (xs : List Int),
                                              List.foldr Int.add x (List.map fg xs) =
                                              List.foldr (λ a acc => Int.add acc (fg a)) x xs

class IntClass where
  add (x : Int) (y : Int) : Int := x + y
  sub (x : Int) (y : Int) : Int := x - y
  mul (x : Int) (y : Int) : Int := x * y
  map : Int -> Nat

-- ∀ (x : Nat) (xs : List Int), [IntClass] →
--   List.foldr (λ a acc => Nat.add (IntClass.map a) acc) x xs =
--   List.foldr Nat.add x (List.map IntClass.map xs) ===>
-- ∀ (x : Nat) (xs : List Int), [IntClass] →
--   List.foldr (λ a acc => Nat.add acc (IntClass.map a)) x xs =
--   List.foldr Nat.add x (List.map IntClass.map xs)
-- NOTE: Test case for undeclared non polymorphic type class.
-- NOTE: normConst rule is not triggered in this case as `IntClass.map` is
-- implicitly applied to the class instance
#testOptimize [ "ConstUndeclaredFunArg_3" ] ∀ (x : Nat) (xs : List Int), [IntClass] →
                                              List.foldr (λ a acc => Nat.add (IntClass.map a) acc) x xs =
                                              List.foldr Nat.add x (List.map IntClass.map xs) ===>
                                            ∀ (x : Nat) (xs : List Int), [IntClass] →
                                              List.foldr (λ a acc => Nat.add acc (IntClass.map a)) x xs =
                                              List.foldr Nat.add x (List.map IntClass.map xs)

-- ∀ (α : Type) (β : Type) (f : β → β → β) (m : α → β) (x : β) (xs : List α),
--  List.foldr (λ a acc => f (m a) acc) x xs =
--  List.foldr f x (List.map m xs) ===>
-- ∀ (α : Type) (β : Type) (f : β → β → β) (m : α → β) (x : β) (xs : List α),
--  List.foldr (λ a acc => f (m a) acc) x xs =
--  List.foldr f x (List.map m xs)
-- NOTE: Test case for undeclared polymorphic function
#testOptimize [ "ConstUndeclaredFunArg_4" ] ∀ (α : Type) (β : Type) (f : β → β → β) (m : α → β) (x : β) (xs : List α),
                                              List.foldr (λ a acc => f (m a) acc) x xs =
                                              List.foldr f x (List.map m xs) ===>
                                            ∀ (α : Type) (β : Type) (f : β → β → β) (m : α → β) (x : β) (xs : List α),
                                              List.foldr (λ a acc => f (m a) acc) x xs =
                                              List.foldr f x (List.map m xs)

opaque fo : Int → Int

-- ∀ (x : Int) (xs : List Int),
--    List.foldr (λ a acc => Int.add (fo a) acc) x xs =
--    List.foldr Int.add x (List.map fo xs) ===>
-- ∀ (x : Int) (xs : List Int),
--   List.foldr Int.add x (List.map (λ _a => 0) xs) =
--   List.foldr (λ _a acc => acc) x xs
-- NOTE: Test case for opaque function (reduced to a constant value)
#testOptimize [ "ConstUndeclaredFunArg_5" ] (norm-nat-in-result: 1)
                                            ∀ (x : Int) (xs : List Int),
                                               List.foldr (λ a acc => Int.add (fo a) acc) x xs =
                                               List.foldr Int.add x (List.map fo xs) ===>
                                            ∀ (x : Int) (xs : List Int),
                                              List.foldr Int.add x (List.map (λ _a => 0) xs) =
                                              List.foldr (λ _a acc => acc) x xs


/-! Test cases to ensure that polymorphic function (recursive or not) cannot trigger the normConst rule. -/

class Size (α : Type u) where
  size : α → Nat

def mapOption [Size α] (x : Option α) : Nat :=
 match x with
 | none => 0
 | some a => Size.size a

-- ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
--    List.foldr Nat.add x (List.map mapOption xs) ≥ x ===>
-- ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
--    x ≤ ( List.foldr Nat.add x
--          (List.map
--            (λ (x : Option α) =>
--              mapOption.match_1
--              (λ (_ : Option α) => Nat)
--              x
--              (λ (_ : Unit) => 0)
--              (λ (a : α) => Size.size a)
--            ) xs ) )
-- NOTE: Test case to ensure that polymorphic non-recursive functions passed
-- as argument are function applications and therefore cannot trigger normConst rule.
#testOptimize [ "ConstPolyFunArg_1" ] (norm-nat-in-result: 1)
                                      ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
                                         List.foldr Nat.add x (List.map mapOption xs) ≥ x ===>
                                      ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
                                         x ≤ ( List.foldr Nat.add x
                                               (List.map
                                                 (λ (x : Option α) =>
                                                   mapOption.match_1
                                                   (λ (_ : Option α) => Nat)
                                                   x
                                                   (λ (_ : Unit) => 0)
                                                   (λ (a : α) => Size.size a)
                                                 ) xs ) )

abbrev mapAlias [Size α] (x : Option α) := mapOption x

-- ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
--  List.foldr Nat.add x (List.map mapOption xs) =
--  List.foldr Nat.add x (List.map mapAlias xs) ===> True
-- NOTE: Test case to ensure that polymorphic non-recursive functions passed
-- as arguments are function applications and therefore cannot trigger normConst rule.
#testOptimize [ "ConstPolyFunArg_2" ] ∀ (α : Type) (x : Nat) (xs : List (Option α)), [Size α] →
                                         List.foldr Nat.add x (List.map mapOption xs) =
                                         List.foldr Nat.add x (List.map mapAlias xs) ===> True

-- ∀ (α : Type) (x : Nat) (xs : List (List α)),
--  List.foldr Nat.add x (List.map List.length xs) ≥ x ===>
-- ∀ (α : Type) (x : Nat) (xs : List (List α)),
--  x ≤ List.foldr Nat.add x (List.map List.length xs)
-- NOTE: Test case to ensure that polymorphic recursive functions passed
-- as argument are function applications and therefore cannot trigger normConst rule.
#testOptimize [ "ConstPolyFunArg_3" ] ∀ (α : Type) (x : Nat) (xs : List (List α)),
                                        List.foldr Nat.add x (List.map List.length xs) ≥ x ===>
                                      ∀ (α : Type) (x : Nat) (xs : List (List α)),
                                        x ≤ List.foldr Nat.add x (List.map List.length xs)

def listLength : List α → Nat
  | [] => 0
  | _ :: as => 1 + listLength as

#testOptimize [ "ConstPolyFunArg_4" ] ∀ (α : Type) (x : Nat) (xs : List (List α)),
                                        List.foldr Nat.add x (List.map List.length xs) =
                                        List.foldr Nat.add x (List.map listLength xs) ===> True

/-! Test cases to ensure that class constraints are properly handled by the normConst rule. -/

class IntClass2 extends IntClass where
  map x := Int.toNat x

def intMapper [IntClass] (x : Int) : Nat := IntClass.map x

#testOptimize [ "ConstClassCstrArg_1" ] ∀ (x : Nat) (xs : List Int), [IntClass2] →
                                          List.foldr Nat.add x (List.map intMapper xs) ≥ x ===>
                                        ∀ (x : Nat) (xs : List Int), [IntClass2] →
                                          x ≤ List.foldr Nat.add x (List.map (λ x => IntClass.map x) xs)


/-! Test cases to ensure that constructors passed as arguments are properly handled. -/

#testOptimize [ "ConstClassCtorArg_1" ] ∀ (x : Int) (xs : List Nat),
                                          List.foldr Int.add x (List.map Int.ofNat xs) ≥ x ===>
                                        ∀ (x : Int) (xs : List Nat),
                                          x ≤ List.foldr Int.add x (List.map Int.ofNat xs)

def mapOptionDefault (x : Nat) (y : Option Nat) : Nat :=
 match y with
 | none => x
 | some a => a

#testOptimize [ "ConstClassCtorArg_2" ] ∀ (x : Nat) (xs : List Nat),
                                          List.map (mapOptionDefault x) (List.map Option.some xs) = xs ===>
                                        ∀ (x : Nat) (xs : List Nat),
                                          xs = List.map (λ (y : Option Nat) =>
                                                           mapOptionDefault.match_1
                                                           (λ (_ : Option Nat) => Nat)
                                                           y
                                                           (λ (_ : Unit) => x)
                                                           (λ (a : Nat) => a)
                                                         ) (List.map Option.some xs)

/-! Test cases to ensure that partially applied functions passed as arguments are properly handled. -/

-- ∀ (x : Bool) (xs : List Bool), x = true → List.all xs id → List.all (List.map (and x) xs) id ===>
-- ∀ (x : Bool) (xs : List Bool),
--   true = x →
--   true = List.all xs (λ (a : Bool) => a) →
--   true = List.all (List.map (and x) xs) (λ (a : Bool) => a)
#testOptimize [ "ConstPartialFunArg_1" ] ∀ (x : Bool) (xs : List Bool),
                                           x → List.all xs id → List.all (List.map (and x) xs) id ===>
                                         ∀ (x : Bool) (xs : List Bool),
                                           true = x →
                                           true = List.all xs (λ (a : Bool) => a) →
                                           true = List.all (List.map (and x) xs) (λ (a : Bool) => a)

-- ∀ (x : Nat) (xs : List Nat),
--    List.foldr Nat.add 0 (List.map (Nat.add x) xs) ≥ List.length xs * x ===>
-- ∀ (x : Nat) (xs : List Nat),
--    Nat.mul x (List.length xs) ≤ List.foldr Nat.add 0 (List.map (Nat.add x) xs)
#testOptimize [ "ConstPartialFunArg_2" ] (norm-nat-in-result: 1)
                                         ∀ (x : Nat) (xs : List Nat),
                                             List.foldr Nat.add 0 (List.map (Nat.add x) xs) ≥ List.length xs * x ===>
                                         ∀ (x : Nat) (xs : List Nat),
                                            Nat.mul x (List.length xs) ≤ List.foldr Nat.add 0 (List.map (Nat.add x) xs)

-- ∀ (c a : Bool) (xs : List Bool),
--     List.all xs id → a → List.all (List.map (ite c a) xs) id ===>
-- ∀ (c a : Bool) (xs : List Bool),
--     true = List.all xs (λ (b : Bool) => b) →
--     true = a →
--     true = List.all (List.map (ite (true = c) a) xs) (λ (b : Bool) => b)
#testOptimize [ "ConstPartialFunArg_3" ] ∀ (c a : Bool) (xs : List Bool),
                                             List.all xs id → a → List.all (List.map (ite c a) xs) id ===>
                                         ∀ (c a : Bool) (xs : List Bool),
                                             true = List.all xs (λ (b : Bool) => b) →
                                             true = a →
                                             true = List.all (List.map (ite (true = c) a) xs) (λ (b : Bool) => b)

end Test.NormHOF
