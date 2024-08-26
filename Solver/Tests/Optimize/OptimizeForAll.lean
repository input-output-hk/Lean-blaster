import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeForAll
/-! ## Test objectives to validate normalization and simplification rules on `∀` and `→` -/

-- ∀ (c : Prop), True ===> True
#testOptimize [ "ForallTrue_1" ] ∀ (_c : Prop), True ===> True

-- ∀ (x : Int), True ===> True
#testOptimize [ "ForallTrue_2" ] ∀ (_x : Int), True ===> True

-- ∀ (α : Type) (x : List α), True ===> True
#testOptimize [ "ForallTrue_3" ] ∀ (α : Type) (_x : List α), True ===> True

-- ∀ (a : Bool), ! a || a ===> True
#testOptimize [ "ForallTrue_4" ] ∀ (a : Bool), !a || a ===> True

-- ∀ (a : Bool), (if a then true else !a) = true ===> True
#testOptimize [ "ForallTrue_5" ] ∀ (a : Bool), (if a then true else !a) = true ===> True

-- ∀ (a : Bool), if a then True else !a ===> True
#testOptimize [ "ForallTrue_6" ] ∀ (a : Bool), if a then True else !a ===> True


-- ∀ (c : Prop), False ===> False
#testOptimize [ "ForallFalse_1" ] ∀ (_c : Prop), False ===> False

-- ∀ (x : Int), False ===> False
#testOptimize [ "ForallFalse_2" ] ∀ (_x : Int), False ===> False

-- ∀ (α : Type) (x : List α), False ===> False
#testOptimize [ "ForallFalse_3" ] ∀ (α : Type) (_x : List α), True ===> True

-- ∀ (a : Bool), ! a && a ===> False
#testOptimize [ "ForallFalse_4" ] ∀ (a : Bool), !a && a ===> False

-- ∀ (a : Bool), (if a then !a else false) = true ===> False
#testOptimize [ "ForallFalse_5" ] ∀ (a : Bool), (if a then !a else false) = true ===> False

-- ∀ (a : Bool), if a then !a else False ===> False
#testOptimize [ "ForallFalse_6" ] ∀ (a : Bool), if a then !a else False ===> False


-- False → c ===> True
#testOptimize [ "ForallFalseImp_1" ] ∀ (c : Prop), False → c ===> True

-- ¬ (¬ (¬ a)) = a → b ===> True
#testOptimize [ "ForallFalseImp_2" ] ∀ (a b : Prop), ¬ (¬ (¬ a)) = a → b ===> True

-- (if (!c && c) then a else b) = !b → p ===> True
#testOptimize [ "ForallFalseImp_3" ] ∀ (a b c : Bool) (p : Prop), (if (!c && c) then a else b) = !b → p ===> True

-- let x := a && a in
-- let y := ! a && x in
-- (if y then p else q) ∧ ¬ q → p ===> True
#testOptimize [ "ForallFalseImp_4" ] ∀ (a : Bool) (p q : Prop),
                                       let x := a && a; let y := ! a && x;
                                       (if y then p else q) ∧ ¬ q → p ===> True

-- ∀ (a b : Prop) (h : ¬ (¬ (¬ a)) = a), b ===> True
#testOptimize [ "ForallFalseImp_5" ] ∀ (a b : Prop) (_h : ¬ (¬ (¬ a)) = a), b ===> True


-- True → c ===> c
#testOptimize [ "ForallTrueImp_1" ] ∀ (c : Prop), True → c ===> ∀ (c : Prop), c

-- (¬ (¬ a)) = a → b ===> b
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "ForallTrueImp_2" ] ∀ (a b : Prop), (¬ (¬ a)) = a → b ===> ∀ (_a b : Prop), b


-- (if (!c && c) then a else b) = b → p ===> p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "ForallTrueImp_3" ] ∀ (a b c : Bool) (p : Prop), (if (!c && c) then a else b) = b → p ===>
                                    ∀ (_a _b _c : Bool) (p : Prop), p

-- let x := a && a in
-- let y := ! a && x in
-- (if y then p else q) ∨ ¬ q → p ===> p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "ForallTrueImp_4" ] ∀ (a : Bool) (p q : Prop),
                                       let x := a && a; let y := ! a && x;
                                       (if y then p else q) ∨ ¬ q → p ===>
                                    ∀ (_a : Bool) (p _q : Prop), p

-- ∀ (a b : Prop) (h: (¬ (¬ a)) = a), b ===> ∀ (a b: Prop), b
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "ForallTrueImp_5" ] ∀ (a b : Prop) (_h : (¬ (¬ a)) = a), b ===> ∀ (_a b : Prop), b

-- p → p ===> True
#testOptimize [ "ForallExact_1" ] ∀ (p : Prop), p → p ===> True

-- p ∧ p → p ===> True
#testOptimize [ "ForallExact_2" ] ∀ (p : Prop), p ∧ p → p ===> True

-- p ∨ p → p ===> True
#testOptimize [ "ForallExact_3" ] ∀ (p : Prop), p ∨ p → p ===> True

-- ¬ (¬ p) → p ===> True
#testOptimize [ "ForallExact_4" ] ∀ (p : Prop), ¬ (¬ p) → p ===> True

-- ¬ (¬ (¬ p)) → ¬ p ===> True
#testOptimize [ "ForallExact_5" ] ∀ (p : Prop), ¬ (¬ (¬ p)) → ¬ p ===> True

-- ¬ (a = (b && ! b)) → a ===> True
#testOptimize [ "ForallExact_6" ] ∀ (a b : Bool), ¬ (a = (b && !b)) → a ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- (¬ y) → a ===> True
#testOptimize [ "ForallExact_7" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; (¬ y) → a ===> True

-- ¬ (a = (b || ! b)) → !a ===> True
#testOptimize [ "ForallExact_8" ] ∀ (a b : Bool), ¬ (a = (b || !b)) → !a ===> True

-- let x := a && a in
-- let y := a || x in
-- ¬ y → !a ===> True
#testOptimize [ "ForallExact_9" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y → !a ===> True

-- ((b ∧ ¬ b) ∨ a) → a ===> True
#testOptimize [ "ForallExact_10" ] ∀ (a b : Prop), ((b ∧ ¬ b) ∨ a) → a ===> True

opaque a : Nat
opaque b : Nat
opaque c : Nat

-- [b + a, c] = [a + c, c] → [Nat.add a c, c] = [Nat.add b a, c] ===> True
#testOptimize [ "ForallExact_11" ] [b + a, c] = [a + c, c] → [Nat.add a c, c] = [Nat.add b a, c] ===> True

-- not a → !a
#testOptimize [ "ForallExact_12" ] ∀ (a : Bool), not a → !a ===> True

-- not (not a) → a
#testOptimize [ "ForallExact_13" ] ∀ (a : Bool), not (not a) → a ===> True

-- not a = not (not b) → b = not a ===> True
#testOptimize [ "ForallExact_14" ] ∀ (a b : Bool), not a = not (not b) → b = not a ===> True

-- not a = not (not (not b)) → a = b ===> True
#testOptimize [ "ForallExact_15" ] ∀ (a b : Bool), not a = not (not (not b)) → a = b ===> True

-- (¬ (¬ a)) = ¬ (¬ b) → a = b ===> True
#testOptimize [ "ForallExact_16" ] ∀ (a b : Prop), (¬ (¬ a)) = ¬ (¬ b) → a = b ===> True

-- (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → a = b ===> True
#testOptimize [ "ForallExact_17" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → a = b ===> True

-- ((∀ (x : Int), x > 10)) → (∀ (x : Int), x > 10) ===> True
#testOptimize [ "ForallExact_18" ] (∀ (x : Int), x > 10) → (∀ (x : Int), x > 10) ===> True

-- ((∀ (x : Int), x > 10)) → (∀ (z : Int), z > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "ForallExact_19" ] (∀ (x : Int), x > 10) → (∀ (z : Int), z > 10) ===> True

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- if c then x else y → (¬ (p = q) → a) ∧ ((p = q) → b) ==> True
#testOptimize [ "ForallExact_20" ] ∀ (c p q : Bool) (a b : Prop),
                                      let x := if ¬ (p = q) then a else b;
                                      let y := if (q = p) then b else a;
                                      (if c then x else y) → (¬ (p = q) → a) ∧ ((p = q) → b) ===> True

-- (if ¬ c then x else y) > x → (if c then y else x) > x ===> True
#testOptimize [ "ForallExact_21" ] ∀ (c : Prop) (x y : Int),
                                     [Decidable c] → (if ¬ c then x else y) > x → (if c then y else x) > x ===> True


-- true = ( if c then a else b ) → ( (!c || a) && (c || b) ) ===> True
#testOptimize [ "ForallExact_22" ] ∀ (c a b : Bool), true = (if c then a else b) → ( (!c || a) && (c || b) ) ===> True


-- (if c then a else b) → (!c → b) ∧ (c → a) ===> True (with Type(a) = Prop and Type(c) = Bool)
#testOptimize [ "ForallExact_23" ] ∀ (c : Bool) (a b : Prop), (if c then a else b) → (!c → b) ∧ (c → a) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ((if y then p else q) > p) → ((if true = a then q else p) > p) ===> True
#testOptimize [ "ForallExact_24" ] ∀ (a : Bool) (p q: Int),
                                     let x := a || a; let y := ! a || ! x;
                                     ((if y then p else q ) > p) → ((if (true = a) then q else p) > p) ===> True

-- ∀ (p : Prop) (h : ¬ (¬ (¬ p))), ¬ p ===> True
#testOptimize [ "ForallExact_25" ] ∀ (p : Prop) (_h :  ¬ (¬ (¬ p))), ¬ p ===> True

-- ∀ (a b : Bool) (h : ¬ (a = (b && ! b))), a ===> True
#testOptimize [ "ForallExact_26" ] ∀ (a b : Bool) (_h : ¬ (a = (b && !b))), a ===> True


-- ¬ p → p ===> p
#testOptimize [ "ForallNegPropImp_1" ] ∀ (p : Prop), ¬ p → p ===> ∀ (p : Prop), p

-- p → ¬ p ===> ¬ p
#testOptimize [ "ForallNegPropImp_2" ] ∀ (p : Prop), p → ¬ p ===> ∀ (p : Prop), ¬ p


-- ¬(a = b) → (¬ (¬ a)) = ¬ (¬ b) ===> a = b
#testOptimize [ "ForallNegPropImp_3" ] ∀ (a b : Prop), ¬ (a = b) → (¬ (¬ a)) = ¬ (¬ b) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬(a = b) ===> ¬(a = b)
#testOptimize [ "ForallNegPropImp_4" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬ (a = b) ===>
                                       ∀ (a b : Prop), ¬ (a = b)

-- ∀ (a b : Prop) (h : (¬ (¬ (¬ a))) = ¬ (¬ (¬ b))), ¬(a = b) ===> ∀ (a b : Prop), ¬(a = b)
#testOptimize [ "ForallNegPropImp_5" ] ∀ (a b : Prop) (_h : (¬ (¬ (¬ a))) = ¬ (¬ (¬ b))), ¬ (a = b) ===>
                                       ∀ (a b : Prop), ¬ (a = b)

-- a → !a ===> false = a (with Type(a) = Bool)
#testOptimize [ "ForallNegBoolImp_1" ] ∀ (a : Bool), a → !a ===> ∀ (a : Bool), false = a

-- !a → a ===> true = a (with Type(a) = Bool)
#testOptimize [ "ForallNegBoolImp_2" ] ∀ (a : Bool), !a → a ===> ∀ (a : Bool), true = a

-- let x := a && a in
-- let y := a || x in
-- ¬ y → a ===> true = a
#testOptimize [ "ForallNegBoolImp_3" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y → a ===>
                                       ∀ (a : Bool), true = a

-- let x := a || a in
-- let y := ! a || ! x in
-- (¬ y) → !a ===> false = a
#testOptimize [ "ForallNegBoolImp_4" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; ¬ y → !a ===>
                                       ∀ (a : Bool), false = a

-- let x := a && a in
-- let y := a || x in
-- ∀ (a : Bool) (h : ¬ (a || (a && a))), a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallNegBoolImp_5" ] ∀ (a : Bool) (_h : ¬ (a || (a && a))), a ===>
                                       ∀ (a : Bool), true = a

-- ∀ (p q : Prop), p → q ===> ∀ (p q : Prop), p → q
#testOptimize [ "ForallUnchanged_1" ] ∀ (p q : Prop), p → q ===> ∀ (p q : Prop), p → q


-- ∀ (p q r : Prop), p ∧ q → r ===> ∀ (p q r : Prop), p ∧ q → r
#testOptimize [ "ForallUnchanged_2" ] ∀ (p q r : Prop), p ∧ q → r ===> ∀ (p q r : Prop), p ∧ q → r


-- ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b ===> ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b
-- NOTE: reordering applied on operands
#testOptimize [ "ForallUnchanged_3" ] ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b ===>
                                      ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b


-- ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y ===> ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y
-- NOTE: reordering applied on operands
#testOptimize [ "ForallUnchanged_4" ] ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y ===>
                                      ∀ (f : Int → Bool) (x y : Int), x = y → f y = f x


end Test.OptimizeForAll
