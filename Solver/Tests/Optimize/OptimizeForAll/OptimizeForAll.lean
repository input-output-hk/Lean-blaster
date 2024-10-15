import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeForAll
/-! ## Test objectives to validate normalization and simplification rules on `∀` and `→` -/

/-! Test cases for simplification rule `∀ (n : t), True ==> True`. -/

-- ∀ (c : Prop), True ===> True
#testOptimize [ "ForallTrue_1" ] ∀ (_a : Prop), True ===> True

-- ∀ (x : Int), True ===> True
#testOptimize [ "ForallTrue_2" ] ∀ (_x : Int), True ===> True

-- ∀ (α : Type) (x : List α), True ===> True
#testOptimize [ "ForallTrue_3" ] ∀ (α : Type) (_x : List α), True ===> True

-- ∀ (a : Bool), ! a || a ===> True
#testOptimize [ "ForallTrue_4" ] ∀ (a : Bool), !a || a ===> True

-- ∀ (a : Bool), (if a then true else !a) = true ===> True
#testOptimize [ "ForallTrue_5" ] ∀ (a : Bool), (if a then true else !a) = true ===> True

-- ∀ (a : Bool), if a then True else !a ===> True
-- NOTE: In this case, the `then` and `else` expressions are of type `Prop`.
#testOptimize [ "ForallTrue_6" ] ∀ (a : Bool), if a then True else !a ===> True

-- ∀ (a b c : Prop), ¬ (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) ===> True
#testOptimize [ "ForallTrue_7"] ∀ (a b c : Prop), ¬ (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) ===> True

-- let x := a && a
-- let y := a || !x
-- ∀ (a b : Bool), ((y || a) || b) ===> True
#testOptimize [ "ForallTrue_8" ] ∀ (a b : Bool), let x := a && a; let y := a || !x; ((y || a) || b) ===> True


/-! Test cases for simplification rule `e → True ==> True`. -/

-- ∀ (a : Prop), a → True ===> True
#testOptimize [ "ForallImpTrue_1" ] ∀ (a : Prop), a → True ===> True

-- ∀ (x : Int), x > 10 → True ===> True
#testOptimize [ "ForallImpTrue_2" ] ∀ (x : Int), x > 10 → True ===> True

-- ∀ (α : Type) (x : List α), List.length x > 10 ===> True
#testOptimize [ "ForallImpTrue_3" ] ∀ (α : Type) (x : List α), List.length x > 10 → True ===> True

-- ∀ (a : Prop) (b : Bool), a → (b || !b) ===> True
#testOptimize [ "ForallImpTrue_4" ] ∀ (a : Prop) (b : Bool), a → (b || !b) ===> True

-- ∀ (a b : Prop) (c : Bool), a ∧ b → (if c then true else !c) = true ===> True
#testOptimize [ "ForallImpTrue_5" ] ∀ (a b : Prop) (c : Bool), a ∧ b → (if c then true else !c) = true ===> True

-- ∀ (a b c : Prop), (a ∨ c) → ¬ ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ===> True
#testOptimize [ "ForallImpTrue_6"] ∀ (a b c : Prop), a ∨ c → ¬ ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ===> True

-- ∀ (a b : Prop), a → b → True ===> True
#testOptimize [ "ForallImpTrue_7" ] ∀ (a b : Prop), a → b → True ===> True

-- ∀ (a b c : Prop), a → b → c → True ===> True
#testOptimize [ "ForallImpTrue_8" ] ∀ (a b c : Prop), a → b → c → True ===> True


/-! Test cases to ensure that `∀ (n : t), False` will not be simplified to `False`. -/

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

-- ∀ (a : Bool) (b : Prop), if a then b ∧ ¬ b else False ===> False
#testOptimize [ "ForallFalse_6" ] ∀ (a : Bool) (b : Prop), if a then (b ∧ ¬ b) else False ===> False

-- ∀ (a b : Bool), if a then b && !b else False ===> False
#testOptimize [ "ForallFalse_7" ] ∀ (a b : Bool), if a then (b && !b) else False ===> False


-- ∀ (a b c : Prop), (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) ===> False
#testOptimize [ "ForallFalse_8"] ∀ (a b c : Prop), (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) ===> False

-- let x := a || a
-- let y := a && !x
-- ∀ (a b : Bool), ((y || !b) && b) ===> False
#testOptimize [ "ForallFalse_9" ] ∀ (a b : Bool), let x := a || a; let y := a && !x; ((y || !b) && b) ===> False

--- ∀ (a : Empty), False ===> ∀ (a : Empty), False
#testOptimize [ "ForallFalse_10" ] ∀ (_a : Empty), False ===> ∀ (_a : Empty), False


--- ∀ (a : Empty), False ===> ∀ (a : Empty), False
#testOptimize [ "ForallFalse_10" ] ∀ (_a : Empty), False ===> ∀ (_a : Empty), False



/-! Test cases for simplification rule `False → e ==> True`. -/

-- ∀ (a : Prop), False → a ===> True
#testOptimize [ "ForallFalseImp_1" ] ∀ (a : Prop), False → a ===> True

-- (¬ (¬ (¬ a))) = a → b ===> True
#testOptimize [ "ForallFalseImp_2" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = a → b ===> True

-- ∀ (a : Bool) (b : Prop), (!a && a) → b ===> True
#testOptimize [ "ForallFalseImp_3" ] ∀ (a : Bool) (b : Prop), (!a && a) → b ===> True

-- ∀ (a : Bool) (b p : Prop), (if a then b ∧ ¬ b else False) → p ===> True
#testOptimize [ "ForallFalseImp_4" ] ∀ (a : Bool) (b p : Prop), (if a then (b ∧ ¬ b) else False) → p ===> True

-- ∀ (a b c : Bool) (p : Prop), ( (if (!c && c) then a else b) = !b ) → p ===> True
#testOptimize [ "ForallFalseImp_5" ] ∀ (a b c : Bool) (p : Prop), ( (if (!c && c) then a else b) = !b ) → p ===> True

-- ∀ (a b c d : Prop), (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) → d ===> True
#testOptimize [ "ForallFalseImp_6"] ∀ (a b c d : Prop), (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) → d ===> True

-- let x := a && a in
-- let y := ! a && x in
-- (if y then p else q) ∧ ¬ q → p ===> True
#testOptimize [ "ForallFalseImp_7" ] ∀ (a : Bool) (p q : Prop),
                                       let x := a && a; let y := ! a && x;
                                       (if y then p else q) ∧ ¬ q → p ===> True

-- ∀ (a b : Prop) (h : (¬ (¬ (¬ a))) = a), b ===> True
#testOptimize [ "ForallFalseImp_8" ] ∀ (a b : Prop) (_h : (¬ (¬ (¬ a))) = a), b ===> True


-- ∀ (a b : Prop), False → a → b ===> True
#testOptimize [ "ForallFalseImp_9" ] ∀ (a b : Prop), False → a → b ===> True

-- ∀ (a b c : Prop), False → a → b → c ===> True
#testOptimize [ "ForallFalseImp_10" ] ∀ (a b c : Prop), False → a → b → c ===> True

-- ∀ (h : false), false ===> True
-- NOTE: This is a syntactic sugar for false = true → false = true
#testOptimize [ "ForallFalseImp_11" ] ∀ (_h : false), false ===> True

-- ∀ (h : false), true ===> True
#testOptimize [ "ForallFalseImp_12" ] ∀ (_h : false), true ===> True

-- ∀ (a : Prop) (h : false), a ===> True
#testOptimize [ "ForallFalseImp_13" ]  ∀ (a : Prop) (_h : false), a ===> True

-- ∀ (a : Bool) (h : false), a ===> True
#testOptimize [ "ForallFalseImp_14" ]  ∀ (a : Bool) (_h : false), a ===> True



/-! Test cases for simplification rule `True → e ==> e`. -/

-- ∀ (a : Prop), True → a ===> ∀ (a : Prop), a
#testOptimize [ "ForallTrueImp_1" ] ∀ (a : Prop), True → a ===> ∀ (a : Prop), a

-- ∀ (a b : Prop), (¬ (¬ a)) = a → b ===> ∀ (b : Prop), b
#testOptimize [ "ForallTrueImp_2" ] ∀ (a b : Prop), (¬ (¬ a)) = a → b ===> ∀ (b : Prop), b

-- ∀ (a : Bool) (b : Prop), (!a || a) → b ===> ∀ (b : Prop), b
#testOptimize [ "ForallTrueImp_3" ] ∀ (a : Bool) (b : Prop), (!a || a) → b ===>
                                    ∀ (b : Prop), b

-- ∀ (a : Bool) (b p : Prop), (if a then b ∨ ¬ b else True) → p ===> ∀ (p : Prop), p
#testOptimize [ "ForallTrueImp_4" ] ∀ (a : Bool) (b p : Prop), (if a then (b ∨ ¬ b) else True) → p ===>
                                    ∀ (p : Prop), p

-- ∀ (a b c : Bool) (p : Prop), (if (!c && c) then a else b) = b → p ===> ∀ (p : Prop), p
#testOptimize [ "ForallTrueImp_5" ] ∀ (a b c : Bool) (p : Prop), (if (!c && c) then a else b) = b → p ===>
                                    ∀ (p : Prop), p

-- ∀ (a b c d : Prop), ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬ a → d ===> ∀ (d : Prop), d
#testOptimize [ "ForallTrueImp_6"] ∀ (a b c d : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬ a → d ===>
                                   ∀ (d : Prop), d

-- let x := a && a in
-- let y := ! a && x in
-- (if y then p else q) ∨ ¬ q → p ===> p
#testOptimize [ "ForallTrueImp_7" ] ∀ (a : Bool) (p q : Prop),
                                       let x := a && a; let y := ! a && x;
                                       (if y then p else q) ∨ ¬ q → p ===>
                                    ∀ (p : Prop), p

-- ∀ (a b : Prop) (h: (¬ (¬ a)) = a), b ===> ∀ (b : Prop), b
#testOptimize [ "ForallTrueImp_8" ] ∀ (a b : Prop) (_h : (¬ (¬ a)) = a), b ===> ∀ (b : Prop), b


-- ∀ (a : Bool) (b : Prop), (b ∨ ¬ b) → (!a || a) → b ===> ∀ (b : Prop), b
#testOptimize [ "ForallTrueImp_9" ] ∀ (a : Bool) (b : Prop), (b ∨ ¬ b) → (!a || a) → b ===>
                                    ∀ (b : Prop), b


/-! Test cases for simplification rule `e1 → e2 ==> True (if p1 =ₚₜᵣ p2 ∧ Type(e1) = Prop)`. -/

-- ∀ (p : Prop), p → p ===> True
#testOptimize [ "ForallExact_1" ] ∀ (p : Prop), p → p ===> True

-- ∀ (p : Prop), p ∧ p → p ===> True
#testOptimize [ "ForallExact_2" ] ∀ (p : Prop), p ∧ p → p ===> True

-- ∀ (p : Prop), p ∨ p → p ===> True
#testOptimize [ "ForallExact_3" ] ∀ (p : Prop), p ∨ p → p ===> True

-- ∀ (p : Prop), ¬ (¬ p) → p ===> True
#testOptimize [ "ForallExact_4" ] ∀ (p : Prop), ¬ (¬ p) → p ===> True

-- ∀ (p : Prop), ¬ (¬ (¬ p)) → ¬ p ===> True
#testOptimize [ "ForallExact_5" ] ∀ (p : Prop), ¬ (¬ (¬ p)) → ¬ p ===> True

-- ∀ (a b : Bool), ¬ (a = (b && ! b)) → a ===> True
#testOptimize [ "ForallExact_6" ] ∀ (a b : Bool), ¬ (a = (b && !b)) → a ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool), (¬ y) → a ===> True
#testOptimize [ "ForallExact_7" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; (¬ y) → a ===> True

-- ∀ (a b : Bool), ¬ (a = (b || ! b)) → !a ===> True
#testOptimize [ "ForallExact_8" ] ∀ (a b : Bool), ¬ (a = (b || !b)) → !a ===> True

-- let x := a && a in
-- let y := a || x in
-- ∀ (a : Bool), ¬ y → !a ===> True
#testOptimize [ "ForallExact_9" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y → !a ===> True

-- ∀ (a b : Prop), ((b ∧ ¬ b) ∨ a) → a ===> True
#testOptimize [ "ForallExact_10" ] ∀ (a b : Prop), ((b ∧ ¬ b) ∨ a) → a ===> True

opaque a : Nat
opaque b : Nat
opaque c : Nat

-- [b + a, c] = [a + c, c] → [Nat.add a c, c] = [Nat.add b a, c] ===> True
#testOptimize [ "ForallExact_11" ] [b + a, c] = [a + c, c] → [Nat.add a c, c] = [Nat.add b a, c] ===> True

-- ∀ (a : Bool), not a → !a
#testOptimize [ "ForallExact_12" ] ∀ (a : Bool), not a → !a ===> True

-- ∀ (a : Bool), not (not a) → a
#testOptimize [ "ForallExact_13" ] ∀ (a : Bool), not (not a) → a ===> True

-- ∀ (a b : Bool), not a = not (not b) → b = not a ===> True
#testOptimize [ "ForallExact_14" ] ∀ (a b : Bool), not a = not (not b) → b = not a ===> True

-- ∀ (a b : Bool), not a = not (not (not b)) → a = b ===> True
#testOptimize [ "ForallExact_15" ] ∀ (a b : Bool), not a = not (not (not b)) → a = b ===> True

-- ∀ (a b : Bool), (¬ (¬ a)) = ¬ (¬ b) → a = b ===> True
#testOptimize [ "ForallExact_16" ] ∀ (a b : Prop), (¬ (¬ a)) = ¬ (¬ b) → a = b ===> True

-- ∀ (a b : Bool), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → a = b ===> True
#testOptimize [ "ForallExact_17" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → a = b ===> True

-- ((∀ (x : Int), x > 10)) → (∀ (x : Int), x > 10) ===> True
#testOptimize [ "ForallExact_18" ] (∀ (x : Int), x > 10) → (∀ (x : Int), x > 10) ===> True

-- ((∀ (x : Int), x > 10)) → (∀ (z : Int), z > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "ForallExact_19" ] (∀ (x : Int), x > 10) → (∀ (z : Int), z > 10) ===> True

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- ∀ (c p q : Bool) (a b : Prop), if c then x else y → (¬ (p = q) → a) ∧ ((p = q) → b) ==> True
#testOptimize [ "ForallExact_20" ] ∀ (c p q : Bool) (a b : Prop),
                                      let x := if ¬ (p = q) then a else b;
                                      let y := if (q = p) then b else a;
                                      (if c then x else y) → (¬ (p = q) → a) ∧ ((p = q) → b) ===> True

-- ∀ (c : Prop) (x y : Int), (if ¬ c then x else y) > x → (if c then y else x) > x ===> True
#testOptimize [ "ForallExact_21" ] ∀ (c : Prop) (x y : Int),
                                     [Decidable c] → (if ¬ c then x else y) > x → (if c then y else x) > x ===> True


-- ∀ (c a b : Bool), true = ( if c then a else b ) → ( (!c || a) && (c || b) ) ===> True
#testOptimize [ "ForallExact_22" ] ∀ (c a b : Bool), true = (if c then a else b) → ( (!c || a) && (c || b) ) ===> True


-- ∀ (c : Bool) (a b : Prop), (if c then a else b) → (!c → b) ∧ (c → a) ===> True (with Type(a) = Prop and Type(c) = Bool)
#testOptimize [ "ForallExact_23" ] ∀ (c : Bool) (a b : Prop), (if c then a else b) → (!c → b) ∧ (c → a) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool) (p q: Int), ((if y then p else q) > p) → ((if true = a then q else p) > p) ===> True
#testOptimize [ "ForallExact_24" ] ∀ (a : Bool) (p q: Int),
                                     let x := a || a; let y := ! a || ! x;
                                     ((if y then p else q ) > p) → ((if (true = a) then q else p) > p) ===> True

-- ∀ (p : Prop) (h : ¬ (¬ (¬ p))), ¬ p ===> True
#testOptimize [ "ForallExact_25" ] ∀ (p : Prop) (_h :  ¬ (¬ (¬ p))), ¬ p ===> True

-- ∀ (a b : Bool) (h : ¬ (a = (b && ! b))), a ===> True
#testOptimize [ "ForallExact_26" ] ∀ (a b : Bool) (_h : ¬ (a = (b && !b))), a ===> True

-- (∀ (y x : Int), x > y) → (∀ (x y: Int), x < y) ===> True
#testOptimize [ "ForallExact_27" ] (∀ (y x : Int), x > y) → (∀ (x y : Int), x < y) ===> True

-- ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (y z : Int), y > x ∧ z > y) ===> True
#testOptimize [ "ForallExact_28" ] ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (y z : Int), y > x ∧ z > y) ===> True

-- ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (y z : Int), x < y ∧ z > y) ===> True
#testOptimize [ "ForallExact_29" ] ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (y z : Int), x < y ∧ z > y) ===> True

-- ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (m n : Int), x < m ∧ n > m) ===> True
#testOptimize [ "ForallExact_30" ] ∀ (x : Int), (∃ (y z : Int), y > x ∧ z > y) → (∃ (m n : Int), x < m ∧ n > m) ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
    - `∀ (n : t), True ==> True`
    - `e → True ==> True`
    - `False → e ==> True`
    - `True → e ==> e`
    - `e1 → e2 ==> True (if p1 =ₚₜᵣ p2 ∧ Type(e1) = Prop)`
-/

-- ∀ (a : Prop), a ===> ∀ (a : Prop), a
#testOptimize [ "ForallUnchanged_1" ] ∀ (a : Prop), a ===> ∀ (a : Prop), a

-- ∀ (a b : Prop), a ∧ b  ===> ∀ (a : Prop), a ∧ b
#testOptimize [ "ForallUnchanged_2" ] ∀ (a b : Prop), a ∧ b  ===> ∀ (a b : Prop), a ∧ b

-- ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y
#testOptimize [ "ForallUnchanged_3" ] ∀ (x y : Int), x < y ===> ∀ (x y : Int), x < y

-- ∀ (α : Type) (x : List α) (n : Nat), List.length x < n ===> ∀ (α : Type) (x : List α) (n : Nat), List.length x < n
#testOptimize [ "ForallUnchanged_4" ] ∀ (α : Type) (x : List α) (n : Nat), List.length x < n ===>
                                      ∀ (α : Type) (x : List α) (n : Nat) , List.length x < n

-- let x := a || a
-- let y := a && !x
-- ∀ (a b : Bool), ((y || a) || b) ===> ∀ (a b : Bool), a || b
#testOptimize [ "ForallUnchanged_5" ] ∀ (a b : Bool), let x := a || a; let y := a && !x; ((y || a) || b) ===>
                                      ∀ (a b : Bool), true = (a || b)

-- ∀ (a b : Bool), if a then b else !a ===> ∀ (a b : Bool), true = (b || !a)
#testOptimize [ "ForallUnchanged_6" ] ∀ (a b : Bool), (if a then b else !a) = true ===>
                                      ∀ (a b : Bool), true = (b || !a)

-- ∀ (a b c : Bool), if a then b else !a ===> ∀ (a b c : Bool), true = ((b || c) && (!a || !c))
#testOptimize [ "ForallUnchanged_7" ] ∀ (a b c : Bool), (if c then !a else b) = true ===>
                                      ∀ (a b c : Bool), true = ((b || c) && (!a || !c))


-- ∀ (a b c : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ((b ∧ a) ∧ ¬(a ∧ b))) ===> ∀ (a : Prop), a
#testOptimize [ "ForallUnchanged_8"] ∀ (a b c : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ((b ∧ a) ∧ ¬(a ∧ b)) ===>
                                     ∀ (a : Prop), a


-- ∀ (a b : Prop), a → b ===> ∀ (a b : Prop), a → b
#testOptimize [ "ForallUnchanged_9" ] ∀ (a b : Prop), a → b ===> ∀ (a b : Prop), a → b


-- ∀ (a b c : Prop), a → b → c ===> ∀ (a b c : Prop), a → b → c
#testOptimize [ "ForallUnchanged_10" ] ∀ (a b c : Prop), a → b → c ===> ∀ (a b c : Prop), a → b → c


-- ∀ (x y z : Int), x > z → y > z ===> ∀ (x y : Int), z < x → y < z
#testOptimize [ "ForallUnchanged_11" ] ∀ (x y z : Int), x > z → y < z ===> ∀ (x y z : Int), z < x → y < z

-- ∀ (α : Type) (x y : List α) (n : Nat), List.length x < n → List.length y < n ===>
-- ∀ (α : Type) (x y : List α) (n : Nat), List.length x < n → List.length y < n
#testOptimize [ "ForallUnchanged_12" ] ∀ (α : Type) (x y : List α) (n : Nat), List.length x < n → List.length y < n ===>
                                       ∀ (α : Type) (x y : List α) (n : Nat), List.length x < n → List.length y < n

-- (¬ (¬ (¬ a))) = b → c ===> ∀ (a b c : Prop), b = ¬ a → c
#testOptimize [ "ForallUnchanged_13" ] ∀ (a b c : Prop), (¬ (¬ (¬ a))) = b → c ===>
                                       ∀ (a b c : Prop), b = ¬ a → c

-- ∀ (a b : Bool) (p : Prop), (!a && b) → p ===> ∀ (a b : Bool) (p : Prop), true = (b && !a) → p
#testOptimize [ "ForallUnchanged_14" ] ∀ (a b : Bool) (p : Prop), (!a && b) → p ===>
                                       ∀ (a b : Bool) (p : Prop), true = (b && !a) → p

-- ∀ (a : Bool) (b p : Prop), (if a then b else False) → p ===>
-- ∀ (a : Bool) (b p : Prop), (false = a → False) ∧ (true = a → b) → p
#testOptimize [ "ForallUnchanged_15" ] ∀ (a : Bool) (b p : Prop), (if a then b else False) → p ===>
                                       ∀ (a : Bool) (b p : Prop), (false = a → False) ∧ (true = a → b) → p

-- ∀ (a b c : Bool) (p : Prop), ( (if (!c && c) then a else c) = !b ) → p ===>
-- ∀ (b c : Bool) (p : Prop), c = !b → p
#testOptimize [ "ForallUnchanged_16" ] ∀ (a b c : Bool) (p : Prop), ( (if (!c && c) then a else c) = !b ) → p ===>
                                       ∀ (b c : Bool) (p : Prop), c = !b → p

-- ∀ (a b c p : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ (b ∨ c) → p ===>
-- ∀ (a b c p : Prop), a ∧ (b ∨ c) → p ===>
#testOptimize [ "ForallUnchanged_17"] ∀ (a b c p : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ (b ∨ c) → p ===>
                                      ∀ (a b c p : Prop), a ∧ (b ∨ c) → p
-- let x := a && a in
-- let y := ! a && x in
-- ∀ (a : Bool) (p q r : Prop), (if y then p else r) ∧ ¬ q → p ===>
-- ∀ (p q r : Prop), r ∧ ¬ q → p
#testOptimize [ "ForallUnchanged_18" ] ∀ (a : Bool) (p q r : Prop),
                                        let x := a && a; let y := ! a && x;
                                        (if y then p else r) ∧ ¬ q → p ===>
                                       ∀ (p q r : Prop), r ∧ ¬ q → p

-- ∀ (a b : Prop) (h : (¬ (¬ (¬ a))) = b), c ===>
-- ∀ (a b : Prop) (h : b = (¬ a)), c
#testOptimize [ "ForallUnchanged_19" ] ∀ (a b c : Prop) (_h : (¬ (¬ (¬ a))) = b), c ===>
                                       ∀ (a b c : Prop) (_h : b = (¬ a)), c

-- ∀ (a : Prop) (b : Bool), a → (b || b) ===> ∀ (a : Prop) (b : Bool), a → true = b
#testOptimize [ "ForallUnchanged_20" ] ∀ (a : Prop) (b : Bool), a → (b || b) ===>
                                       ∀ (a : Prop) (b : Bool), a → true = b

-- ∀ (a b : Prop) (c : Bool), a ∧ b → (if c then !c else c) = true ===>
-- ∀ (a b : Prop), a ∧ b → False
#testOptimize [ "ForallUnchanged_21" ] ∀ (a b : Prop) (c : Bool), a ∧ b → (if c then !c else c) = true ===>
                                       ∀ (a b : Prop), a ∧ b → False

-- ∀ (a b c : Prop), (a ∨ c) → ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬ a ===>
-- ∀ (a c : Prop), (a ∨ c) → False
#testOptimize [ "ForallUnchanged_22"] ∀ (a b c : Prop), a ∨ c → ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬ a) ===>
                                      ∀ (a c : Prop), (a ∨ c) → False


-- ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b ===>
-- ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b
#testOptimize [ "ForallUnchanged_23" ] ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b ===>
                                       ∀ (f : Prop → Prop) (a b : Prop), a = b → f a = f b

-- ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y ===>
-- ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y
-- NOTE: reordering applied on operands
#testOptimize [ "ForallUnchanged_24" ] ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y ===>
                                       ∀ (f : Int → Bool) (x y : Int), x = y → f x = f y


-- (∀ (x y : Int), x > y) → (∀ (y x : Int), x > y) ===>
-- (∀ (x y : Int), y < x) → (∀ (y x : Int), y < x)
-- NOTE: This is considered as unchanged for now until we have advanced simplification rules
#testOptimize [ "ForallUnchanged_25" ] (∀ (x y : Int), x > y) → (∀ (y x : Int), x > y) ===>
                                       (∀ (x y : Int), y < x) → (∀ (y x : Int), y < x)


/-! Test cases for simplification rule `¬ e → e ==> e`. -/

-- ∀ (p : Prop), ¬ p → p ===> ∀ (p : Prop), p
#testOptimize [ "ForallNegPropImp_1" ] ∀ (p : Prop), ¬ p → p ===> ∀ (p : Prop), p

-- ∀ (a b : Prop), ¬(a = b) → (¬ (¬ a)) = ¬ (¬ b) ===> a = b
#testOptimize [ "ForallNegPropImp_2" ] ∀ (a b : Prop), ¬ (a = b) → (¬ (¬ a)) = ¬ (¬ b) ===> ∀ (a b : Prop), a = b

-- ∀ (x y : Nat), ¬ x < y → y > x ==> ∀ (x y : Nat), x < y
#testOptimize [ "ForallNegPropImp_3" ] ∀ (x y : Nat), ¬ x < y → y > x ===> ∀ (x y : Nat), x < y

-- ∀ (a b: Bool), ¬ ((a || (b && b)) && (b || a)) → (a || b) ===> ∀ (a b: Bool), true = (a || b)
#testOptimize [ "ForallNegPropImp_4" ] ∀ (a b: Bool), ¬ ((a || (b && b)) && (b || a)) → (a || b) ===>
                                       ∀ (a b : Bool), true = (a || b)

-- ∀ (p : Prop), ¬ (¬ (¬ p)) → p ===> ∀ (p : Prop), p
#testOptimize [ "ForallNegPropImp_5" ] ∀ (p : Prop), ¬ (¬ (¬ p)) → p ===> ∀ (p : Prop), p

-- ∀ (a b : Prop), ¬ ((b ∧ ¬ b) ∨ a) → a ===> ∀ (a : Prop), a
#testOptimize [ "ForallNegPropImp_6" ] ∀ (a b : Prop), ¬ ((b ∧ ¬ b) ∨ a) → a ===> ∀ (a : Prop), a

-- ¬ ((∀ (x y : Int), x > y)) → (∀ (x y : Int), y < x) ===> ∀ (x y : Int), y < x
#testOptimize [ "ForallNegPropImp_7" ] ¬ ((∀ (x y : Int), x > y)) → (∀ (x y : Int), y < x) ===> ∀ (x y : Int), y < x

-- ¬ ((∀ (x y : Int), x > y)) → (∀ (x z : Int), z < x) ===> ∀ (x z : Int), z < x
#testOptimize [ "ForallNegPropImp_8" ] ¬ ((∀ (x y : Int), x > y)) → (∀ (x z : Int), z < x) ===> ∀ (x z : Int), z < x

-- ∀ (p : Prop) (h : ¬ (¬ (¬ p))), p ===> ∀ (p : Prop), p
#testOptimize [ "ForallNegPropImp_9" ] ∀ (p : Prop) (_h :  ¬ (¬ (¬ p))), p ===> ∀ (p : Prop), p

-- ∀ (a b : Bool) (h : ¬ (a = (b || ! b))), a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallNegPropImp_10" ] ∀ (a b : Bool) (_h : ¬ (a = (b || !b))), a ===> ∀ (a : Bool), true = a



/-! Test cases to ensure that simplification rule ``¬ e → e ==> e` is not wrongly applied. -/

-- ∀ (p q : Prop), ¬ p → q ===> ∀ (p : Prop), ¬ p → q
#testOptimize [ "ForallNegPropImpUnchanged_1" ] ∀ (p q : Prop), ¬ p → q ===> ∀ (p q : Prop), ¬ p → q

-- ∀ (a b : Prop), ¬(a = b) → (¬ (¬ a)) = ¬ b ===>
-- ∀ (a b : Prop), ¬(a = b) → a = ¬ b
#testOptimize [ "ForallNegPropImpUnchanged_2" ] ∀ (a b : Prop), ¬ (a = b) → (¬ (¬ a)) = ¬ b ===>
                                                ∀ (a b : Prop), ¬(a = b) → a = ¬ b

-- ∀ (x y z : Nat), ¬ x < y → y > z ==> ∀ (x y z : Nat), ¬ x < y → z < y
#testOptimize [ "ForallNegPropImpUnchanged_3" ] ∀ (x y z : Nat), ¬ x < y → y > z ===>
                                                ∀ (x y z : Nat), ¬ x < y → z < y

-- ∀ (a b c : Bool), ¬ ((a || (b && b)) && (b || a)) → (a || c) ===>
-- ∀ (a b c : Bool), false = (a || b) → true = (a || c)
#testOptimize [ "ForallNegPropImpUnchanged_4" ] ∀ (a b c : Bool), ¬ ((a || (b && b)) && (b || a)) → (a || c) ===>
                                                ∀ (a b c : Bool), false = (a || b) → true = (a || c)

-- ∀ (p q : Prop), ¬ (¬ (¬ p)) → q ===> ∀ (p q : Prop), ¬ p → q
#testOptimize [ "ForallNegPropImpUnchanged_5" ] ∀ (p q : Prop), ¬ (¬ (¬ p)) → q ===> ∀ (p q : Prop), ¬ p → q

-- ∀ (a b c : Prop), ¬ ((b ∧ ¬ b) ∨ a) → c ===> ∀ (a c : Prop), ¬ a → c
#testOptimize [ "ForallNegPropImpUnchanged_6" ] ∀ (a b c : Prop), ¬ ((b ∧ ¬ b) ∨ a) → c ===>
                                                ∀ (a c : Prop), ¬ a → c

-- ¬ ((∀ (x y : Int), x > y)) → (∀ (x y : Int), x < y) ===>
-- ¬ ((∀ (x y : Int), y < x)) → (∀ (x y : Int), x < y)
#testOptimize [ "ForallNegPropImpUnchanged_7" ] ¬ ((∀ (x y : Int), x > y)) → (∀ (x y : Int), x < y) ===>
                                                ¬ ((∀ (x y : Int), y < x)) → (∀ (x y : Int), x < y)

-- ¬ ((∀ (x y : Int), x > y)) → (∀ (x z : Int), x < z) ===>
-- ¬ ((∀ (x y : Int), y < x)) → (∀ (x z : Int), x < z)
#testOptimize [ "ForallNegPropImpUnchanged_8" ] ¬ ((∀ (x y : Int), x > y)) → (∀ (x z : Int), x < z) ===>
                                                ¬ ((∀ (x y : Int), y < x)) → (∀ (x z : Int), x < z)

-- ∀ (p q : Prop) (h : ¬ (¬ (¬ p))), q ===> ∀ (p q : Prop) (h : ¬ p) , q
#testOptimize [ "ForallNegPropImpUnchanged_9" ] ∀ (p q : Prop) (_h :  ¬ (¬ (¬ p))), q ===>
                                                ∀ (p q : Prop) (_h : ¬ p) , q

-- ∀ (a b c : Bool) (h : ¬ (a = (b || ! b))), c ===>
-- ∀ (a c : Bool) (h : false = a), true = c
#testOptimize [ "ForallNegPropImpUnchanged_10" ] ∀ (a b c : Bool) (_h : ¬ (a = (b || !b))), c ===>
                                                 ∀ (a c : Bool) (_h : false = a), true = c


/-! Test cases for simplification rule `e → ¬ e ==> ¬ e`. -/

-- ∀ (p : Prop), p → ¬ p ===> ¬ p
#testOptimize [ "ForallPropImpNeg_1" ] ∀ (p : Prop), p → ¬ p ===> ∀ (p : Prop), ¬ p

-- ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬(a = b) ===> ¬(a = b)
#testOptimize [ "ForallPropImpNeg_2" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬ (a = b) ===>
                                       ∀ (a b : Prop), ¬ (a = b)

-- ∀ (x y : Nat), y > x → ¬ x < y ==> ∀ (x y : Nat), ¬ x < y
#testOptimize [ "ForallPropImpNeg_3" ] ∀ (x y : Nat), y > x → ¬ x < y ===> ∀ (x y : Nat), ¬ x < y

-- ∀ (a b : Bool), (a || b) → ¬ ((a || (b && b)) && (b || a)) ===> ∀ (a b: Bool), ¬ (a || b) (i.e., false = (a || b))
#testOptimize [ "ForallPropImpNeg_4" ] ∀ (a b : Bool), (a || b) → ¬ ((a || (b && b)) && (b || a)) ===>
                                       ∀ (a b : Bool), false = (a || b)

-- ∀ (p : Prop), p → ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p
#testOptimize [ "ForallPropImpNeg_5" ] ∀ (p : Prop), p → ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p

-- ∀ (a b : Prop), a → ¬ ((b ∧ ¬ b) ∨ a) ===> ∀ (a : Prop), ¬ a
#testOptimize [ "ForallPropImpNeg_6" ] ∀ (a b : Prop), a → ¬ ((b ∧ ¬ b) ∨ a) ===> ∀ (a : Prop), ¬ a

-- (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x > y)) ===> ¬ (∀ (x y : Int), y < x)
-- TODO: Need to be update when implementing propagation of negation on forall
#testOptimize [ "ForallPropImpNeg_7" ] (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x > y)) ===> ¬ (∀ (x y : Int), y < x)

-- (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x > z)) ===> ¬ (∀ (x z : Int), z < x)
-- TODO: Need to be update when implementing propagation of negation on forall
#testOptimize [ "ForallPropImpNeg_8" ] (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x > z)) ===> ¬ (∀ (x z : Int), z < x)

-- ∀ (p : Prop) (h : ¬ (¬ p)), ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p
#testOptimize [ "ForallPropImpNeg_9" ] ∀ (p : Prop) (_h :  ¬ (¬ p)), ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p

-- ∀ (a b : Bool) (h : a), ¬ (a = (b || ! b)) ===> ∀ (a : Bool), ¬ a (i.e., false = a)
#testOptimize [ "ForallPropImpNeg_10" ] ∀ (a b : Bool) (_h : a), ¬ (a = (b || !b)) ===> ∀ (a : Bool), false = a


/-! Test cases to ensure that simplification rule `e → ¬ e ==> ¬ e` is not wrongly applied. -/

-- ∀ (p q : Prop), p → ¬ q ===> ∀ (p q : Prop), p → ¬ q
#testOptimize [ "ForallPropImpNegUnchanged_1" ] ∀ (p q : Prop), p → ¬ q ===> ∀ (p q : Prop), p → ¬ q

-- ∀ (a b c : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬(a = c) ===>
-- ∀ (a b c : Prop), a = b → ¬(a = c)
#testOptimize [ "ForallPropImpNegUnchanged_2" ] ∀ (a b c : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) → ¬ (a = c) ===>
                                                ∀ (a b c : Prop), a = b → ¬(a = c)

-- ∀ (x y z : Nat), y > x → ¬ x < z ==> ∀ (x y z : Nat), x < y → ¬ x < z
#testOptimize [ "ForallPropImpNegUnchanged_3" ] ∀ (x y z : Nat), y > x → ¬ x < z ===>
                                                ∀ (x y z : Nat), x < y → ¬ x < z

-- ∀ (a b c : Bool), (a || c) → ¬ ((a || (b && b)) && (b || a)) ===>
-- ∀ (a b c : Bool), true = (a || c) → false = (a || b)
#testOptimize [ "ForallPropImpNegUnchanged_4" ] ∀ (a b c : Bool), (a || c) → ¬ ((a || (b && b)) && (b || a)) ===>
                                                ∀ (a b c : Bool), true = (a || c) → false = (a || b)

-- ∀ (p q : Prop), p → ¬ (¬ (¬ q)) ===> ∀ (p q : Prop), p → ¬ q
#testOptimize [ "ForallPropImpNegUnchanged_5" ] ∀ (p q : Prop), p → ¬ (¬ (¬ q)) ===> ∀ (p q : Prop), p → ¬ q

-- ∀ (a b c : Prop), a → ¬ ((b ∧ ¬ b) ∨ c) ===> ∀ (a c : Prop), a → ¬ c
#testOptimize [ "ForallPropImpNegUnchanged_6" ] ∀ (a b c : Prop), a → ¬ ((b ∧ ¬ b) ∨ c) ===>
                                                ∀ (a c : Prop), a → ¬ c

-- (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x < y)) ===>
-- (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x < y))
-- TODO: Need to be update when implementing propagation of negation on forall
#testOptimize [ "ForallPropImpNegUnchanged_7" ] (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x < y)) ===>
                                                (∀ (x y : Int), y < x) → ¬ ((∀ (x y : Int), x < y))

-- (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x < z)) ===>
-- (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x < z))
-- TODO: Need to be update when implementing propagation of negation on forall
#testOptimize [ "ForallPropImpNegUnchanged_8" ] (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x < z)) ===>
                                                (∀ (x y : Int), y < x) → ¬ ((∀ (x z : Int), x < z))

-- ∀ (p q : Prop) (h : ¬ (¬ p)), ¬ (¬ (¬ q)) ===> ∀ (p q : Prop) (h : p), ¬ q
#testOptimize [ "ForallPropImpNegUnchanged_9" ] ∀ (p q : Prop) (_h :  ¬ (¬ p)), ¬ (¬ (¬ q)) ===>
                                                ∀ (p q : Prop) (_h : p), ¬ q

-- ∀ (a b c : Bool) (h : a), ¬ (c = (b || ! b)) ===>
-- ∀ (a c : Bool) (h : true = a), false = c
#testOptimize [ "ForallPropImpNegUnchanged_10" ] ∀ (a b c : Bool) (_h : a), ¬ (c = (b || !b)) ===>
                                                 ∀ (a c : Bool) (_h : true = a), false = c



/-! Test cases for simplification rule `true = c → false = c ==> false = c`. -/

-- ∀ (a : Bool), true = a → false = a ===> ∀ (a : Bool), false = a
#testOptimize [ "ForallBoolImpNeg_1" ] ∀ (a : Bool), true = a → false = a ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), a → !a ===> ∀ (a : Bool), false = a
#testOptimize [ "ForallBoolImpNeg_2" ] ∀ (a : Bool), a → !a ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), a → ! (! !a) ===> ∀ (a : Bool), false = a
#testOptimize [ "ForallBoolImpNeg_3" ] ∀ (a : Bool), a → ! (! (!a)) ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), ! (! a) → ! (! !a) ===> ∀ (a : Bool), false = a
#testOptimize [ "ForallBoolImpNeg_4" ] ∀ (a : Bool), ! ! (a) → ! (! (!a)) ===> ∀ (a : Bool), false = a

-- ∀ (a b : Bool), (a && b) → ¬ (a && (a || !a) && b) ===> ∀ (a b : Bool), false = (a && b)
#testOptimize [ "ForallBoolImpNeg_5" ] ∀ (a b : Bool), (a && b) → ¬ (a && (a || !a) && b) ===>
                                       ∀ (a b : Bool), false = (a && b)

-- ∀ (a b : Bool), (a && (a || !a) && b) → ¬ (a && b) ===> ∀ (a b : Bool), false = (a && b)
#testOptimize [ "ForallBoolImpNeg_6" ] ∀ (a b : Bool), (a && (a || !a) && b) → ¬ (a && b) ===>
                                       ∀ (a b : Bool), false = (a && b)

-- ∀ (a b : Bool), (if a then b else true) = true → ¬ (! a || b) ===> ∀ (a b : Bool), false = (b || !a)
#testOptimize [ "ForallBoolImpNeg_7" ] ∀ (a b : Bool), (if a then b else true) = true → ¬ (! a || b) ===>
                                       ∀ (a b : Bool), false = (b || !a)

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a b : Bool), (¬ y) → !a ===> ∀ (a : Bool), false = a
#testOptimize [ "ForallBoolImpNeg_8" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; ¬ y → !a ===>
                                       ∀ (a : Bool), false = a

-- ∀ (a b : Bool) (h : a && (a || !a) && b), ¬ (a && b) ===> ∀ (a b : Bool), false = (a && b)
#testOptimize [ "ForallBoolImpNeg_9" ] ∀ (a b : Bool) (_h : a && (a || !a) && b), ¬ (a && b) ===>
                                       ∀ (a b : Bool), false = (a && b)


/-! Test cases to ensure that simplification rule `true = c → false = c ==> false = c` is not wrongly applied. -/

-- ∀ (a b : Bool), true = a → false = b ===> ∀ (a b : Bool), true = a → false = b
#testOptimize [ "ForallBoolImpNegUnchanged_1" ] ∀ (a b : Bool), true = a → false = b ===>
                                                ∀ (a b : Bool), true = a → false = b

-- ∀ (a b : Bool), a → !b ===> ∀ (a b : Bool), true = a → false = b
#testOptimize [ "ForallBoolImpNegUnchanged_2" ] ∀ (a b : Bool), a → !b ===>
                                                ∀ (a b : Bool), true = a → false = b

-- ∀ (a b : Bool), a → ! (! !b) ===> ∀ (a b : Bool), true = a → false = b
#testOptimize [ "ForallBoolImpNegUnchanged_3" ] ∀ (a b : Bool), a → ! (! (!b)) ===>
                                                ∀ (a b : Bool), true = a → false = b

-- ∀ (a b : Bool), ! (! b) → ! (! !a) ===> ∀ (a b : Bool), true = b → false = a
#testOptimize [ "ForallBoolImpNegUnchanged_4" ] ∀ (a b : Bool), ! ! (b) → ! (! (!a)) ===>
                                                ∀ (a b : Bool), true = b → false = a

-- ∀ (a b c : Bool), (a && b) → ¬ (a && (a || !a) && c) ===>
-- ∀ (a b c : Bool), true = (a && b) → false = (a && c)
#testOptimize [ "ForallBoolImpNegUnchanged_5" ] ∀ (a b c : Bool), (a && b) → ¬ (a && (a || !a) && c) ===>
                                                ∀ (a b c : Bool), true = (a && b) → false = (a && c)

-- ∀ (a b c : Bool), (a && (a || !a) && c) → ¬ (a && b) ===>
-- ∀ (a b c : Bool), true = (a && c) → false = (a && b)
#testOptimize [ "ForallBoolImpNegUnchanged_6" ] ∀ (a b c : Bool), (a && (a || !a) && c) → ¬ (a && b) ===>
                                                ∀ (a b c : Bool), true = (a && c) → false = (a && b)

-- ∀ (a b c : Bool), (if a then c else true) = true → ¬ (! a || b) ===>
-- ∀ (a b c : Bool), true = (c || !a) → false = (b || !a)
#testOptimize [ "ForallBoolImpNegUnchanged_7" ] ∀ (a b c : Bool), (if a then c else true) = true → ¬ (! a || b) ===>
                                                ∀ (a b c : Bool), true = (c || !a) → false = (b || !a)

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a b : Bool), (¬ y) → !b ===> ∀ (a b : Bool), true = a → false = b
#testOptimize [ "ForallBoolImpNegUnchanged_8" ] ∀ (a b : Bool), let x := a || a; let y := !a || !x; ¬ y → !b ===>
                                                ∀ (a b : Bool), true = a → false = b

-- ∀ (a b c : Bool) (h : a && (a || !a) && c), ¬ (a && b) ===>
-- ∀ (a b c : Bool) (h : true = (a && c)), false = (a && b)
#testOptimize [ "ForallBoolImpNegUnchanged_9" ] ∀ (a b c : Bool) (_h : a && (a || !a) && c), ¬ (a && b) ===>
                                                ∀ (a b c : Bool) (_h : true = (a && c)), false = (a && b)


/-! Test cases for simplification rule `false = c → true = c ==> true = c`. -/

-- ∀ (a : Bool), false = a → true = a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallBoolNegImp_1" ] ∀ (a : Bool), false = a → true = a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), !a → a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallBoolNegImp_2" ] ∀ (a : Bool), !a → a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), ! (! !a) → a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallBoolNegImp_3" ] ∀ (a : Bool), ! (! (!a)) → a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), ! (! !a) → ! (! a) ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallBoolNegImp_4" ] ∀ (a : Bool), ! (! (!a)) → ! ! (a) ===> ∀ (a : Bool), true = a

-- ∀ (a b : Bool), ¬ (a && b) → (a && (a || !a) && b) ===> ∀ (a b : Bool), true = (a && b)
#testOptimize [ "ForallBoolNegImp_5" ] ∀ (a b : Bool), ¬ (a && b) → (a && (a || !a) && b) ===>
                                       ∀ (a b : Bool), true = (a && b)

-- ∀ (a b : Bool), ¬ (a && (a || !a) && b) → (a && b) ===> ∀ (a b : Bool), true = (a && b)
#testOptimize [ "ForallBoolNegImp_6" ] ∀ (a b : Bool), ¬ (a && (a || !a) && b) → (a && b) ===>
                                       ∀ (a b : Bool), true = (a && b)

-- ∀ (a b : Bool), (if a then b else true) = false → (! a || b) ===> ∀ (a b : Bool), true = (b || !a)
#testOptimize [ "ForallBoolNegImp_7" ] ∀ (a b : Bool), (if a then b else true) = false → (! a || b) ===>
                                       ∀ (a b : Bool), true = (b || !a)

-- let x := a && a in
-- let y := a || x in
-- ∀ (a : Bool), ¬ y → a ===> ∀ (a : Bool), true = a
#testOptimize [ "ForallBoolNegImp_8" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y → a ===>
                                       ∀ (a : Bool), true = a

-- ∀ (a b : Bool) (h : ¬ (a && (a || !a) && b)), (a && b) ===> ∀ (a b : Bool), true = (a && b)
#testOptimize [ "ForallBoolNegImp_9" ] ∀ (a b : Bool) (_h : ¬ (a && (a || !a) && b)), (a && b) ===>
                                       ∀ (a b: Bool), true = (a && b)


/-! Test cases to ensure that simplification rule `false = c → true = c ==> true = c` is not wrongly applied. -/

-- ∀ (a b : Bool), false = a → true = b ===> ∀ (a b : Bool), false = a → true = b
#testOptimize [ "ForallBoolNegImpUnchanged_1" ] ∀ (a b : Bool), false = a → true = b ===>
                                                ∀ (a b : Bool), false = a → true = b

-- ∀ (a b : Bool), !b → a ===> ∀ (a b : Bool), false = b → true = a
#testOptimize [ "ForallBoolNegImpUnchanged_2" ] ∀ (a b : Bool), !b → a ===>
                                                ∀ (a b : Bool), false = b → true = a

-- ∀ (a b : Bool), ! (! !a) → b ===> ∀ (a b : Bool), false = a → true = b
#testOptimize [ "ForallBoolNegImpUnchanged_3" ] ∀ (a b : Bool), ! (! (!a)) → b ===>
                                                ∀ (a b : Bool), false = a → true = b

-- ∀ (a b : Bool), ! (! !b) → ! (! a) ===> ∀ (a b : Bool), false = b → true = a
#testOptimize [ "ForallBoolNegImpUnchanged_4" ] ∀ (a b : Bool), ! (! (!b)) → ! ! (a) ===>
                                                ∀ (a b : Bool), false = b → true = a

-- ∀ (a b c : Bool), ¬ (a && b) → (a && (a || !a) && c) ===>
-- ∀ (a b c : Bool), false = (a && b) → true = (a && c)
#testOptimize [ "ForallBoolNegImpUnchanged_5" ] ∀ (a b c : Bool), ¬ (a && b) → (a && (a || !a) && c) ===>
                                                ∀ (a b c : Bool), false = (a && b) → true = (a && c)

-- ∀ (a b c : Bool), ¬ (a && (a || !a) && c) → (a && b) ===>
-- ∀ (a b c : Bool), false = (a && c) → true = (a && b)
#testOptimize [ "ForallBoolNegImpUnchanged_6" ] ∀ (a b c : Bool), ¬ (a && (a || !a) && c) → (a && b) ===>
                                                ∀ (a b c : Bool), false = (a && c) → true = (a && b)

-- ∀ (a b c : Bool), (if a then c else true) = false → (! a || b) ===>
-- ∀ (a b c : Bool), false = (c || !a) → true = (b || !a)
#testOptimize [ "ForallBoolNegImpUnchanged_7" ] ∀ (a b c : Bool), (if a then c else true) = false → (! a || b) ===>
                                                ∀ (a b c : Bool), false = (c || !a) → true = (b || !a)

-- let x := a && a in
-- let y := a || x in
-- ∀ (a b : Bool), ¬ y → b ===> ∀ (a b : Bool), false = a → true = b
#testOptimize [ "ForallBoolNegImpUnchanged_8" ] ∀ (a b : Bool), let x := a && a; let y := a || x; ¬ y → b ===>
                                                ∀ (a b : Bool), false = a → true = b

-- ∀ (a b c : Bool) (h : ¬ (a && (a || !a) && b)), (a && c) ===>
-- ∀ (a b c : Bool) (h : false = (a && b)), true = (a && c)
#testOptimize [ "ForallBoolNegImpUnchanged_9" ] ∀ (a b c : Bool) (_h : ¬ (a && (a || !a) && b)), (a && c) ===>
                                                ∀ (a b c : Bool) (_h : false = (a && b)), true = (a && c)

end Test.OptimizeForAll
