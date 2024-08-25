import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeITE
/-! ## Test objectives to validate normalization and simplification rules on `ite` -/

-- if c then a else a ===> a (with Type(c) = Bool)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteAbsorption_1" ] ∀ (c : Bool) (a : Prop), if c then a else a ===> ∀ (_c : Bool) (a : Prop), a

-- if c then a else a ===> a (with Type(c) = Prop)
-- TODO: remove unused quantifier and constraint when COI performed on forall
#testOptimize [ "IteAbsorption_2" ] ∀ (c a : Prop), [Decidable c] → if c then a else a ===> ∀ (c a : Prop), [Decidable c] → a

-- if c then a ∧ b else b ∧ a ===> a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteAbsorption_3" ] ∀ (c : Bool) (a b : Prop), if c then a ∧ b else b ∧ a ===> ∀ (_c : Bool) (a b : Prop), a ∧ b

-- if c then ¬ (¬ a) else a ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteAbsorption_4" ] ∀ (c : Bool) (a : Prop), if c then ¬ (¬ a) else a ===> ∀ (_c : Bool) (a : Prop), a

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- if c then x else y ===> a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteAbsorption_5" ] ∀ (c : Bool) (a b : Prop), let x := a ∧ b; let y := (¬ (¬ a)) ∧ b; if c then x else y ===>
                                    ∀ (_c : Bool) (a b : Prop), a ∧ b

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- if c then x else y ===> (¬ (p = q) → a) ∧ ((p = q) → b)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteAbsorption_6" ] ∀ (c p q : Bool) (a b : Prop),
                                      let x := if ¬ (p = q) then a else b;
                                      let y := if (q = p) then b else a;
                                      if c then x else y ===>
                                    ∀ (_c p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)

-- if True then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteTrueCond_1" ] ∀ (a b : Prop), if True then a else b ===> ∀ (a _b : Prop), a


-- if (! c || c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteTrueCond_2" ] ∀ (c : Bool) (a b : Prop), if (! c) || c then a else b ===> ∀ (_c : Bool) (a _b : Prop), a

-- if (¬ c ∨ c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteTrueCond_3" ] ∀ (c a b : Prop), [Decidable c] → if (¬ c ∨ c) then a else b ===>
                                  ∀ (c a _b : Prop), [Decidable c] → a

-- let x := a || a in
-- let y := ! a || x in
-- if y then b else c ===> b
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "IteTrueCond_4" ] ∀ (a : Bool) (b c : Prop), let x := a || a; let y := ! a || x; if y then b else c ===>
                                  ∀ (_a : Bool) (b _c : Prop), b


-- if False then a else b ===> b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteFalseCond_1" ] ∀ (a b : Prop), if False then a else b ===> ∀ (_a b : Prop), b


-- if (! c && c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteFalseCond_2" ] ∀ (c : Bool) (a b : Prop), if (! c) && c then a else b ===> ∀ (_c : Bool) (_a b : Prop), b

-- if (¬ c ∧ c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteFalseCond_3" ] ∀ (c a b : Prop), [Decidable c] → if (¬ c ∧ c) then a else b ===>
                                   ∀ (c _a b : Prop), [Decidable c] → b

-- let x := a && a in
-- let y := ! a && x in
-- if y then b else c ===> c
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "IteFalseCond_4" ] ∀ (a : Bool) (b c : Prop), let x := a && a; let y := ! a && x; if y then b else c ===>
                                   ∀ (_a : Bool) (_b c : Prop), c


-- (if ¬ c then x else y) > x ===> (if c then y else x) > x
#testOptimize [ "IteNegCond_1" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if ¬ c then x else y) > x ===>
                                 ∀ (c : Prop) (x y : Int), [Decidable c] → (if c then y else x) > x

-- (if c = False then x else y) > x ===> (if c then y else x) > x
#testOptimize [ "IteNegCond_2" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = False then x else y) > x ===>
                                 ∀ (c : Prop) (x y : Int), [Decidable c] → (if c then y else x) > x

-- (if ¬ ( a = b ) then x else y) > x ===> (if a = b then y else x) > x
#testOptimize [ "IteNegCond_3" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if ¬ (a = b) then x else y) > x ===>
                                 ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if (a = b) then y else x) > x

-- (( if ¬ c then x else y ) > x) = ((if c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_4" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                   ((if ¬ c then x else y) > x) = ((if c then y else x) > x) ===> True

-- ((if c = False then x else y) > x) = ((if c then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_5" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                   ((if c = False then x else y) > x) = ((if c then y else x) > x) ===> True

-- ((if ¬ a = b then x else y) > x) = ((if a = b then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_6" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                   ((if ¬ (a = b) then x else y) > x) = ((if (a = b) then y else x) > x) ===> True

-- (if c = false then x else y) > x ===> (if true = c then y else x) > x
#testOptimize [ "IteFalseEqCond_1" ] ∀ (c : Bool) (x y : Int), (if c = false then x else y) > x ===>
                                     ∀ (c : Bool) (x y : Int), (if true = c then y else x) > x

-- (if !c then x else y) > x ===> (if true = c then y else x) > x
#testOptimize [ "IteFalseEqCond_2" ] ∀ (c : Bool) (x y : Int), (if !c then x else y) > x ===>
                                     ∀ (c : Bool) (x y : Int), (if true = c then y else x) > x

-- (if c == false then x else y) > x ===> (if true = c then y else x) > x
#testOptimize [ "IteFalseEqCond_3" ] ∀ (c : Bool) (x y : Int), (if c == false then x else y) > x ===>
                                     ∀ (c : Bool) (x y : Int), (if true = c then y else x) > x

-- (if !(! (! c)) then x else y) > x ===> (if true = c then y else x) > x
#testOptimize [ "IteFalseEqCond_4" ] ∀ (c : Bool) (x y : Int), (if ! (! (! c)) then x else y) > x ===>
                                     ∀ (c : Bool) (x y : Int), (if true = c then y else x) > x

-- (if a = (! b && b ) then x else y) > x ===> (if true = a then y else x) > x
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "IteFalseEqCond_5" ] ∀ (a b : Bool) (x y : Int), (if a = (! b && b) then x else y) > x  ===>
                                     ∀ (a _b : Bool) (x y : Int), (if true = a then y else x) > x

-- let x := a || a in
-- let y := ! a || ! x in
-- (if y then p else q) > p ===> (if true = a then q else p) > p
#testOptimize [ "IteFalseEqCond_6" ] ∀ (a : Bool) (p q : Int),
                                       let x := a || a; let y := ! a || ! x;
                                       (if y then p else q) > p ===>
                                     ∀ (a : Bool) (p q : Int),
                                       (if (true = a) then q else p) > p

-- ((if c = false then x else y) > x) = ((if c then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_7" ] ∀ (c : Bool) (x y : Int),
                                       ((if c = false then x else y) > x) = ((if c then y else x) > x) ===> True


-- ((if !c then x else y) > x) = ((if true = c then y else x) > x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_8" ] ∀ (c : Bool) (x y : Int),
                                     ((if !c then x else y ) > x) = ((if c then y else x) > x) ===> True

-- ((if c == false then x else y) > x) = ((if true = c then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_9" ] ∀ (c : Bool) (x y : Int),
                                       ((if c == false then x else y) > x) = ((if true = c then y else x) > x) ===> True

-- ((if !(! (! c)) then x else y) > x) = ((if true = c then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_10" ] ∀ (c : Bool) (x y : Int),
                                        (( if ! (! (! c)) then x else y) > x) = ((if true = c then y else x) > x) ===> True

-- ((if a = (! b && b ) then x else y) > x) = ((if true = a then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_11" ] ∀ (a b : Bool) (x y : Int),
                                        ((if a = (! b && b) then x else y) > x) = ((if true = a then y else x) > x) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ((if y then p else q) > p) = ((if true = a then q else p) > p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_12" ] ∀ (a : Bool) (p q: Int),
                                        let x := a || a; let y := ! a || ! x;
                                        ((if y then p else q ) > p) = ((if (true = a) then q else p) > p) ===> True

-- if c then a else b ===> (!c || a) && (c || b) (with Type(c) = Type(a) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToBoolExpr_1" ] ∀ (c a b : Bool), true = (if c then a else b) ===>
                                    ∀ (c a b : Bool), true = ((a || ! c) && (c || b))

-- ( if c then a else b ) = ( (!c || a) && (c || b) ) ===> True
#testOptimize [ "IteToBoolExpr_2" ] ∀ (c a b : Bool), (if c then a else b) = ( (!c || a) && (c || b) ) ===> True

-- ( if a then a else b ) ===> (a || b)
#testOptimize [ "IteToBoolExpr_3" ] ∀ (a b : Bool), true = (if a then a else b) ===> ∀ (a b : Bool), true = (a || b)

-- ( if a then a else b ) = (a || b) ===> True
#testOptimize [ "IteToBoolExpr_4" ] ∀ (a b : Bool), (if a then a else b) = (a || b) ===> True

-- ( if a then b else a ) ===> (! a || b) && a
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToBoolExpr_5" ] ∀ (a b : Bool), true = (if a then b else a) ===>
                                    ∀ (a b : Bool), true = (a && (b || !a))

-- ( if a then b else a ) = ( (! a || b) && a ) ===> True
#testOptimize [ "IteToBoolExpr_6" ] ∀ (a b : Bool), (if a then b else a) = ( (! a || b) && a ) ===> True

-- ( if a then true else b ) ===> a || b
#testOptimize [ "IteToBoolExpr_7" ] ∀ (a b : Bool), true = (if a then true else b) ===>
                                    ∀ (a b : Bool), true = (a || b)

-- ( if a then true else b ) = ( a || b ) ===> True
#testOptimize [ "IteToBoolExpr_8" ] ∀ (a b : Bool), (if a then true else b) = (a || b) ===> True


-- ( if a then b else true ) ===> ! a || b
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToBoolExpr_9" ] ∀ (a b : Bool), true = (if a then b else true) ===>
                                    ∀ (a b : Bool), true = (b || ! a)

-- ( if a then b else true ) = ( !a || b ) ===> True
#testOptimize [ "IteToBoolExpr_10" ] ∀ (a b : Bool), (if a then b else true) = (!a || b) ===> True


-- ( if a then false else b ) ===> !a && (a || b)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToBoolExpr_11" ] ∀ (a b : Bool), true = (if a then false else b) ===>
                                     ∀ (a b : Bool), true = ( (a || b) && !a)

-- ( if a then false else b ) = !a && ( a || b ) ===> True
#testOptimize [ "IteToBoolExpr_12" ] ∀ (a b : Bool), (if a then false else b) = (!a && (a || b)) ===> True


-- ( if a then b else false ) ===> (! a || b) && a
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToBoolExpr_13" ] ∀ (a b : Bool), true = (if a then b else false) ===>
                                    ∀ (a b : Bool), true = (a && (b || ! a))

-- ( if a then b else false ) = ( !a || b ) && a ===> True
#testOptimize [ "IteToBoolExpr_14" ] ∀ (a b : Bool), (if a then b else false) = ((!a || b) && a) ===> True


-- (if c then a else b) ===> (c → a) ∧ (¬ c → b) (with Type(a) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToPropExpr_1" ] ∀ (c a b : Prop), [Decidable c] → if c then a else b ===>
                                    ∀ (c a b : Prop), [Decidable c] → (¬ c → b) ∧ (c → a)

-- (if c then a else b) ===> (true = c → a) ∧ (false = c → b) (with Type(a) = Prop and Type(c) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToPropExpr_2" ] ∀ (c : Bool) (a b : Prop), if c then a else b ===>
                                    ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)

-- (if c then True else a) ===> (false = c → a) (with Type(c) = Bool)
#testOptimize [ "IteToPropExpr_3" ] ∀ (c : Bool) (a : Prop), if c then True else a ===>
                                    ∀ (c : Bool) (a : Prop), (false = c → a)
-- (if c then False else a) ===> False
#testOptimize [ "IteToPropExpr_4" ] ∀ (c : Bool) (a : Prop), if c then False else a ===> False

-- (if c then a else True) ===> (true = c → a) (with Type(c) = Bool)
#testOptimize [ "IteToPropExpr_5" ] ∀ (c : Bool) (a : Prop), if c then a else True ===>
                                    ∀ (c : Bool) (a : Prop), (true = c → a)

-- (if c then a else False) ===> False
#testOptimize [ "IteToPropExpr_6" ] ∀ (c : Bool) (a : Prop), if c then a else False ===> False


-- (if c then ¬ c else a) ===> ¬ c ∧ (¬ c → a) (with Type(c) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToPropExpr_7" ] ∀ (c : Prop) (a : Prop), [Decidable c] → if c then ¬ c else a ===>
                                    ∀ (c : Prop) (a : Prop), [Decidable c] → (¬ c → a) ∧ ¬ c

-- (if c then a else c) ===> (c → a) ∧ c (with Type(c) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToPropExpr_8" ] ∀ (c : Prop) (a : Prop), [Decidable c] → if c then a else c ===>
                                    ∀ (c : Prop) (a : Prop), [Decidable c] → c ∧ (c → a)

-- (if c then !c else a) ===> (false = c) ∧ (false = c → a) (with Type(c) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "IteToPropExpr_9" ] ∀ (c : Bool) (a : Prop), if c then !c else a ===>
                                    ∀ (c : Bool) (a : Prop), (false = c) ∧ (false = c → a)

-- (if c then a else c) ===> (true = c → a) ∧ (true = c) (with Type(c) = Bool)
#testOptimize [ "IteToPropExpr_10" ] ∀ (c : Bool) (a : Prop), if c then a else c ===>
                                     ∀ (c : Bool) (a : Prop), (true = c → a) ∧ (true = c)


-- (if c then x else y) > x ===> (if true = c then x else y) > x (with Type(c) = Bool)
#testOptimize [ "IteUnchanged_1" ] ∀ (c : Bool) (x y : Int), (if c then x else y) > x ===>
                                   ∀ (c : Bool) (x y : Int), (if true = c then x else y) > x

-- (if c then x else y) > x ===> (if c then x else y) > x (with Type(c) = Prop)
#testOptimize [ "IteUnchanged_2" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if c then x else y) > x ===>
                                   ∀ (c : Prop) (x y : Int), [Decidable c] → (if c then x else y) > x

-- (if c then -x else x) > y ===> (if true = c then Int.neg x else x) > y
#testOptimize [ "IteUnchanged_3" ] ∀ (c : Bool) (x y : Int), (if c then -x else x) > y ===>
                                   ∀ (c : Bool) (x y : Int), (if true = c then Int.neg x else x) > y

-- let p := x + y in
-- let q := x - y in
-- (if c then p else q) > x ===> (if true = c then Int.add x y else Int.sub x y) > x
#testOptimize [ "IteUnchanged_4" ] ∀ (c : Bool) (x y : Int),
                                     let p := x + y; let q := x - y;
                                     (if c then p else q) > x ===>
                                   ∀ (c : Bool) (x y : Int),
                                     (if true = c then Int.add x y else Int.sub x y) > x

-- (if (! a || b) then x else y) > x ===> (if true = (b || ! a) then x else y) > x
#testOptimize [ "IteUnchanged_5" ] ∀ (a b : Bool) (x y : Int),
                                     (if (! a) || b then x else y) > x ===>
                                   ∀ (a b : Bool) (x y : Int),
                                     (if true = ( b || (! a) ) then x else y) > x

-- (if (¬ a ∨ b) then x else y) > x ===> (if ( b ∨ ¬ a ) then x else y) > x
#testOptimize [ "IteUnchanged_6" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                     (if (¬ a ∨ b) then x else y) > x ===>
                                   ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                     (if (b ∨ ¬ a) then x else y) > x

-- let p := a && ! a in
-- let q := a || p in
-- (if q then x else y) > x ===> (if true = a then x else y) > x
#testOptimize [ "IteUnchanged_7" ] ∀ (a : Bool) (x y : Int),
                                     let p := a && !a; let q := a || p;
                                     (if q then x else y) > x ===>
                                   ∀ (a : Bool) (x y : Int),
                                     (if (true = a) then x else y) > x

-- (if (! a && b) then x else y) > x ===> (if true = (b && ! a) then x else y) > x
#testOptimize [ "IteUnchanged_8" ] ∀ (a b : Bool) (x y : Int), (if (! a) && b then x else y) > x ===>
                                   ∀ (a b : Bool) (x y : Int), (if true = ( b && ! a) then x else y) > x

-- (if (¬ a ∧ b) then x else y) > x ===> (if (b ∧ ¬ a) then x else y) > x
#testOptimize [ "IteUnchanged_9" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if (¬ a ∧ b) then x else y) > x ===>
                                   ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if (b ∧ ¬ a) then x else y) > x

-- (if c = True then x else y) > x ===> (if c then x else y) > c
#testOptimize [ "IteUnchanged_10" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = True then x else y) > x ===>
                                    ∀ (c : Prop) (x y : Int), [Decidable c] → (if c then x else y) > x

-- (if a = b then x else y) > x ===> (if a = b then x else y) > x
#testOptimize [ "IteUnchanged_11" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if a = b then x else y) > x ===>
                                    ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if a = b then x else y) > x

-- (if c = true then x else y) > x ===> (if true = c then x else y) > x
#testOptimize [ "IteUnchanged_12" ] ∀ (c : Bool) (x y : Int), (if c = true then x else y) > x ===>
                                    ∀ (c : Bool) (x y : Int), (if true = c then x else y) > x

-- (if c == true then x else y) > x ===> (if true = c then x else y) > x
#testOptimize [ "IteUnchanged_13" ] ∀ (c : Bool) (x y : Int), (if c == true then x else y) > x ===>
                                    ∀ (c : Bool) (x y : Int), (if true = c then x else y) > x

-- (if ! (! c) then x else y) > x ===> (if true = c then x else y) > x
#testOptimize [ "IteUnchanged_14" ] ∀ (c : Bool) (x y : Int), (if ! (! c) then x else y) > x ===>
                                    ∀ (c : Bool) (x y : Int), (if true = c then x else y) > x

-- (if a = (! b || b ) then x else y) > x ===> (if true = a then x else y) > x
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteUnchanged_15" ] ∀ (a b : Bool) (x y : Int), (if a = (! b || b) then x else y) > x ===>
                                    ∀ (a _b : Bool) (x y : Int), (if true = a then x else y) > x


-- ((if c then x else y) > x) = (if true = c then x else y) > x) ===> True (with Type(c) = Bool)
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_16" ] ∀ (c : Bool) (x y : Int),
                                      ((if c then x else y) > x) = ((if true = c then x else y) > x) ===> True


-- ( if c then -x else x ) > y = (if true = c then Int.neg x else x) > y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_17" ] ∀ (c : Bool) (x y : Int),
                                      ((if c then -x else x ) > y) = ((if true = c then Int.neg x else x) > y) ===> True

-- let p := x + y in
-- let q := x - y in
-- ((if c then p else q) > x) = ((if true = c then x + y else x - y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_18" ] ∀ (c : Bool) (x y : Int),
                                      let p := x + y; let q := x - y;
                                      ((if c then p else q) > x) = ((if true = c then x + y else x - y) > x) ===> True

-- (if (! a || b) then x else y) > x) = ((if true = (b || ! a) then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_19" ] ∀ (a b : Bool) (x y : Int),
                                      ((if (! a) || b then x else y) > x) = ((if true = ( b || (! a) ) then x else y) > x) ===> True

-- ((if (¬ a ∨ b) then x else y > x)) = ((if ( b ∨ ¬ a ) then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_20" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      ((if (¬ a ∨ b) then x else y) > x) = ((if (b ∨ ¬ a) then x else y) > x) ===> True

-- let p := a && ! a in
-- let q := a || x in
-- ((if q then x else y) > x) = ((if true = a then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_21" ] ∀ (a : Bool) (x y : Int),
                                      let p := a && !a; let q := a || p;
                                      ((if q then x else y) > x) = ((if (true = a) then x else y) > x) ===> True

-- ((if (! a && b) then x else y) > x) = ((if true = (b && ! a) then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_22" ] ∀ (a b : Bool) (x y : Int),
                                      ((if (! a) && b then x else y) > x) = ((if true = ( b && ! a) then x else y) > x) ===> True

-- ((if (¬ a ∧ b) then x else y) > x) = ((if (b ∧ ¬ a) then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_23" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      ((if (¬ a ∧ b) then x else y) > x) = ((if (b ∧ ¬ a) then x else y) > x) ===> True

-- ((if c = True then x else y) > x) = ((if c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_24" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                      ((if c = True then x else y) > x) = ((if c then x else y) > x) ===> True

-- ((if c = true then x else y) > x) = ((if true = c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_25" ] ∀ (c : Bool) (x y : Int),
                                      ((if c = true then x else y) > x) = ((if true = c then x else y) > x) ===> True

-- ((if c == true then x else y) > x) = ((if true = c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_26" ] ∀ (c : Bool) (x y : Int),
                                      ((if c == true then x else y) > x) = ((if true = c then x else y) > x) ===> True

-- ((if ! (! c) then x else y) > x) = ((if true = c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteUnchanged_27" ] ∀ (c : Bool) (x y : Int),
                                      ((if ! (! c) then x else y) > x) = ((if true = c then x else y) > x) ===> True

-- ((if a = (! b || b ) then x else y) > x) = ((if true = a then x else y) > x) ===> True
#testOptimize [ "IteUnchanged_28" ] ∀ (a b : Bool) (x y : Int),
                                      ((if a = (! b || b) then x else y) > x) = ((if true = a then x else y) > x) ===> True

end Test.OptimizeITE
