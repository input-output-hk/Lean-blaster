import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeDITE
/-! ## Test objectives to validate normalization and simplification rules on `dite` -/

-- if h : c then a else a ===> a (with Type(c) = Bool)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_1" ] ∀ (c : Bool) (a : Prop), if _h : c then a else a ===> ∀ (_c : Bool) (a : Prop), a

-- if h : c then a else a ===> a (with Type(c) = Prop)
-- TODO: remove unused quantifier and constraint when COI performed on forall
#testOptimize [ "DIteAbsorption_2" ] ∀ (c a : Prop), [Decidable c] → if _h : c then a else a ===> ∀ (c a : Prop), [Decidable c] → a

-- if h : c then a ∧ b else b ∧ a ===> a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_3" ] ∀ (c : Bool) (a b : Prop), if _h : c then a ∧ b else b ∧ a ===> ∀ (_c : Bool) (a b : Prop), a ∧ b

-- if h : c then ¬ (¬ a) else a ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_4" ] ∀ (c : Bool) (a : Prop), if _h : c then ¬ (¬ a) else a ===> ∀ (_c : Bool) (a : Prop), a

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- if h : c then x else y ===> a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_5" ] ∀ (c : Bool) (a b : Prop), let x := a ∧ b; let y := (¬ (¬ a)) ∧ b; if _h : c then x else y ===>
                                     ∀ (_c : Bool) (a b : Prop), a ∧ b

-- let x := if h2 : ¬ (p = q) then a else b in
-- let y := if h3 : q = p then b else a in
-- (if h1 : c then x else y) ===> (¬ (p = q) → a) ∧ ((p = q) → b)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_6" ] ∀ (c p q : Bool) (a b : Prop),
                                      let x := if _h2 : ¬ (p = q) then a else b;
                                      let y := if _h3 : (q = p) then b else a;
                                      if _h1 : c then x else y ===>
                                     ∀ (_c p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)
-- let x := if ! d then a else b in
-- let y := if d then b else a in
-- (if h : c then x else y) ===> (false = d → a) ∧ (true = d → b)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_7" ] ∀ (c d : Bool) (a b : Prop),
                                       let x := if ! d then a else b;
                                       let y := if d then b else a;
                                       if _h : c then x else y ===>
                                     ∀ (_c d : Bool) (a b : Prop), ((false = d) → a) ∧ ((true = d) → b)

-- if h : True then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_1" ] ∀ (a b : Prop), if _h : True then a else b ===> ∀ (a _b : Prop), a


-- if h : (! c || c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_2" ] ∀ (c : Bool) (a b : Prop), if _h : (! c) || c then a else b ===> ∀ (_c : Bool) (a _b : Prop), a

-- if h : (¬ c ∨ c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_3" ] ∀ (c a b : Prop), [Decidable c] → if _h : (¬ c ∨ c) then a else b ===>
                                   ∀ (c a _b : Prop), [Decidable c] → a

-- let x := a || a in
-- let y := ! a || x in
-- if h : y then b else c ===> b
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "DIteTrueCond_4" ] ∀ (a : Bool) (b c : Prop), let x := a || a; let y := ! a || x; if _h : y then b else c ===>
                                   ∀ (_a : Bool) (b _c : Prop), b


-- if h : False then a else b ===> b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_1" ] ∀ (a b : Prop), if _h : False then a else b ===> ∀ (_a b : Prop), b


-- if h : (! c && c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_2" ] ∀ (c : Bool) (a b : Prop), if _h : (! c) && c then a else b ===> ∀ (_c : Bool) (_a b : Prop), b

-- if h : (¬ c ∧ c) then a else b ===> a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_3" ] ∀ (c a b : Prop), [Decidable c] → if _h : (¬ c ∧ c) then a else b ===>
                                   ∀ (c _a b : Prop), [Decidable c] → b

-- let x := a && a in
-- let y := ! a && x in
-- if h : y then b else c ===> c
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "DIteFalseCond_4" ] ∀ (a : Bool) (b c : Prop), let x := a && a; let y := ! a && x; if _h : y then b else c ===>
                                   ∀ (_a : Bool) (_b c : Prop), c


-- (if h : ¬ c then x else y) > x ===> (if h : c then y else x) > x
#testOptimize [ "DIteNegCond_1" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : ¬ c then x else y) > x ===>
                                  ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c then y else x) > x

-- (if h : c = False then x else y) > x ===> (if h : c then y else x) > x
#testOptimize [ "DIteNegCond_2" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c = False then x else y) > x ===>
                                  ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c then y else x) > x

-- (if h : ¬ ( a = b ) then x else y) > x ===> (if h : a = b then y else x) > x
#testOptimize [ "DIteNegCond_3" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                    (if _h : ¬ (a = b) then x else y) > x ===>
                                  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                    (if _h : a = b then y else x) > x

-- ( ( if h : ¬ c then x else y ) > x) = ( (if h : c then y else x) > x ) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_4" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                    ((if _h : ¬ c then x else y) > x) = ((if _h : c then y else x) > x) ===> True

-- ( ( if h : c = False then x else y ) > x ) = ( (if h : c then y else x) > x ) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_5" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                    ((if _h : c = False then x else y) > x) = ((if _h : c then y else x) > x) ===> True

-- (( if h : ¬ (a = b) then x else y ) > x) = ((if h : a = b then y else x) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_6" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                    ((if _h : ¬ (a = b) then x else y) > x) = ((if _h : a = b then y else x) > x) ===> True

-- (( if h : c = false then x else y) > x ) = ((if h : true = c then y else x) > x) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_1" ] ∀ (c : Bool) (x y : Int),
                                        ((if _h : c = false then x else y) > x) = ((if _h : true = c then y else x) > x) ===> True

-- (( if h : !c then x else y) > x) = ((if h : true = c then y else x) > x) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_2" ] ∀ (c : Bool) (x y : Int),
                                        ((if _h : !c then x else y) > x) = ((if _h : true = c then y else x) > x) ===> True

-- ((if h : c == false then x else y) > x) = ((if h : true = c then y else x) > x) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_3" ] ∀ (c : Bool) (x y : Int),
                                        ((if _h : c == false then x else y) > x) = ((if _h : true = c then y else x) > x) ===> True

-- ((if h : !(! (! c)) then x else y) > x) = ((if h : true = c then y else x) > x) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_4" ] ∀ (c : Bool) (x y : Int),
                                        ((if _h : ! (! (! c)) then x else y) > x) = ((if _h : true = c then y else x) > x) ===> True

-- (( if h : a = (! b && b ) then x else y) > x ) = ((if h : true = a then y else x) > x) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_5" ] ∀ (a b : Bool) (x y : Int),
                                        ((if _h : a = (! b && b) then x else y) > x) = ((if _h : true = a then y else x) > x) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ((if h : y then p else q) > p) = ((if h : true = a then q else p)> p) ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteFalseEqCond_6" ] ∀ (a : Bool) (p q : Int),
                                        let x := a || a; let y := ! a || ! x;
                                        ((if _h : y then p else q) > p) = ((if _h : (true = a) then q else p) > p) ===> True

-- if h : c then a else b ===> (!c || a) && (c || b) (with Type(c) = Type(a) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToBoolExpr_1" ] ∀ (c a b : Bool), true = (if _h : c then a else b) ===>
                                     ∀ (c a b : Bool), true = ( (a || ! c) && (c || b) )

-- ( if h : c then a else b ) = ( (!c || a) && (c || b) ) ===> True
#testOptimize [ "DIteToBoolExpr_2" ] ∀ (c a b : Bool), (if _h : c then a else b) = ( (!c || a) && (c || b) ) ===> True

-- ( if h : a then a else b ) ===> (a || b)
#testOptimize [ "DIteToBoolExpr_3" ] ∀ (a b : Bool), true = (if _h : a then a else b) ===> ∀ (a b : Bool), true = (a || b)

-- ( if h : a then a else b ) = (a || b) ===> True
#testOptimize [ "DIteToBoolExpr_4" ] ∀ (a b : Bool), (if _h : a then a else b) = (a || b) ===> True

-- ( if h : a then b else a ) ===> (! a || b) && a
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToBoolExpr_5" ] ∀ (a b : Bool), true = (if _h : a then b else a) ===>
                                     ∀ (a b : Bool), true = (a && (b || !a))

-- ( if h : a then b else a ) = ( (! a || b) && a ) ===> True
#testOptimize [ "DIteToBoolExpr_6" ] ∀ (a b : Bool), (if _h : a then b else a) = ( (! a || b) && a ) ===> True

-- ( if h : a then true else b ) ===> a || b
#testOptimize [ "DIteToBoolExpr_7" ] ∀ (a b : Bool), true = (if _h : a then true else b) ===>
                                     ∀ (a b : Bool), true = (a || b)

-- ( if h : a then true else b ) = ( a || b ) ===> True
#testOptimize [ "DIteToBoolExpr_8" ] ∀ (a b : Bool), (if _h : a then true else b) = (a || b) ===> True


-- ( if h : a then b else true ) ===> ! a || b
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToBoolExpr_9" ] ∀ (a b : Bool), true = (if _h : a then b else true) ===>
                                     ∀ (a b : Bool), true = (b || ! a)

-- ( if h : a then b else true ) = ( !a || b ) ===> True
#testOptimize [ "DIteToBoolExpr_10" ] ∀ (a b : Bool), (if _h : a then b else true) = (!a || b) ===> True


-- ( if h : a then false else b ) ===> !a && (a || b)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToBoolExpr_11" ] ∀ (a b : Bool), true = (if _h : a then false else b) ===>
                                      ∀ (a b : Bool), true = ((a || b) && !a)

-- ( if h : a then false else b ) = (( a || b ) && !a) ===> True
#testOptimize [ "DIteToBoolExpr_12" ] ∀ (a b : Bool), (if _h : a then false else b) = ((a || b) && !a) ===> True

-- ( if h : a then b else false ) ===> (! a || b) && a
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToBoolExpr_13" ] ∀ (a b : Bool), true = (if _h : a then b else false) ===>
                                      ∀ (a b : Bool), true = (a && (b || ! a))

-- ( if h : a then b else false ) = ( b || !a ) && a ===> True
#testOptimize [ "DIteToBoolExpr_14" ] ∀ (a b : Bool), (if _h : a then b else false) = ((b || !a) && a) ===> True


-- (if h : c then a else b) ===> (c → a) ∧ (¬ c → b) (with Type(a) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToPropExpr_1" ] ∀ (c a b : Prop), [Decidable c] → if _h : c then a else b ===>
                                     ∀ (c a b : Prop), [Decidable c] → (¬ c → b) ∧ (c → a)

-- (if h : c then a else b) ===> (true = c → a) ∧ (false = c → b) (with Type(a) = Prop and Type(c) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToPropExpr_2" ] ∀ (c : Bool) (a b : Prop), if _h : c then a else b ===>
                                    ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)

-- (if h : c then True else a) ===> (false = c → a) (with Type(c) = Bool)
#testOptimize [ "DIteToPropExpr_3" ] ∀ (c : Bool) (a : Prop), if _h : c then True else a ===>
                                     ∀ (c : Bool) (a : Prop), (false = c → a)

-- (if h : c then False else a) ===> False
#testOptimize [ "DIteToPropExpr_4" ] ∀ (c : Bool) (a : Prop), if _h : c then False else a ===> False

-- (if h : c then a else True) ===> (true = c → a) (with Type(c) = Bool)
#testOptimize [ "DIteToPropExpr_5" ] ∀ (c : Bool) (a : Prop), if _h : c then a else True ===>
                                     ∀ (c : Bool) (a : Prop), (true = c → a)

-- (if h : c then a else False) ===> False
#testOptimize [ "DIteToPropExpr_6" ] ∀ (c : Bool) (a : Prop), if _h : c then a else False ===> False


-- (if h : c then ¬ c else a) ===> ¬ c ∧ (¬ c → a) (with Type(c) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToPropExpr_7" ] ∀ (c : Prop) (a : Prop), [Decidable c] → if _h : c then ¬ c else a ===>
                                     ∀ (c : Prop) (a : Prop), [Decidable c] → ¬ c ∧ (¬ c → a)

-- (if h : c then a else c) ===> (c → a) ∧ c (with Type(c) = Prop)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToPropExpr_8" ] ∀ (c : Prop) (a : Prop), [Decidable c] → if _h : c then a else c ===>
                                     ∀ (c : Prop) (a : Prop), [Decidable c] → c ∧ (c → a)

-- (if h : c then !c else a) ===> (false = c) ∧ (false = c → a) (with Type(c) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteToPropExpr_9" ] ∀ (c : Bool) (a : Prop), if _h : c then !c else a ===>
                                     ∀ (c : Bool) (a : Prop), (false = c) ∧ (false = c → a)

-- (if h : c then a else c) ===> (true = c → a) ∧ (true = c) (with Type(c) = Bool)
#testOptimize [ "DIteToPropExpr_10" ] ∀ (c : Bool) (a : Prop), if _h : c then a else c ===>
                                      ∀ (c : Bool) (a : Prop), (true = c → a) ∧ (true = c)


-- (if h : a = b then x else y) > x ===> (if h : a = b then x else y) > x (with Type(a) = Type (b) =  Bool)
#testOptimize [ "DIteUnchanged_1" ] ∀ (a b : Bool) (x y : Int), (if _h : a = b then x else y) > x ===>
                                    ∀ (a b : Bool) (x y : Int), (if _h : a = b then x else y) > x

-- (if h : c then x else y) > x ===> (if h : c then x else y) > x (with Type(c) = Prop)
#testOptimize [ "DIteUnchanged_2" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c then x else y) > x ===>
                                    ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c then x else y) > x

-- (if h : c then -x else x) = if h : true = c then -x else x ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_3" ] ∀ (c : Bool) (x : Int), (if _h : c then -x else x) = if _h : true = c then -x else x ===> True

-- let p := x + y in
-- let q := x - y in
-- (if h : c then p else q) = if h : true = c then x + y else x - y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_4" ] ∀ (c : Bool) (x y : Int),
                                      let p := x + y; let q := x - y;
                                      (if _h : c then p else q) = (if _h : true = c then x + y else x - y) ===> True

-- (if h : (! a || b) then x else y) = if h : true = (b || ! a) then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_5" ] ∀ (a b : Bool) (x y : Int),
                                      (if _h : (! a) || b then x else y) = if _h : true = ( b || (! a) ) then x else y ===> True

-- (if h : (¬ a ∨ b) then x else y) > x ===> (if h : ( b ∨ ¬ a ) then x else y) > x
#testOptimize [ "DIteUnchanged_6" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if _h : (¬ a ∨ b) then x else y) > x ===>
                                    ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if _h : (b ∨ ¬ a) then x else y) > x

-- let p := a && ! a in
-- let q := a || p in
-- (if h : q then x else y) = if true = a then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_7" ] ∀ (a : Bool) (x y : Int),
                                      let p := a && !a; let q := a || p;
                                      (if _h : q then x else y) = if _h : (true = a) then x else y ===> True

-- (if h : (! a && b) then x else y) = if true = (b && ! a) then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_8" ] ∀ (a b : Bool) (x y : Int),
                                      (if _h : (! a) && b then x else y) = if _h : true = ( b && ! a) then x else y ===> True

-- (if h : (¬ a ∧ b) then x else y) > x ===> (if h : (b ∧ ¬ a) then x else y) > x
#testOptimize [ "DIteUnchanged_9" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if _h : (¬ a ∧ b) then x else y) > x ===>
                                    ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (if _h : (b ∧ ¬ a) then x else y) > x

-- (if h : c = True then x else y) > x ===> (if h : c then x else y) > x
#testOptimize [ "DIteUnchanged_10" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c = True then x else y) > x ===>
                                     ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c then x else y) > x

-- (if h : a = b then x else y) > x ===> (if h : a = b then x else y) > x
-- NOTE: reordering applied on commutative operators
#testOptimize [ "DIteUnchanged_11" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if _h : a = b then x else y) > x ===>
                                     ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if _h : a = b then x else y) > x

-- (if h : c = true then x else y) = if h : true = c then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_12" ] ∀ (c : Bool) (x y : Int),
                                       (if _h : c = true then x else y) = if _h : true = c then x else y ===> True

-- (if h : c == true then x else y) = if h : true = c then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_13" ] ∀ (c : Bool) (x y : Int),
                                       (if _h : c == true then x else y) = if _h : true = c then x else y ===> True

-- (if h : ! (! c) then x else y) = if h : true = c then x else y ===> True
-- NOTE: here, we can only check for equality as constraint `h` is internally rewritten for the `then` and `else` branches.
#testOptimize [ "DIteUnchanged_14" ] ∀ (c : Bool) (x y : Int),
                                       (if _h : ! (! c) then x else y) = if _h : true = c then x else y ===> True

-- (if h : (¬ a ∨ b) then x else y) > x = (if h : ( b ∨ ¬ a ) then x else y) > x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteUnchanged_15" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                       ((if _h : (¬ a ∨ b) then x else y) > x) = ((if _h : (b ∨ ¬ a) then x else y) > x) ===> True

-- (( if h : (¬ a ∧ b) then x else y ) > x) = ((if h : (b ∧ ¬ a) then x else y)> x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteUnchanged_16" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      ((if _h : (¬ a ∧ b) then x else y ) > x) = ((if _h : (b ∧ ¬ a) then x else y) > x) ===> True

-- ((if _h : c = True then x else y) > x) = ((if _h : c then x else y) > x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteUnchanged_17" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                       ((if _h : c = True then x else y ) > x) = ((if _h : c then x else y) > x) ===> True

-- ( if _h : a = (! b || b ) then x else y ) = if _h : true = a then x else y ===> True
#testOptimize [ "DIteUnchanged_18" ] ∀ (a b : Bool) (x y : Int),
                                      ( if _h : a = (! b || b) then x else y ) = if _h : true = a then x else y ===> True

end Test.OptimizeDITE
