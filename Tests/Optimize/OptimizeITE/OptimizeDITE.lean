import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeDITE
/-! ## Test objectives to validate normalization and simplification rules on `dite` -/

/-! Test cases for simplification rule ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> e1 (if e1 =ₚₜᵣ e2)`. -/

-- ∀ (c : Bool) (a : Prop) (f : c → Prop → Prop),
--   if h : c then ((f h a) ∧ (¬ f h a)) ∨ a else a ===>
-- ∀ (a : Prop), a
#testOptimize [ "DIteAbsorption_1" ]
  ∀ (c : Bool) (a : Prop) (f : c → Prop → Prop),
    if h : c then ((f h a) ∧ (¬ f h a)) ∨ a else a ===>
  ∀ (a : Prop), a

-- ∀ (c a : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then ((f h a) ∧ ¬ (f h a)) ∨ a else a ===>
-- ∀ (a : Prop), a
#testOptimize [ "DIteAbsorption_2" ]
  ∀ (c a : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then ((f h a) ∧ ¬ (f h a)) ∨ a else a ===>
  ∀ (a : Prop), a

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   if h : c then ((f h a) ∨ True) ∧ a ∧ b else b ∧ a ===>
-- ∀ (a b : Prop), a ∧ b
#testOptimize [ "DIteAbsorption_3" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    if h : c then ((f h a) ∨ True) ∧ a ∧ b else b ∧ a ===>
  ∀ (a b : Prop), a ∧ b

-- ∀ (c : Bool) (a : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then ¬ (¬ a) else a ∧ ((f h c) ∨ True) ===>
-- ∀ (a : Prop), a
#testOptimize [ "DIteAbsorption_4" ]
  ∀ (c : Bool) (a : Prop) (f : ¬ c → Prop → Prop),
    if h : c then ¬ (¬ a) else a ∧ ((f h c) ∨ True) ===>
  ∀ (a : Prop), a

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
--   if h : c then ((f h a) ∨ True) ∧ x else y ===>
-- ∀ (a b : Prop), a ∧ b
#testOptimize [ "DIteAbsorption_5" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
    if h : c then ((f h a) ∨ True) ∧ x else y ===>
  ∀ (a b : Prop), a ∧ b

-- ∀ (a c : Bool) (f : ¬ c → Bool → Bool),
--   if h : c then !(! a) else ((f h c) || true) && a ===>
-- ∀ (a : Bool), true = a
#testOptimize [ "DIteAbsorption_6" ]
  ∀ (a c : Bool) (f : ¬ c → Bool → Bool),
    if h : c then !(! a) else ((f h c) || true) && a ===>
  ∀ (a : Bool), true = a


-- ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
--   if h : c then (!(!a)) = !(!(!b)) else a = !b ∧ (True ∨ (f h a)) ===>
-- ∀ (a b : Bool), a = !b
#testOptimize [ "DIteAbsorption_7" ]
  ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
    if h : c then (!(!a)) = !(!(!b)) else a = !b ∧ (True ∨ (f h a)) ===>
  ∀ (a b : Bool), a = !b

-- ∀ (c : Bool) (x y : Nat) (f : ¬ c → Nat → Nat),
--   (if h : c then (x + 40) - 40 else (0 - (f h y)) + x) < y ===>
-- ∀ (x y : Nat), x < y
#testOptimize [ "DIteAbsorption_8" ]
  ∀ (c : Bool) (x y : Nat) (f : ¬ c → Nat → Nat),
    (if h : c then (x + 40) - 40 else (0 - (f h y)) + x) < y ===>
  ∀ (x y : Nat), x < y

-- ∀ (c : Bool) (f : c → Int → Int),
--   if h : c then ∀ (x y : Int), x > (0 * (f h x)) + y else ∀ (z y : Int), y < z ===>
-- ∀ (x y : Int), y < x
#testOptimize [ "DIteAbsorption_9" ]
  ∀ (c : Bool) (f : c → Int → Int),
    if h : c then ∀ (x y : Int), x > (0 * (f h x)) + y else ∀ (z y : Int), y < z ===>
  ∀ (x y : Int), y < x

-- ∀ (c p q : Bool) (a b : Prop) (f : c → Prop → Prop),
--   let x := if ¬ (p = q) then a else b;
--   let y := if (q = p) then b else a;
--   if h : c then (¬ (f h a) ∧ False) ∨ x else y ===>
-- ∀ (p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)
#testOptimize [ "DIteAbsorption_10" ]
  ∀ (c p q : Bool) (a b : Prop) (f : c → Prop → Prop),
    let x := if ¬ (p = q) then a else b;
    let y := if (q = p) then b else a;
    if h : c then (¬ (f h a) ∧ False) ∨ x else y ===>
  ∀ (p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)


-- ∀ (c : Bool) (a : Prop) (f : c → Prop → Prop),
--   (if h : c then ((f h a) ∨ True) ∧ a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_11" ]
  ∀ (c : Bool) (a : Prop) (f : c → Prop → Prop),
    (if h : c then ((f h a) ∨ True) ∧ a else a) = a ===> True

-- ∀ (c a : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then ((f h a) ∨ True) ∧ a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_12" ]
  ∀ (c a : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then ((f h a) ∨ True) ∧ a else a) = a ===> True

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--  (if h : c then ((f h a) ∨ True) ∧ a ∧ b else b ∧ a) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_13" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
   (if h : c then ((f h a) ∨ True) ∧ a ∧ b else b ∧ a) = (a ∧ b) ===> True

-- ∀ (c : Bool) (a : Prop) (f : ¬ c → Prop → Prop),
--   (if h : c then ¬ (¬ a) else ((f h c) ∨ True) ∧ a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_14" ]
  ∀ (c : Bool) (a : Prop) (f : ¬ c → Prop → Prop),
    (if h : c then ¬ (¬ a) else ((f h c) ∨ True) ∧ a) = a ===> True

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
--   (if h : c then ((f h a) ∨ True) ∧ x else y) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_15" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
    (if h : c then ((f h a) ∨ True) ∧ x else y) = (a ∧ b) ===> True

-- ∀ (a c : Bool) (f : ¬ c → Bool → Bool),
--   (if h : c then !(! a) else ((f h c) || true) && a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_16" ]
  ∀ (a c : Bool) (f : ¬ c → Bool → Bool),
    (if h : c then !(! a) else ((f h c) || true) && a) = a ===> True

-- ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
--   (if h : c then (!(!a)) = !(!(!b)) else a = !b ∧ (True ∨ (f h a))) = (a = !b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_17" ]
  ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
    (if h : c then (!(!a)) = !(!(!b)) else a = !b ∧ (True ∨ (f h a))) = (a = !b) ===> True

-- ∀ (c : Bool) (x y : Nat) (f : ¬ c → Nat → Nat),
--   ((if h : c then (x + 40) - 40 else (0 - (f h y)) + x) < y) = (x < y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_18" ]
  ∀ (c : Bool) (x y : Nat) (f : ¬ c → Nat → Nat),
    ((if h : c then (x + 40) - 40 else (0 - (f h y)) + x) < y) = (x < y) ===> True

-- ∀ (c : Bool) (f : c → Int → Int),
--   (if h : c then ∀ (x y : Int), x > (0 * (f h x)) + y else ∀ (z y : Int), y < z) =
--   ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_19" ]
  ∀ (c : Bool) (f : c → Int → Int),
    (if h : c then ∀ (x y : Int), x > (0 * (f h x)) + y else ∀ (z y : Int), y < z) =
    ∀ (x y : Int), y < x ===> True

-- ∀ (c p q : Bool) (a b : Prop) (f : c → Prop → Prop),
--   let x := if ¬ (p = q) then a else b;
--   let y := if (q = p) then b else a;
--   (if h : c then (¬ (f h a) ∧ False) ∨ x else y) = (if p = q then b else a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_20" ]
  ∀ (c p q : Bool) (a b : Prop) (f : c → Prop → Prop),
    let x := if ¬ (p = q) then a else b;
    let y := if (q = p) then b else a;
    (if h : c then (¬ (f h a) ∧ False) ∨ x else y) = (if p = q then b else a) ===> True



/-! Test cases to ensure that simplification rule
      ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> e1 (if e1 =ₚₜᵣ e2)`
    is not applied wrongly.
-/

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   if h : c then f h a else b ===>
-- ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
--   (false = c → b) ∧ (∀ (h : true = c), f h a)
#testOptimize [ "DIteAbsorptionUnchanged_1" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    if h : c then f h a else b ===>
  ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
    (false = c → b) ∧ (∀ (h : true = c), f h a)

-- ∀ (c a b : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then (f h a) else b ===>
-- ∀ (c a b : Prop) (f : c → Prop → Prop),
--   (∀ (h : c), f h a) ∧ (¬ c → b)
#testOptimize [ "DIteAbsorptionUnchanged_2" ]
  ∀ (c a b : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then (f h a) else b ===>
  ∀ (c a b : Prop) (f : c → Prop → Prop),
    (∀ (h : c), f h a) ∧ (¬ c → b)

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   if h : c then f h a ∧ b else ¬ a ∧ ¬ b ===>
-- ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
--   (false = c → ¬ a ∧ ¬ b) ∧ (∀ (h : true = c), b ∧ f h a)
#testOptimize [ "DIteAbsorptionUnchanged_3" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    if h : c then f h a ∧ b else ¬ a ∧ ¬ b ===>
  ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
    (false = c → ¬ a ∧ ¬ b) ∧ (∀ (h : true = c), b ∧ f h a)

-- ∀ (c : Bool) (a b : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then ¬ (¬ a) else f h b ===>
-- ∀ (c : Bool) (a b : Prop) (f : false = c → Prop → Prop),
--   (∀ (h : false = c),  f h b) ∧ (true = c → a)
#testOptimize [ "DIteAbsorptionUnchanged_4" ]
  ∀ (c : Bool) (a b : Prop) (f : ¬ c → Prop → Prop),
    if h : c then ¬ (¬ a) else f h b ===>
  ∀ (c : Bool) (a b : Prop) (f : false = c → Prop → Prop),
    (∀ (h : false = c),  f h b) ∧ (true = c → a)

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   let x := ¬ a ∧ ¬ b;
--   let y := (¬ (¬ a)) ∧ b;
--   if h : c then f h x else y ===>
-- ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
--   (false = c → a ∧ b) ∧ (∀ (h : true = c), f h (¬ a ∧ ¬ b))
#testOptimize [ "DIteAbsorptionUnchanged_5" ]
  ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
    let x := ¬ a ∧ ¬ b;
    let y := (¬ (¬ a)) ∧ b;
    if h : c then f h x else y ===>
  ∀ (c : Bool) (a b : Prop) (f : true = c → Prop → Prop),
    (false = c → a ∧ b) ∧ (∀ (h : true = c), f h (¬ a ∧ ¬ b))

-- ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
--   (if h : c then !(! a) else f h b) = true ===>
-- ∀ (a b c : Bool) (f : false = c → Bool → Bool),
--   (∀ (h : false = c), true = f h b) ∧ (true = c → true = a)
#testOptimize [ "DIteAbsorptionUnchanged_6" ]
  ∀ (a b c : Bool) (f : ¬ c → Bool → Bool),
    (if h : c then !(! a) else f h b) = true ===>
  ∀ (a b c : Bool) (f : false = c → Bool → Bool),
    (∀ (h : false = c), true = f h b) ∧ (true = c → true = a)

-- ∀ (a b c d: Bool) (f : ¬ c → Bool → Bool),
--   if h : c then (!(!a)) = !(!(!b)) else (f h b) = !d ===>
-- ∀ (a b c d : Bool) (f : false = c → Bool → Bool),
--   (∀ (h : false = c), (!d) = f h b) ∧ (true = c → a = !b)
#testOptimize [ "DIteAbsorptionUnchanged_7" ]
  ∀ (a b c d: Bool) (f : ¬ c → Bool → Bool),
    if h : c then (!(!a)) = !(!(!b)) else (f h b) = !d ===>
  ∀ (a b c d : Bool) (f : false = c → Bool → Bool),
    (∀ (h : false = c), (!d) = f h b) ∧ (true = c → a = !b)

-- ∀ (c : Bool) (x y z : Nat) (f : ¬ c → Nat → Nat),
--  (if h : c then (x + 40) - 40 else f h y) < z ===>
-- ∀ (c : Bool) (x y z : Nat) (f : ¬ c → Nat → Nat),
--  Solver.dite' (true = c) (fun _ => x) (fun h : _ => f h y) < z
def diteAbsorptionUnchanged_8 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE `h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE `h
              (Lean.Expr.const `Nat [])
              (Lean.Expr.const `Nat [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Bool []))
                          (Lean.Expr.const `Bool.true []))
                        (Lean.Expr.bvar 4)))
                  (Lean.Expr.lam `h
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 4)
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.false []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                  (Lean.BinderInfo.default))))
            (Lean.Expr.bvar 1))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteAbsorptionUnchanged_8" : term => return diteAbsorptionUnchanged_8

#testOptimize [ "DIteAbsorptionUnchanged_8" ]
  ∀ (c : Bool) (x y z : Nat) (f : ¬ c → Nat → Nat),
    (if h : c then (x + 40) - 40 else f h y) < z ===> diteAbsorptionUnchanged_8

-- ∀ (c : Bool) (f : c → Int → Int),
--   if h : c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool) (f : true = c → Int → Int),
--   (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), y < f h x)
#testOptimize [ "DIteAbsorptionUnchanged_9" ]
  ∀ (c : Bool) (f : c → Int → Int),
    if h : c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool) (f : true = c → Int → Int),
    (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), y < f h x)


/-! Test cases for simplification rule `dite True (fun h : True => e1) (fun h : False => e2)` ==> e1`. -/

-- ∀ (a b : Prop) (f : ¬ True → Prop → Prop),
-- if h : True then a else f h b ===> ∀ (a : Prop), a
#testOptimize [ "DIteTrueCond_1" ]
  ∀ (a b : Prop) (f : ¬ True → Prop → Prop),
  if h : True then a else f h b ===> ∀ (a : Prop), a

-- ∀ (a b : Bool) (f : ¬ True → Bool → Bool), if h : True then !a else f h b ===>
-- ∀ (a : Bool), false = a
#testOptimize [ "DIteTrueCond_2" ]
  ∀ (a b : Bool) (f : ¬ True → Bool → Bool), if h : True then !a else f h b ===>
  ∀ (a : Bool), false = a

-- ∀ (x y z : Nat) (f : ¬ True → Nat → Nat),
--   (if h : True then (x + 40) - 40 else f h y) < z ===>
-- ∀ (x z : Nat), x < z
#testOptimize [ "DIteTrueCond_3" ]
  ∀ (x y z : Nat) (f : ¬ True → Nat → Nat),
    (if h : True then (x + 40) - 40 else f h y) < z ===>
  ∀ (x z : Nat), x < z

-- ∀ (f : ¬ True → Int → Int),
--   if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), f h y > z ===>
-- ∀ (x y : Int), y < x
#testOptimize [ "DIteTrueCond_4" ]
  ∀ (f : ¬ True → Int → Int),
    if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), f h y > z ===>
  ∀ (x y : Int), y < x

-- ∀ (c : Bool) (a b : Prop) (f : ¬ ((! c) || c) → Prop → Prop),
--   if h : (! c) || c then a else f h b ===>
-- ∀ (a : Prop), a
#testOptimize [ "DIteTrueCond_5" ]
  ∀ (c : Bool) (a b : Prop) (f : ¬ ((! c) || c) → Prop → Prop),
    if h : (! c) || c then a else f h b ===>
  ∀ (a : Prop), a

-- ∀ (c a b : Prop) (f : ¬ (¬ c ∨ c) → Prop → Prop), [Decidable c] →
--   if h : (¬ c ∨ c) then a else f h b ===>
-- ∀ (a : Prop), a
#testOptimize [ "DIteTrueCond_6" ]
  ∀ (c a b : Prop) (f : ¬ (¬ c ∨ c) → Prop → Prop), [Decidable c] →
    if h : (¬ c ∨ c) then a else f h b ===>
  ∀ (a : Prop), a

-- ∀ (a : Bool) (b c : Prop),
--   let x := a || a; let y := ! a || x;
--   ∀ (f : ¬ y → Prop → Prop),
--     if h : y then b else f h c ===>
-- ∀ (b : Prop), b
#testOptimize [ "DIteTrueCond_7" ]
  ∀ (a : Bool) (b c : Prop),
    let x := a || a; let y := ! a || x;
    ∀ (f : ¬ y → Prop → Prop),
      if h : y then b else f h c ===>
  ∀ (b : Prop), b

-- ∀ (a b : Prop) (f : ¬ True → Prop → Prop),
--   (if h : True then a else f h b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_8" ]
  ∀ (a b : Prop) (f : ¬ True → Prop → Prop),
    (if h : True then a else f h b) = a ===> True

-- ∀ (a b : Bool) (f : ¬ True → Bool → Bool),
--   (if h : True then !a else f h b) = !a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_9" ]
  ∀ (a b : Bool) (f : ¬ True → Bool → Bool),
    (if h : True then !a else f h b) = !a ===> True

-- ∀ (x y z : Nat) (f : ¬ True → Nat → Nat),
--   ((if h : True then (x + 40) - 40 else f h y) < z) = (x < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_10" ]
  ∀ (x y z : Nat) (f : ¬ True → Nat → Nat),
    ((if h : True then (x + 40) - 40 else f h y) < z) = (x < z) ===> True

-- ∀ (f : ¬ True → Int → Int),
--   (if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), f h y > z) =
--   ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_11" ]
  ∀ (f : ¬ True → Int → Int),
    (if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), f h y > z) =
    ∀ (x y : Int), y < x ===> True

-- ∀ (c : Bool) (a b : Prop) (f : ¬ ((! c) || c) → Prop → Prop),
--   (if h : (! c) || c then a else f h b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_12" ]
  ∀ (c : Bool) (a b : Prop) (f : ¬ ((! c) || c) → Prop → Prop),
    (if h : (! c) || c then a else f h b) = a ===> True

-- ∀ (c a b : Prop) (f : ¬ (¬ c ∨ c) → Prop → Prop), [Decidable c] →
--   (if h : (¬ c ∨ c) then a else f h b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_13" ]
  ∀ (c a b : Prop) (f : ¬ (¬ c ∨ c) → Prop → Prop), [Decidable c] →
    (if h : (¬ c ∨ c) then a else f h b) = a ===> True

-- ∀ (a : Bool) (b c : Prop),
--   let x := a || a; let y := ! a || x;
--   ∀ (f : ¬ y → Prop → Prop),
--     (if h : y then b else f h c) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_14" ]
   ∀ (a : Bool) (b c : Prop),
     let x := a || a; let y := ! a || x;
     ∀ (f : ¬ y → Prop → Prop),
       (if h : y then b else f h c) = b ===> True


/-! Test cases for simplification rule `dite False (fun h : True => e1) (fun h : False => e2)` ==> e2`. -/

-- ∀ (a b : Prop) (f : False → Prop → Prop),
--   if h : False then f h a else b ===> ∀ (b : Prop), b
#testOptimize [ "DIteFalseCond_1" ]
  ∀ (a b : Prop) (f : False → Prop → Prop),
    if h : False then f h a else b ===> ∀ (b : Prop), b

-- ∀ (a b : Bool) (f : False → Bool → Bool),
--   if h : False then f h !a else b ===>
-- ∀ (b : Bool), true = b
#testOptimize [ "DIteFalseCond_2" ]
  ∀ (a b : Bool) (f : False → Bool → Bool), if h : False then f h !a else b ===>
  ∀ (b : Bool), true = b

-- ∀ (x y z : Nat) (f : False → Nat → Nat), (if h : False then (f h x + 40) - 40 else y) < z ===>
-- ∀ (y z : Nat), y < z
#testOptimize [ "DIteFalseCond_3" ]
  ∀ (x y z : Nat) (f : False → Nat → Nat), (if h : False then (f h x + 40) - 40 else y) < z ===>
  ∀ (y z : Nat), y < z

-- ∀ (f : False → Int → Int),
--   if h : False then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (z y : Int), z < y
#testOptimize [ "DIteFalseCond_4" ]
  ∀ (f : False → Int → Int),
    if h : False then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (z y : Int), z < y

-- ∀ (c : Bool) (a b : Prop) (f : (! c) && c → Prop → Prop),
--   if h : (! c) && c then f h a else b ===>
-- ∀ (b : Prop), b
-- ∀ (c : Bool) (a b : Prop), if h : (! c && c) then a else b ===> ∀ (b : Prop), b
#testOptimize [ "DIteFalseCond_5" ]
  ∀ (c : Bool) (a b : Prop) (f : (! c) && c → Prop → Prop),
    if h : (! c) && c then f h a else b ===>
  ∀ (b : Prop), b

-- ∀ (c a b : Prop) (f : ¬ c ∧ c → Prop → Prop), [Decidable c] →
--   if h : ¬ c ∧ c then f h a else b ===>
-- ∀ (b : Prop), b
#testOptimize [ "DIteFalseCond_6" ]
  ∀ (c a b : Prop) (f : ¬ c ∧ c → Prop → Prop), [Decidable c] →
    if h : ¬ c ∧ c then f h a else b ===>
  ∀ (b : Prop), b

-- ∀ (a : Bool) (b c : Prop),
--   let x := a && a; let y := ! a && x;
--   ∀ (f : y → Prop → Prop),
--     if h : y then f h b else c ===>
-- ∀ (c : Prop), c
#testOptimize [ "DIteFalseCond_7" ]
  ∀ (a : Bool) (b c : Prop),
    let x := a && a; let y := ! a && x;
    ∀ (f : y → Prop → Prop),
      if h : y then f h b else c ===>
  ∀ (c : Prop), c

-- ∀ (a b : Prop) (f : False → Prop → Prop),
--   (if h : False then f h a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_8" ]
  ∀ (a b : Prop) (f : False → Prop → Prop),
    (if h : False then f h a else b) = b ===> True

-- ∀ (a b : Bool) (f : False → Bool → Bool),
--   (if h : False then f h !a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_9" ]
  ∀ (a b : Bool) (f : False → Bool → Bool),
    (if h : False then f h !a else b) = b ===> True

-- ∀ (x y z : Nat) (f : False → Nat → Nat),
--   ((if h : False then (f h x + 40) - 40 else y) < z) = (y < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_10" ]
  ∀ (x y z : Nat) (f : False → Nat → Nat),
    ((if h : False then (f h x + 40) - 40 else y) < z) = (y < z) ===> True

-- ∀ (f : False → Int → Int),
--   (if h : False then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
--   ∀ (z y : Int), z < y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_11" ]
  ∀ (f : False → Int → Int),
    (if h : False then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
    ∀ (z y : Int), z < y ===> True

-- ∀ (c : Bool) (a b : Prop) (f : (! c) && c → Prop → Prop),
--   (if h : (! c) && c then f h a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_12" ]
  ∀ (c : Bool) (a b : Prop) (f : (! c) && c → Prop → Prop),
    (if h : (! c) && c then f h a else b) = b ===> True

-- ∀ (c a b : Prop) (f : ¬ c ∧ c → Prop → Prop), [Decidable c] →
--   (if h : ¬ c ∧ c then f h a else b) = b ===> True
#testOptimize [ "DIteFalseCond_13" ]
  ∀ (c a b : Prop) (f : ¬ c ∧ c → Prop → Prop), [Decidable c] →
    (if h : ¬ c ∧ c then f h a else b) = b ===> True

-- ∀ (a : Bool) (b c : Prop),
--   let x := a && a; let y := ! a && x;
--   ∀ (f : y → Prop → Prop),
--      (if h : y then f h b else c) = c ===> True
#testOptimize [ "DIteFalseCond_14" ]
  ∀ (a : Bool) (b c : Prop),
    let x := a && a; let y := ! a && x;
    ∀ (f : y → Prop → Prop),
       (if h : y then f h b else c) = c ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
     - ``dite True (fun h : True => e1) (fun h : False => e2)` ==> e1`
     - \`dite False (fun h : True => e1) (fun h : False => e2)` ==> e2`
-/

-- ∀ (a b : Bool) (p q : Prop) (f : (! a || a) && b → Prop → Prop),
--   if h : (! a || a) && b then f h p else q ===>
-- ∀ (b : Bool) (p q : Prop) (f : true = b → Prop → Prop),
--   (false = b → q) ∧ (∀ (h : true = b), f h p)
#testOptimize [ "DIteCondUnchanged_1" ]
  ∀ (a b : Bool) (p q : Prop) (f : (! a || a) && b → Prop → Prop),
    if h : (! a || a) && b then f h p else q ===>
  ∀ (b : Bool) (p q : Prop) (f : true = b → Prop → Prop),
    (false = b → q) ∧ (∀ (h : true = b), f h p)

-- ∀ (a b c d : Bool) (f : (b && !b) || a → Bool → Bool),
--   (if h : (b && !b) || a then f h c else d) = true ===>
-- ∀ (a c d : Bool) (f : true = a → Bool → Bool),
--   (false = a → true = d) ∧ (∀ (h : true = a), true = f h c)
#testOptimize [ "DIteCondUnchanged_2" ]
  ∀ (a b c d : Bool) (f : (b && !b) || a → Bool → Bool),
    (if h : (b && !b) || a then f h c else d) = true ===>
  ∀ (a c d : Bool) (f : true = a → Bool → Bool),
    (false = a → true = d) ∧ (∀ (h : true = a), true = f h c)

-- ∀ (a b : Bool) (x y z : Nat) (f : b && (a || !a) → Nat → Nat),
--   (if h : b && (a || !a) then (f h x + 40) - 40 else y) < z ===>
-- ∀ (b : Bool) (x y z : Nat) (f : true = b → Nat → Nat),
--   Solver.dite' (true = b) (fun h : _ => f h x) (fun _ => y) < z
def diteCondUnchanged_3 : Expr :=
Lean.Expr.forallE `b
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE `h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.true []))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE `h
              (Lean.Expr.const `Nat [])
              (Lean.Expr.const `Nat [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Bool []))
                          (Lean.Expr.const `Bool.true []))
                        (Lean.Expr.bvar 4)))
                  (Lean.Expr.lam
                    `h
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 4))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam
                  `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.false []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3)
                  (Lean.BinderInfo.default))))
            (Lean.Expr.bvar 1))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteCondUnchanged_3" : term => return diteCondUnchanged_3

#testOptimize [ "DIteCondUnchanged_3" ]
  ∀ (a b : Bool) (x y z : Nat) (f : b && (a || !a) → Nat → Nat),
    (if h : b && (a || !a) then (f h x + 40) - 40 else y) < z ===> diteCondUnchanged_3

-- ∀ (a b p q : Prop) (f : (¬ a ∨ a) ∧ b → Prop → Prop), [Decidable a] → [Decidable b] →
--   if h : (¬ a ∨ a) ∧ b then f h p else q ===>
-- ∀ (b p q : Prop) (f : b → Prop → Prop), (∀ (h : b), f h p) ∧ (¬ b → q)
#testOptimize [ "DIteCondUnchanged_4" ]
  ∀ (a b p q : Prop) (f : (¬ a ∨ a) ∧ b → Prop → Prop), [Decidable a] → [Decidable b] →
    if h : (¬ a ∨ a) ∧ b then f h p else q ===>
  ∀ (b p q : Prop) (f : b → Prop → Prop), (∀ (h : b), f h p) ∧ (¬ b → q)

-- ∀ (a b : Prop) (c d : Bool) (f : (b ∧ ¬ b) ∨ a → Bool → Bool),
--   [Decidable a] → [Decidable b] → (if h : (b ∧ ¬ b) ∨ a then f h c else d) = true ===>
-- ∀ (a : Prop) (c d : Bool) (f : a → Bool → Bool),
--   (∀ (h : a), true = f h c) ∧ (¬ a → true = d)
#testOptimize [ "DIteCondUnchanged_5" ]
  ∀ (a b : Prop) (c d : Bool) (f : (b ∧ ¬ b) ∨ a → Bool → Bool),
    [Decidable a] → [Decidable b] → (if h : (b ∧ ¬ b) ∨ a then f h c else d) = true ===>
  ∀ (a : Prop) (c d : Bool) (f : a → Bool → Bool),
    (∀ (h : a), true = f h c) ∧ (¬ a → true = d)

-- ∀ (a b : Prop) (x y z : Nat) (f : b ∧ (a ∨ ¬ a) → Nat → Nat),
--   [Decidable a] → [Decidable b] → (if h : b ∧ (a ∨ ¬ a) then (f h x + 40) - 40 else y) < z ===>
-- ∀ (b : Prop) (x y z : Nat) (f : b → Nat → Nat),
--   Solver.dite' b (fun h : _ => f h x) (fun _ => y) < z
#testOptimize [ "DIteCondUnchanged_6" ]
  ∀ (a b : Prop) (x y z : Nat) (f : b ∧ (a ∨ ¬ a) → Nat → Nat),
    [Decidable a] → [Decidable b] → (if h : b ∧ (a ∨ ¬ a) then (f h x + 40) - 40 else y) < z ===>
  ∀ (b : Prop) (x y z : Nat) (f : b → Nat → Nat),
    Solver.dite' b (fun h : _ => f h x) (fun _ => y) < z


/-! Test cases for simplification rule:
       ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
         `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')`.
-/

-- ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   if h : ¬ c then f h a else b ===>
-- ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), (c → b) ∧ (∀ (h : ¬ c), f h a)
#testOptimize [ "DIteNegCond_1" ]
  ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    if h : ¬ c then f h a else b ===>
  ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), (c → b) ∧ (∀ (h : ¬ c), f h a)

-- ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
--   (if h : ¬ c then f h a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool),
--   (c → true = b) ∧ (∀ (h : ¬ c), true = f h a)
#testOptimize [ "DIteNegCond_2" ]
  ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
    (if h : ¬ c then f h a else b) = true ===>
  ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool),
    (c → true = b) ∧ (∀ (h : ¬ c), true = f h a)

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : ¬ c then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
--   Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z
#testOptimize [ "DIteNegCond_3" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
    (if h : ¬ c then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
    Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z

-- ∀ (c : Prop) (f : ¬ c → Int → Int), [Decidable c] →
--   if h : ¬ c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop) (f : ¬ c → Int → Int),
--   (c → ∀ (z y : Int), z < y) ∧ (∀ (h : ¬ c), ∀ (x y : Int), y < f h x)
#testOptimize [ "DIteNegCond_4" ]
  ∀ (c : Prop) (f : ¬ c → Int → Int), [Decidable c] →
    if h : ¬ c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Prop) (f : ¬ c → Int → Int),
    (c → ∀ (z y : Int), z < y) ∧ (∀ (h : ¬ c), ∀ (x y : Int), y < f h x)

-- ∀ (c : Prop) (x y : Int) (f : c = False → Int → Int), [Decidable c] →
--   (if h : c = False then f h x else y) > x ===>
-- ∀ (c : Prop) (x y : Int) (f : ¬ c → Int → Int),
--   x < Solver.dite' c (fun _ => y) (fun h : _ => f h x)
#testOptimize [ "DIteNegCond_5" ]
  ∀ (c : Prop) (x y : Int) (f : c = False → Int → Int), [Decidable c] →
    (if h : c = False then f h x else y) > x ===>
  ∀ (c : Prop) (x y : Int) (f : ¬ c → Int → Int),
    x < Solver.dite' c (fun _ => y) (fun h : _ => f h x)

-- ∀ (a b : Prop) (x y : Int) (f : ¬ (a = b) → Int → Int), [Decidable a] → [Decidable b] →
--   (if h : ¬ (a = b) then f h x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int) (f : ¬ (a = b) → Int → Int),
--   x < Solver.dite' (a = b) (fun _ => y) (fun h : _ => f h x)
#testOptimize [ "DIteNegCond_6" ]
  ∀ (a b : Prop) (x y : Int) (f : ¬ (a = b) → Int → Int), [Decidable a] → [Decidable b] →
    (if h : ¬ (a = b) then f h x else y) > x ===>
  ∀ (a b : Prop) (x y : Int) (f : ¬ (a = b) → Int → Int),
    x < Solver.dite' (a = b) (fun _ => y) (fun h : _ => f h x)

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ (¬ c)) → Nat → Nat), [Decidable c] →
--   (if h : ¬ (¬ (¬ c)) then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
--   Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z
#testOptimize [ "DIteNegCond_7" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ (¬ c)) → Nat → Nat), [Decidable c] →
    (if h : ¬ (¬ (¬ c)) then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
    Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z

-- ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : ¬ c then f h a else b) = if h : c then b else f h a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_8" ]
  ∀ (a b c : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : ¬ c then f h a else b) = if h : c then b else f h a ===> True

-- ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
--   (if h : ¬ c then f h a else b) = (if h : c then b else f h a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_9" ]
  ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
    (if h : ¬ c then f h a else b) = (if h : c then b else f h a) ===> True

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
--   ((if h : ¬ c then f h x else y) < z) = ((if h : c then y else f h x) < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_10" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
    ((if h : ¬ c then f h x else y) < z) = ((if h : c then y else f h x) < z) ===> True

-- ∀ (c : Prop) (f : ¬ c → Int → Int), [Decidable c] →
--   (if h : ¬ c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
--   (if h : c then ∀ (z y : Int), y > z else ∀ (x y : Int), f h x > y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_11" ]
  ∀ (c : Prop) (f : ¬ c → Int → Int), [Decidable c] →
    (if h : ¬ c then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
    (if h : c then ∀ (z y : Int), y > z else ∀ (x y : Int), f h x > y) ===> True

-- ∀ (c : Prop) (x y : Int), [Decidable c] →
--   (∀ (f : c = False → Int → Int), ((if h : c = False then f h x else y) > x)) =
--   ∀ (g : ¬ c → Int → Int), (x < (if h : c then y else g h x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_12" ]
  ∀ (c : Prop) (x y : Int), [Decidable c] →
    (∀ (f : c = False → Int → Int), ((if h : c = False then f h x else y) > x)) =
    ∀ (g : ¬ c → Int → Int), (x < (if h : c then y else g h x)) ===> True

-- ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
--   (∀ (f : ¬ (a = b) → Int → Int), (if h : ¬ (a = b) then f h x else y) > x) =
--   (∀ (g : ¬ (a = b) → Int → Int), x < (if h : (a = b) then y else g h x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_13" ]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
    (∀ (f : ¬ (a = b) → Int → Int), (if h : ¬ (a = b) then f h x else y) > x) =
    (∀ (g : ¬ (a = b) → Int → Int), x < (if h : (a = b) then y else g h x)) ===> True

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] →
--   (∀ (f : ¬ (¬ (¬ c)) → Nat → Nat), (if h : ¬ (¬ (¬ c)) then f h x else y) < z) =
--   (∀ (g : ¬ c → Nat → Nat), (if h : c then y else g h x) < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_14" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] →
    (∀ (f : ¬ (¬ (¬ c)) → Nat → Nat), (if h : ¬ (¬ (¬ c)) then f h x else y) < z) =
    (∀ (g : ¬ c → Nat → Nat), (if h : c then y else g h x) < z) ===> True


/-! Test cases to ensure that simplification rule:
       `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
       `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')`
    is not applied wrongly.
-/

-- ∀ (a b c : Prop) (f : ¬ (¬ c) → Prop → Prop), [Decidable c] →
--     if h : ¬ (¬ c) then f h a else b ===>
-- ∀ (a b c : Prop) (f : c → Prop → Prop), (∀ (h : c), f h a) ∧ (¬ c → b)
#testOptimize [ "DIteNegCondUnchanged_1" ]
  ∀ (a b c : Prop) (f : ¬ (¬ c) → Prop → Prop), [Decidable c] →
      if h : ¬ (¬ c) then f h a else b ===>
  ∀ (a b c : Prop) (f : c → Prop → Prop), (∀ (h : c), f h a) ∧ (¬ c → b)

-- ∀ (c : Prop) (a b : Bool) (f : ¬ (¬ c) → Bool → Bool), [Decidable c] →
--   (if h : ¬ (¬ c) then f h a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool),
--   (∀ (h : c), true = f h a) ∧ (¬ c → true = b)
#testOptimize [ "DIteNegCondUnchanged_2" ]
  ∀ (c : Prop) (a b : Bool) (f : ¬ (¬ c) → Bool → Bool), [Decidable c] →
    (if h : ¬ (¬ c) then f h a else b) = true ===>
  ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool),
    (∀ (h : c), true = f h a) ∧ (¬ c → true = b)

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ c) → Nat → Nat), [Decidable c] →
--   (if h : ¬ (¬ c) then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
--   Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z
#testOptimize [ "DIteNegCondUnchanged_3" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ c) → Nat → Nat), [Decidable c] →
    (if h : ¬ (¬ c) then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
    Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z

-- ∀ (c : Prop) (f : ¬ (¬ c) → Int → Int), [Decidable c] →
--   if h : ¬ (¬ c) then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop) (f : c → Int → Int),
--   (∀ (h : c), ∀ (x y : Int), y < f h x) ∧ (¬ c → ∀ (z y : Int), z < y)
#testOptimize [ "DIteNegCondUnchanged_4" ]
  ∀ (c : Prop) (f : ¬ (¬ c) → Int → Int), [Decidable c] →
    if h : ¬ (¬ c) then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Prop) (f : c → Int → Int),
    (∀ (h : c), ∀ (x y : Int), y < f h x) ∧ (¬ c → ∀ (z y : Int), z < y)

-- ∀ (c : Prop) (x y : Int) (f : c = True → Int → Int), [Decidable c] →
--   (if h : c = True then f h x else y) > x ===>
-- ∀ (c : Prop) (x y : Int) (f : c → Int → Int),
--   x < Solver.dite' c (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteNegCondUnchanged_5" ]
  ∀ (c : Prop) (x y : Int) (f : c = True → Int → Int), [Decidable c] →
    (if h : c = True then f h x else y) > x ===>
  ∀ (c : Prop) (x y : Int) (f : c → Int → Int),
    x < Solver.dite' c (fun h : _ => f h x) (fun _ => y)

-- ∀ (a b : Prop) (x y : Int) (f : ¬ (¬ (a = b)) → Int → Int),
--   [Decidable a] → [Decidable b] →
--   (if h : ¬ (¬ (a = b)) then f h x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int) (f : a = b → Int → Int),
--   x < Solver.dite' (a = b) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteNegCondUnchanged_6" ]
  ∀ (a b : Prop) (x y : Int) (f : ¬ (¬ (a = b)) → Int → Int),
    [Decidable a] → [Decidable b] →
    (if h : ¬ (¬ (a = b)) then f h x else y) > x ===>
  ∀ (a b : Prop) (x y : Int) (f : a = b → Int → Int),
    x < Solver.dite' (a = b) (fun h : _ => f h x) (fun _ => y)

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ (¬ (¬ c))) → Nat → Nat), [Decidable c] →
--   (if h : ¬ (¬ (¬ (¬ c))) then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
--   Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z
#testOptimize [ "DIteNegCondUnchanged_7" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ (¬ (¬ (¬ c))) → Nat → Nat), [Decidable c] →
    (if h : ¬ (¬ (¬ (¬ c))) then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
    Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z


/-! Test cases for simplification rule
    ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
         `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')`.
-/

-- ∀ (c : Bool) (p q : Prop) (f : c = false → Prop → Prop),
--   if h : c = false then f h p else q ===>
-- ∀ (c : Bool) (p q : Prop) (f : false = c → Prop → Prop),
--   (∀ (h : false = c), f h p) ∧ (true = c → q)
#testOptimize [ "DIteFalseEqCond_1" ]
  ∀ (c : Bool) (p q : Prop) (f : c = false → Prop → Prop),
    if h : c = false then f h p else q ===>
  ∀ (c : Bool) (p q : Prop) (f : false = c → Prop → Prop),
    (∀ (h : false = c), f h p) ∧ (true = c → q)

-- ∀ (a b c : Bool) (f : c = false → Bool → Bool),
--   (if h : c = false then f h a else b) = true ===>
-- ∀ (a b c : Bool) (f : false = c → Bool → Bool),
--   (∀ (h : false = c), true = f h a) ∧ (true = c → true = b)
#testOptimize [ "DIteFalseEqCond_2" ]
  ∀ (a b c : Bool) (f : c = false → Bool → Bool),
    (if h : c = false then f h a else b) = true ===>
  ∀ (a b c : Bool) (f : false = c → Bool → Bool),
    (∀ (h : false = c), true = f h a) ∧ (true = c → true = b)

--  ∀ (c : Bool) (x y : Nat) (f : c = false → Nat → Nat),
--   (if h : c = false then f h x else y) > x ===>
--  ∀ (c : Bool) (x y : Nat) (f : c = false → Nat → Nat),
--    Solver.dite' (true = c) (fun _ => y) (fun h : _ => f h x) > x
def diteFalseEqCond_3 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.false []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Nat [])
            (Lean.Expr.const `Nat [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_3" : term => return diteFalseEqCond_3

#testOptimize [ "DIteFalseEqCond_3" ]
  ∀ (c : Bool) (x y : Nat) (f : c = false → Nat → Nat),
    (if h : c = false then f h x else y) > x ===> diteFalseEqCond_3

-- ∀ (c : Bool) (f : c = false → Int → Int),
--   if h : c = false then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool) (f : false = c → Int → Int),
--   (∀ (h : false = c), ∀ (x y : Int), y < f h x) ∧ (true = c → ∀ (z y : Int), z < y)
#testOptimize [ "DIteFalseEqCond_4" ]
  ∀ (c : Bool) (f : c = false → Int → Int),
    if h : c = false then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool) (f : false = c → Int → Int),
    (∀ (h : false = c), ∀ (x y : Int), y < f h x) ∧ (true = c → ∀ (z y : Int), z < y)

def diteFalseEqCond_5 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.false []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_5" : term => return diteFalseEqCond_5

-- ∀ (c : Bool) (x y : Int) (f : !c → Int → Int), (if h : !c then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : false = c → Int → Int),
--  x < Solver.dite' (true = c) (fun _ => y) (fun h : _ => f h x)
#testOptimize [ "DIteFalseEqCond_5" ]
  ∀ (c : Bool) (x y : Int) (f : !c → Int → Int), (if h : !c then f h x else y) > x ===> diteFalseEqCond_5

-- ∀ (c : Bool) (x y : Int) (f : c == false → Int → Int),
--   (if h : c == false then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : false = c → Int → Int),
--   x < (if h : true = c then y else f h x)
#testOptimize [ "DIteFalseEqCond_6" ]
  ∀ (c : Bool) (x y : Int) (f : c == false → Int → Int),
    (if h : c == false then f h x else y) > x ===> diteFalseEqCond_5

-- ∀ (c : Bool) (x y : Int) (f : ! (! (! c)) → Int → Int),
--   (if h : ! (! (! c)) then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : false = c → Int → Int),
--   x < (if h : true = c then y else f h x)
#testOptimize [ "DIteFalseEqCond_7" ]
  ∀ (c : Bool) (x y : Int) (f : ! (! (! c)) → Int → Int),
    (if h : ! (! (! c)) then f h x else y) > x ===> diteFalseEqCond_5

def diteFalseEqCond_8 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.false []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_8" : term => return diteFalseEqCond_8

-- ∀ (a b : Bool) (x y : Int) (f : a = (! b && b) → Int → Int),
--  (if h : a = (! b && b) then f h x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int) (f : false = a → Int → Int),
-- ∀ (a : Bool) (x y : Int), x < Solver.dite' (true = a) (fun _ => y) (fun h : _ => f h x)
#testOptimize [ "DIteFalseEqCond_8" ]
  ∀ (a b : Bool) (x y : Int) (f : a = (! b && b) → Int → Int),
    (if h : a = (! b && b) then f h x else y) > x ===> diteFalseEqCond_8

def diteFalseEqCond_9 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `n
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.false []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_9" : term => return diteFalseEqCond_9

-- ∀ (a : Bool) (m n : Int),
--   let x := a || a; let y := ! a || ! x;
--   ∀ (f : y → Int → Int),
--     (if h : y then f h m else n) > m ===>
-- ∀ (a : Bool) (m n : Int) (f : false = a → Int → Int),
--   m < Solver.dite' (true = a) (fun _ => n) (fun h : _ => f h m)
#testOptimize [ "DIteFalseEqCond_9" ]
  ∀ (a : Bool) (m n : Int),
    let x := a || a; let y := ! a || ! x;
    ∀ (f : y → Int → Int),
      (if h : y then f h m else n) > m ===> diteFalseEqCond_9


-- ∀ (c : Bool) (p q : Prop) (f : ¬ c = true → Prop → Prop),
--   (if h : ¬ c = true then f h p else q) = if h : c = true then q else f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_10" ]
  ∀ (c : Bool) (p q : Prop) (f : ¬ c = true → Prop → Prop),
    (if h : ¬ c = true then f h p else q) = if h : c = true then q else f h p ===> True

-- ∀ (a b c : Bool) (f : ¬ c = true → Bool → Bool),
--   (if h : ¬ c = true then f h a else b) = if h : c = true then b else f h a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_11" ]
  ∀ (a b c : Bool) (f : ¬ c = true → Bool → Bool),
    (if h : ¬ c = true then f h a else b) = if h : c = true then b else f h a ===> True

-- ∀ (c : Bool) (x y : Nat) (f : ¬ c = true → Nat → Nat),
--   ((if h : ¬ c = true then f h x else y) > x) = (x < (if h : c = true then y else f h x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_12" ]
  ∀ (c : Bool) (x y : Nat) (f : ¬ c = true → Nat → Nat),
    ((if h : ¬ c = true then f h x else y) > x) = (x < (if h : c = true then y else f h x)) ===> True

-- ∀ (c : Bool) (f : ¬ c = true → Int → Int),
--   (if h : ¬ c = true then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
--   if h : c = true then ∀ (z y : Int), z < y else ∀ (x y : Int), y < f h x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_13" ]
  ∀ (c : Bool) (f : ¬ c = true → Int → Int),
    (if h : ¬ c = true then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z) =
    if h : c = true then ∀ (z y : Int), z < y else ∀ (x y : Int), y < f h x ===> True


-- ∀ (c : Prop) (x y : Int) (f : ¬ c → Int → Int), [Decidable c] →
--   ((if h : ¬ c then f h x else y) > x) = (x < (if h : c then y else f h x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_14" ]
  ∀ (c : Prop) (x y : Int) (f : ¬ c → Int → Int), [Decidable c] →
    ((if h : ¬ c then f h x else y) > x) = (x < (if h : c then y else f h x)) ===> True

-- ∀ (c : Bool) (x y : Int) (f : ¬ c == true → Int → Int),
--   ((if h : ¬ c == true then f h x else y) > x) = (x < (if h : c == true then y else f h x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_15" ]
  ∀ (c : Bool) (x y : Int) (f : ¬ c == true → Int → Int),
    ((if h : ¬ c == true then f h x else y) > x) = (x < (if h : c == true then y else f h x)) ===> True

-- ∀ (c : Bool) (x y : Int) (f : ¬ ! (! (! c)) → Int → Int),
--   ((if h : ! (! (! c)) then x else f h y) > x) = (x < (if h : ¬ ! (! (! c)) then f h y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_16" ]
  ∀ (c : Bool) (x y : Int) (f : ¬ ! (! (! c)) → Int → Int),
    ((if h : ! (! (! c)) then x else f h y) > x) = (x < (if h : ¬ ! (! (! c)) then f h y else x)) ===> True

-- ∀ (a b : Bool) (x y : Int),
--    let c := a = (! b && b);
--    ∀ (f : ¬ c → Int → Int),
--    ((if h : c then x else f h y) > x) = (x < (if h : ¬ c then f h y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_17" ]
  ∀ (a b : Bool) (x y : Int),
     let c := a = (! b && b);
     ∀ (f : ¬ c → Int → Int),
     ((if h : c then x else f h y) > x) = (x < (if h : ¬ c then f h y else x)) ===> True

-- ∀ (a : Bool) (m n : Int),
--   let x := a || a; let y := ! a || ! x;
--   ∀ (f : ¬ y → Int → Int),
--   ((if h : y then m else f h n) > m) = (m < (if h : ¬ y then f h n else m)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_18" ]
  ∀ (a : Bool) (m n : Int),
    let x := a || a; let y := ! a || ! x;
    ∀ (f : ¬ y → Int → Int),
    ((if h : y then m else f h n) > m) = (m < (if h : ¬ y then f h n else m)) ===> True


/-! Test cases to ensure that simplification rule
       `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
          `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')`
    is not applied wrongly.
-/

-- ∀ (c : Bool) (p q : Prop) (f : c = true → Prop → Prop),
--   (if h : c = true then f h p else q) ===>
-- ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
--   (false = c → q) ∧ ∀ (h : true = c), f h p
#testOptimize [ "DIteFalseEqCondUnchanged_1" ]
  ∀ (c : Bool) (p q : Prop) (f : c = true → Prop → Prop),
    (if h : c = true then f h p else q) ===>
  ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
    (false = c → q) ∧ ∀ (h : true = c), f h p

-- ∀ (a b c : Bool) (f : c = true → Bool → Bool),
--   (if h : c = true then f h a else b) = true ===>
-- ∀ (a b c : Bool) (f : true = c → Bool → Bool),
--   (false = c → true = b) ∧ ∀ (h : true = c), true = f h a
#testOptimize [ "DIteFalseEqCondUnchanged_2" ]
  ∀ (a b c : Bool) (f : c = true → Bool → Bool),
    (if h : c = true then f h a else b) = true ===>
  ∀ (a b c : Bool) (f : true = c → Bool → Bool),
    (false = c → true = b) ∧ ∀ (h : true = c), true = f h a

def diteFalseEqCondUnchanged_3 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.true []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Nat [])
            (Lean.Expr.const `Nat [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_3" : term => return diteFalseEqCondUnchanged_3

-- ∀ (c : Bool) (x y : Nat) (f : c = true → Nat → Nat),
--  (if h : c = true then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat) (f : true = c → Nat → Nat),
--  x < Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_3" ]
  ∀ (c : Bool) (x y : Nat) (f : c = true → Nat → Nat),
    (if h : c = true then f h x else y) > x ===> diteFalseEqCondUnchanged_3

-- ∀ (c : Bool) (f : c = true → Int → Int),
--   if h : c = true then ∀ (x y : Int), x > f h y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool) (f : true = c → Int → Int),
--   (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), f h y < x)
#testOptimize [ "DIteFalseEqCondUnchanged_4" ]
  ∀ (c : Bool) (f : c = true → Int → Int),
    if h : c = true then ∀ (x y : Int), x > f h y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool) (f : true = c → Int → Int),
    (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), f h y < x)

-- ∀ (a b : Bool) (p q : Prop) (f : a = b → Prop → Prop),
--   (if h : a = b then f h p else q) ===>
-- ∀ (a b : Bool) (p q : Prop) (f : a = b → Prop → Prop),
--   (¬ (a = b) → q) ∧ ∀ (h : a = b), f h p
#testOptimize [ "DIteFalseEqCondUnchanged_5" ]
  ∀ (a b : Bool) (p q : Prop) (f : a = b → Prop → Prop),
    (if h : a = b then f h p else q) ===>
  ∀ (a b : Bool) (p q : Prop) (f : a = b → Prop → Prop),
    (¬ (a = b) → q) ∧ ∀ (h : a = b), f h p

-- ∀ (a b c d : Bool) (f : a = b → Bool → Bool),
--   (if h : a = b then f h c else d) = true ===>
-- ∀ (a b c d : Bool) (f : a = b → Bool → Bool),
--   (¬ (a = b) → true = d) ∧ ∀ (h : a = b), true = f h c
#testOptimize [ "DIteFalseEqCondUnchanged_6" ]
  ∀ (a b c d : Bool) (f : a = b → Bool → Bool),
    (if h : a = b then f h c else d) = true ===>
  ∀ (a b c d : Bool) (f : a = b → Bool → Bool),
    (¬ (a = b) → true = d) ∧ ∀ (h : a = b), true = f h c

-- ∀ (a b : Bool) (x y : Nat) (f : a = b → Nat → Nat),
--   (if h : a = b then f h x else y) > x ===>
-- ∀ (a b : Bool) (x y : Nat) (f : a = b → Nat → Nat),
--   x < Solver.dite' (a = b) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_7" ]
  ∀ (a b : Bool) (x y : Nat) (f : a = b → Nat → Nat),
    (if h : a = b then f h x else y) > x ===>
  ∀ (a b : Bool) (x y : Nat) (f : a = b → Nat → Nat),
    x < Solver.dite' (a = b) (fun h : _ => f h x) (fun _ => y)

-- ∀ (c : Bool) (f : c = true → Int → Int),
--   if h : c = true then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool) (f : true = c → Int → Int),
--   (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), y < f h x)
#testOptimize [ "DIteFalseEqCondUnchanged_8" ]
  ∀ (c : Bool) (f : c = true → Int → Int),
    if h : c = true then ∀ (x y : Int), f h x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool) (f : true = c → Int → Int),
    (false = c → ∀ (z y : Int), z < y) ∧ (∀ (h : true = c), ∀ (x y : Int), y < f h x)

def diteFalseEqCondUnchanged_9 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.true []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_9" : term => return diteFalseEqCondUnchanged_9

-- ∀ (c : Bool) (x y : Int) (f : !(!c) → Int → Int), (if h : !(!c) then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
--  x < Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_9" ]
  ∀ (c : Bool) (x y : Int) (f : !(!c) → Int → Int),
    (if h : !(!c) then f h x else y) > x ===> diteFalseEqCondUnchanged_9

-- ∀ (c : Bool) (x y : Int) (f : c == true → Int → Int), (if h : c == true then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
--   x < Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_10" ]
  ∀ (c : Bool) (x y : Int) (f : c == true → Int → Int),
    (if h : c == true then f h x else y) > x ===> diteFalseEqCondUnchanged_9

-- ∀ (c : Bool) (x y : Int) (f : !(!(! (! c))) → Int → Int),
--  (if h : !(!(! (! c))) then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
--   x < Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_11" ]
  ∀ (c : Bool) (x y : Int) (f : !(!(! (! c))) → Int → Int),
    (if h : !(! (! (! c))) then f h x else y) > x ===> diteFalseEqCondUnchanged_9

def diteFalseEqCondUnchanged_12 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.true []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_12" : term => return diteFalseEqCondUnchanged_12

-- ∀ (a b : Bool) (x y : Int) (f : a = (! b || b) → Int → Int),
--  (if h : a = (! b || b) then f h x else y) > x ===>
-- ∀ (a : Bool) (x y : Int) (f : true = a → Int → Int),
--  x < Solver.dite' (true = a) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteFalseEqCondUnchanged_12" ]
  ∀ (a b : Bool) (x y : Int) (f : a = (! b || b) → Int → Int),
    (if h : a = (! b || b) then f h x else y) > x ===> diteFalseEqCondUnchanged_12

def diteFalseEqCondUnchanged_13 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `n
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h1
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.true []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h2
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_13" : term => return diteFalseEqCondUnchanged_13

-- ∀ (a : Bool) (m n : Int),
--   let x := a && a; let y := a || x;
--   ∀ (f : y → Int → Int),
--     (if h : y then f h m else n) > m ===>
-- ∀ (a : Bool) (m n : Int) (f : true = a → Int → Int),
--  m < Solver.dite' (true = a) (fun h : _ => f h m) (fun _ => n)
#testOptimize [ "DIteFalseEqCondUnchanged_13" ]
  ∀ (a : Bool) (m n : Int),
    let x := a && a; let y := a || x;
    ∀ (f : y → Int → Int),
      (if h : y then f h m else n) > m ===> diteFalseEqCondUnchanged_13


/-! Test cases for simplification rule ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`. -/

-- ∀ (c p q : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then f h p else q ===>
-- ∀ (c p q : Prop) (f : c → Prop → Prop),
--   (∀ (h : c), f h p) ∧ (¬ c → q)
#testOptimize [ "DIteToPropExpr_1" ]
  ∀ (c p q : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then f h p else q ===>
  ∀ (c p q : Prop) (f : c → Prop → Prop),
    (∀ (h : c), f h p) ∧ (¬ c → q)

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   if h : c then True else f h p ===>
-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop) (h : ¬ c), f h p
#testOptimize [ "DIteToPropExpr_2" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    if h : c then True else f h p ===>
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop) (h : ¬ c), f h p

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then f h p else True ===>
-- ∀ (c p : Prop) (f : c → Prop → Prop) (h : c), f h p
#testOptimize [ "DIteToPropExpr_3" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then f h p else True ===>
  ∀ (c p : Prop) (f : c → Prop → Prop) (h : c), f h p


-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   if h : c then False else f h p ===>
-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), ¬ c ∧ ∀ (h : ¬ c), f h p
#testOptimize [ "DIteToPropExpr_4" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    if h : c then False else f h p ===>
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), ¬ c ∧ ∀ (h : ¬ c), f h p

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then f h p else False ===>
-- ∀ (c p : Prop) (f : c → Prop → Prop), c ∧ ∀ (h : c), f h p
#testOptimize [ "DIteToPropExpr_5" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then f h p else False ===>
  ∀ (c p : Prop) (f : c → Prop → Prop), c ∧ ∀ (h : c), f h p

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--  if h : c then c else f h p ===>
-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop) (h : ¬ c), f h p
#testOptimize [ "DIteToPropExpr_6" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
   if h : c then c else f h p ===>
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop) (h : ¬ c), f h p

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then f h p else c ===>
-- ∀ (c p : Prop) (f : c → Prop → Prop), c ∧ ∀ (h : c), f h p
#testOptimize [ "DIteToPropExpr_7" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then f h p else c ===>
  ∀ (c p : Prop) (f : c → Prop → Prop), c ∧ ∀ (h : c), f h p

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   if h : c then ¬ c else f h p ===>
-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), ¬ c ∧ ∀ (h : ¬ c), f h p
#testOptimize [ "DIteToPropExpr_8" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    if h : c then ¬ c else f h p ===>
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), ¬ c ∧ ∀ (h : ¬ c), f h p

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   if h : c then f h p else ¬ c ===>
-- ∀ (c p : Prop) (f : c → Prop → Prop) (h : c), f h p
#testOptimize [ "DIteToPropExpr_9" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    if h : c then f h p else ¬ c ===>
  ∀ (c p : Prop) (f : c → Prop → Prop) (h : c), f h p

-- ∀ (c p q : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   if h : ¬ c then f h p else q ===>
-- ∀ (c p q : Prop) (f : ¬ c → Prop → Prop),
--   (c → q) ∧ ∀ (h : ¬ c), f h p
#testOptimize [ "DIteToPropExpr_10" ]
  ∀ (c p q : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    if h : ¬ c then f h p else q ===>
  ∀ (c p q : Prop) (f : ¬ c → Prop → Prop),
    (c → q) ∧ ∀ (h : ¬ c), f h p

-- ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop),
--   if h : c then f h p else q ===>
-- ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
--   (false = c → q) ∧ ∀ (h : true = c), f h p
#testOptimize [ "DIteToPropExpr_11" ]
  ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop),
    if h : c then f h p else q ===>
  ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
    (false = c → q) ∧ ∀ (h : true = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then True else f h p ===>
-- ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop) (h : false = c), f h p
#testOptimize [ "DIteToPropExpr_12" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    if h : c then True else f h p ===>
  ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop) (h : false = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   if h : c then f h p else True ===>
-- ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop) (h : true = c), f h p
#testOptimize [ "DIteToPropExpr_13" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    if h : c then f h p else True ===>
  ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop) (h : true = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then False else f h p ===>
-- ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop),
--   false = c ∧ ∀ (h : false = c), f h p
#testOptimize [ "DIteToPropExpr_14" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    if h : c then False else f h p ===>
  ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop),
    false = c ∧ ∀ (h : false = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   if h : c then f h p else False ===>
-- ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop),
--   true = c ∧ ∀ (h : true = c), f h p
#testOptimize [ "DIteToPropExpr_15" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    if h : c then f h p else False ===>
  ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop),
    true = c ∧ ∀ (h : true = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then c else f h p ===>
-- ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop)
--   (h : false = c), f h p
#testOptimize [ "DIteToPropExpr_16" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    if h : c then c else f h p ===>
  ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop)
    (h : false = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   if h : c then f h p else c ===>
-- ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop),
--   true = c ∧ ∀ (h : true = c), f h p
#testOptimize [ "DIteToPropExpr_17" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    if h : c then f h p else c ===>
  ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop),
    true = c ∧ ∀ (h : true = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   if h : c then !c else f h p ===>
-- ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop),
--    false = c ∧ ∀ (h : false = c), f h p
#testOptimize [ "DIteToPropExpr_18" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    if h : c then !c else f h p ===>
  ∀ (c : Bool) (p : Prop) (f : false = c → Prop → Prop),
     false = c ∧ ∀ (h : false = c), f h p

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   if h : c then f h p else !c ===>
-- ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop)
--   (h : true = c), f h p
#testOptimize [ "DIteToPropExpr_19" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    if h : c then f h p else !c ===>
  ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop)
    (h : true = c), f h p

-- ∀ (c : Bool) (p q : Prop) (f : !c → Prop → Prop),
--   if h : !c then f h p else q ===>
-- ∀ (c : Bool) (p q : Prop) (f : false = c → Prop → Prop),
--   (∀ (h : false = c), f h p) ∧ (true = c → q)
#testOptimize [ "DIteToPropExpr_20" ]
  ∀ (c : Bool) (p q : Prop) (f : !c → Prop → Prop),
    if h : !c then f h p else q ===>
  ∀ (c : Bool) (p q : Prop) (f : false = c → Prop → Prop),
    (∀ (h : false = c), f h p) ∧ (true = c → q)

-- ∀ (c p q : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then f h p else q) = ((¬ c → q) ∧ ∀ (h : c), f h p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_21" ]
  ∀ (c p q : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then f h p else q) = ((¬ c → q) ∧ ∀ (h : c), f h p) ===> True

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : c then True else f h p) = ∀ (h : ¬ c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_22" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : c then True else f h p) = ∀ (h : ¬ c), f h p ===> True

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then f h p else True) = ∀ (h : c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_23" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then f h p else True) = ∀ (h : c), f h p ===> True

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : c then False else f h p) = ((c → False) ∧ ∀ (h : ¬ c), f h p) ===> True
#testOptimize [ "DIteToPropExpr_24" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : c then False else f h p) = ((c → False) ∧ ∀ (h : ¬ c), f h p) ===> True

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then f h p else False) = ((∀ (h : c), f h p) ∧ (¬ c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_25" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then f h p else False) = ((∀ (h : c), f h p) ∧ (¬ c → False)) ===> True

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : c then c else f h p) = ∀ (h : ¬ c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_26" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : c then c else f h p) = ∀ (h : ¬ c), f h p ===> True

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then f h p else c) = (c ∧ ∀ (h : c), f h p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_27" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then f h p else c) = (c ∧ ∀ (h : c), f h p) ===> True

-- ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : c then ¬ c else f h p) = ((∀ (h : ¬ c), f h p) ∧ ¬ c) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_28" ]
  ∀ (c p : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : c then ¬ c else f h p) = ((∀ (h : ¬ c), f h p) ∧ ¬ c) ===> True

-- ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
--   (if h : c then f h p else ¬ c) = ∀ (h : c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_29" ]
  ∀ (c p : Prop) (f : c → Prop → Prop), [Decidable c] →
    (if h : c then f h p else ¬ c) = ∀ (h : c), f h p ===> True

-- ∀ (c p q : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
--   (if h : ¬ c then f h p else q) = ((∀ (h :¬ c), f h p) ∧ (c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_30" ]
  ∀ (c p q : Prop) (f : ¬ c → Prop → Prop), [Decidable c] →
    (if h : ¬ c then f h p else q) = ((∀ (h :¬ c), f h p) ∧ (c → q)) ===> True

-- ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop),
--   (if h : c then f h p else q) = ((∀ (h : c), f h p) ∧ (false = c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_31" ]
  ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop),
    (if h : c then f h p else q) = ((∀ (h : c), f h p) ∧ (false = c → q)) ===> True

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   (if h : c then True else f h p) = ∀ (h : ¬ c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_32" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    (if h : c then True else f h p) = ∀ (h : ¬ c), f h p ===> True

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   (if h : c then f h p else True) = ∀ (h : c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_33" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    (if h : c then f h p else True) = ∀ (h : c), f h p ===> True

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--    (if h : c then False else f h p) = ((∀ (h : ¬ c), f h p) ∧ (true = c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_34" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
     (if h : c then False else f h p) = ((∀ (h : ¬ c), f h p) ∧ (true = c → False)) ===> True

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--    (if h : c then f h p else False) = ((false = c → False) ∧ ∀ (h : c), f h p) ===> True
#testOptimize [ "DIteToPropExpr_35" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
     (if h : c then f h p else False) = ((false = c → False) ∧ ∀ (h : c), f h p) ===> True

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   (if h : c then true = c else f h p) = ∀ (h : ¬ c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_36" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    (if h : c then true = c else f h p) = ∀ (h : ¬ c), f h p ===> True

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--   (if h : c then f h p else c) = ((∀ (h : c), f h p) ∧ (true = c)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_37" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
    (if h : c then f h p else c) = ((∀ (h : c), f h p) ∧ (true = c)) ===> True

-- ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
--   (if h : c then true = !c else f h p) =
--   ((false = c) ∧ ∀ (h : ¬ c), f h p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_38" ]
  ∀ (c : Bool) (p : Prop) (f : ¬ c → Prop → Prop),
    (if h : c then true = !c else f h p) =
    ((false = c) ∧ ∀ (h : ¬ c), f h p) ===> True

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
--      (if h : c then f h p else true = !c) = ∀ (h : c), f h p ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_39" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop),
       (if h : c then f h p else true = !c) = ∀ (h : c), f h p ===> True

-- ∀ (c : Bool) (p q : Prop) (f : !c → Prop → Prop),
--   (if h : !c then f h p else q) = ((true = c → q) ∧ ∀ (h : !c), f h p) ===> True
#testOptimize [ "DIteToPropExpr_40" ]
  ∀ (c : Bool) (p q : Prop) (f : !c → Prop → Prop),
    (if h : !c then f h p else q) = ((true = c → q) ∧ ∀ (h : !c), f h p) ===> True


/-! Test cases to ensure that simplification rule
      `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`
    is not applied wrongly.
 -/

-- ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat), [Decidable c] →
--   (if h : c then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
--   Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z
#testOptimize [ "DIteToPropExprUnchanged_1" ]
  ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat), [Decidable c] →
    (if h : c then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : c → Nat → Nat),
    Solver.dite' c (fun h : _ => f h x) (fun _ => y) < z


def dIteToPropExprUnchanged_2 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE `h1
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.true []))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE `h2
              (Lean.Expr.const `Nat [])
              (Lean.Expr.const `Nat [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Bool []))
                          (Lean.Expr.const `Bool.true []))
                        (Lean.Expr.bvar 4)))
                  (Lean.Expr.lam `h
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 4))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.false []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3)
                  (Lean.BinderInfo.default))))
            (Lean.Expr.bvar 1))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_2" : term => return dIteToPropExprUnchanged_2

-- ∀ (c : Bool) (x y z : Nat) (f : c → Nat → Nat),
--   (if h : c then f h x else y) < z ===>
-- ∀ (c : Bool) (x y z : Nat) (f : true = c → Nat → Nat),
--  Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y) < z
#testOptimize [ "DIteToPropExprUnchanged_2" ]
  ∀ (c : Bool) (x y z : Nat) (f : c → Nat → Nat),
   (if h : c then f h x else y) < z ===> dIteToPropExprUnchanged_2

-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
--   (if h : ¬ c then f h x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
--   Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z
#testOptimize [ "DIteToPropExprUnchanged_3" ]
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat), [Decidable c] →
    (if h : ¬ c then f h x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat) (f : ¬ c → Nat → Nat),
    Solver.dite' c (fun _ => y) (fun h : _ => f h x) < z

def dIteToPropExprUnchanged_4 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE `h1
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE `h2
              (Lean.Expr.const `Nat [])
              (Lean.Expr.const `Nat [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Bool []))
                          (Lean.Expr.const `Bool.true []))
                        (Lean.Expr.bvar 4)))
                  (Lean.Expr.lam `h
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3)
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.false []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 4))
                  (Lean.BinderInfo.default))))
            (Lean.Expr.bvar 1))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_4" : term => return dIteToPropExprUnchanged_4

-- ∀ (c : Bool) (x y z : Nat) (f : !c → Nat → Nat),
--   (if h : !c then f h x else y) < z
--  ∀ (c : Bool) (x y z : Nat) (f : false = c → Nat → Nat),
--   Solver.dite' (true = c) (fun _ => y) (fun h : _ => f h x) < z
#testOptimize [ "DIteToPropExprUnchanged_4" ]
  ∀ (c : Bool) (x y z : Nat) (f : !c → Nat → Nat),
    (if h : !c then f h x else y) < z ===> dIteToPropExprUnchanged_4

def dIteToPropExprUnchanged_5 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h1
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.false []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h2
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.const `Int.neg []) (Lean.Expr.bvar 3))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_5" : term => return dIteToPropExprUnchanged_5

--  ∀ (c : Bool) (x y : Int) (f : ¬ c → Int → Int),
--   (if h : c then -x else f h x) > y ===>
-- ∀ (c : Bool) (x y : Int) (f : false = c → Int → Int),
--   y < Solver.dite' (true = c) (fun _ => x.neg) (fun h : _ => f h x)
#testOptimize [ "DIteToPropExprUnchanged_5" ]
  ∀ (c : Bool) (x y : Int) (f : ¬ c → Int → Int),
    (if h : c then -x else f h x) > y ===> dIteToPropExprUnchanged_5

def dIteToPropExprUnchanged_6 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `f
        (Lean.Expr.forallE `h1
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.const `Bool.true []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE `h2
            (Lean.Expr.const `Int [])
            (Lean.Expr.const `Int [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Int.add []) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 2)))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Int.add []) (Lean.Expr.bvar 3))
                (Lean.Expr.app (Lean.Expr.const `Int.neg []) (Lean.Expr.bvar 2)))
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_6" : term => return dIteToPropExprUnchanged_6

-- ∀ (c : Bool) (x y : Int) (f : c → Int → Int),
--    let p := x + y; let q := x - y;
--    (if h : c then f h p else q) > x ===>
-- ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
--    x < Solver.dite' (true = c) (fun h : _ => f h (x.add y)) (fun _ => x.add y.neg)
#testOptimize [ "DIteToPropExprUnchanged_6" ]
  ∀ (c : Bool) (x y : Int) (f : c → Int → Int),
     let p := x + y; let q := x - y;
     (if h : c then f h p else q) > x ===> dIteToPropExprUnchanged_6

def dIteToPropExprUnchanged_7 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `b
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `x
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `y
        (Lean.Expr.const `Int [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE `h1
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.true []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Bool.or []) (Lean.Expr.bvar 2))
                (Lean.Expr.app (Lean.Expr.const `Bool.not []) (Lean.Expr.bvar 3))))
            (Lean.Expr.forallE `h2
              (Lean.Expr.const `Int [])
              (Lean.Expr.const `Int [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
                (Lean.Expr.const `Int.instLTInt []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Solver.dite' [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Int []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Bool.or []) (Lean.Expr.bvar 3))
                        (Lean.Expr.app (Lean.Expr.const `Bool.not []) (Lean.Expr.bvar 4)))))
                (Lean.Expr.lam `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Bool.or []) (Lean.Expr.bvar 3))
                      (Lean.Expr.app (Lean.Expr.const `Bool.not []) (Lean.Expr.bvar 4))))
                  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 3))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.false []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Bool.or []) (Lean.Expr.bvar 3))
                    (Lean.Expr.app (Lean.Expr.const `Bool.not []) (Lean.Expr.bvar 4))))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_7" : term => return dIteToPropExprUnchanged_7

-- ∀ (a b : Bool) (x y : Int) (f : (! a) || b → Int → Int),
--  (if h : (! a) || b then f h x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int) (f : true = (b || !a) → Int → Int),
--   x < Solver.dite' (true = (b || !a)) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteToPropExprUnchanged_7" ]
  ∀ (a b : Bool) (x y : Int) (f : (! a) || b → Int → Int),
     (if h : (! a) || b then f h x else y) > x ===> dIteToPropExprUnchanged_7

-- ∀ (a b : Prop) (x y : Int) (f : ¬ a ∨ b → Int → Int), [Decidable a] → [Decidable b] →
--   (if h : ¬ a ∨ b then f h x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int) (f : b ∨ ¬ a → Int → Int),
--   x < Solver.dite' (b ∨ ¬ a) (fun h : _=> f h x) (fun _ => y)
#testOptimize [ "DIteToPropExprUnchanged_8" ]
  ∀ (a b : Prop) (x y : Int) (f : ¬ a ∨ b → Int → Int), [Decidable a] → [Decidable b] →
    (if h : ¬ a ∨ b then f h x else y) > x ===>
  ∀ (a b : Prop) (x y : Int) (f : b ∨ ¬ a → Int → Int),
    x < Solver.dite' (b ∨ ¬ a) (fun h : _=> f h x) (fun _ => y)

-- ∀ (a : Prop) (c b : Bool) (f : c → Prop → Prop), [Decidable a] →
--  (if h : c then f h a else b) = (if h : c then f h a else b) ===> True
#testOptimize [ "DIteToPropExprUnchanged_9" ]
  ∀ (a : Prop) (c b : Bool) (f : c → Prop → Prop), [Decidable a] →
   (if h : c then f h a else b) = (if h : c then f h a else b) ===> True

-- ∀ (c : Bool) (x y : Nat) (f : c → Nat → Nat),
--   (if h : c then f h x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat) (f : true = c → Nat → Nat),
--  x < Solver.dite' (true = c) (fun h : _ => f h x) (fun _ => y)
#testOptimize [ "DIteToBoolExprUnchanged_10" ]
  ∀ (c : Bool) (x y : Nat) (f : c → Nat → Nat),
    (if h : c then f h x else y) > x ===> diteFalseEqCondUnchanged_3

end Test.OptimizeDITE
