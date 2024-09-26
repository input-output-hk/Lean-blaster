import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeDITE
/-! ## Test objectives to validate normalization and simplification rules on `dite` -/

/-! Test cases for simplification rule ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> e1 (if e1 =ₚₜᵣ e2)`. -/

--  ∀ (c : Bool) (a : Prop), if h : c then a else a ===> ∀ (c : Bool) (a : Prop), a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_1" ] ∀ (c : Bool) (a : Prop), if _h : c then a else a ===>
                                     ∀ (_c : Bool) (a : Prop), a

-- ∀ (c a : Prop), if h : c then a else a ===> ∀ (c a : Prop), a
-- TODO: remove unused quantifier and constraint when COI performed on forall
#testOptimize [ "DIteAbsorption_2" ] ∀ (c a : Prop), [Decidable c] → if _h : c then a else a ===>
                                     ∀ (c a : Prop), [Decidable c] → a

-- ∀ (c : Bool) (a b : Prop), if h : c then a ∧ b else b ∧ a ===> ∀ (c : Bool) (a b : Prop), a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_3" ] ∀ (c : Bool) (a b : Prop), if _h : c then a ∧ b else b ∧ a ===>
                                     ∀ (_c : Bool) (a b : Prop), a ∧ b

-- ∀ (c : Bool) (a : Prop), if h : c then ¬ (¬ a) else a ===> ∀ (c : Bool) (a : Prop), a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_4" ] ∀ (c : Bool) (a : Prop), if _h : c then ¬ (¬ a) else a ===>
                                     ∀ (_c : Bool) (a : Prop), a

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), if h : c then x else y ===> ∀ (c : Bool) (a b : Prop), a ∧ b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_5" ] ∀ (c : Bool) (a b : Prop),
                                       let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
                                       if _h : c then x else y ===>
                                     ∀ (_c : Bool) (a b : Prop), a ∧ b

-- ∀ (a c : Bool), if h : c then ! (!a) else a ===> ∀ (a c : Bool), true = a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_6" ] ∀ (a c : Bool), if _h : c then !(! a) else a ===>
                                     ∀ (a _c : Bool), true = a


-- ∀ (a b c : Bool), if h : c then (!(!a)) = !(!(!b)) else a = !b ===> ∀ (a b c : Bool), a = !b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_7" ] ∀ (a b c : Bool), if _h : c then (!(!a)) = !(!(!b)) else a = !b ===>
                                     ∀ (a b _c : Bool), a = !b

-- ∀ (c : Bool) (x y : Nat), (if h : c then (x + 40) - 40 else x) < y ===>
-- ∀ (c : Bool) (x y : Nat), x < y
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_8" ] ∀ (c : Bool) (x y : Nat), (if _h : c then (x + 40) - 40 else x) < y ===>
                                     ∀ (_c : Bool) (x y : Nat), x < y

-- ∀ (c : Bool), if h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z ===>
-- ∀ (c : Bool), ∀ (x y : Int), y < x
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_9" ] ∀ (c : Bool), if _h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z ===>
                                     ∀ (_c : Bool) (x y : Int), y < x

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- ∀ (c p q : Bool) (a b : Prop), if h : c then x else y ===>
-- ∀ (c p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteAbsorption_10" ] ∀ (c p q : Bool) (a b : Prop),
                                        let x := if ¬ (p = q) then a else b;
                                        let y := if (q = p) then b else a;
                                        if _h : c then x else y ===>
                                      ∀ (_c p q : Bool) (a b : Prop), (¬ (p = q) → a) ∧ ((p = q) → b)


--  ∀ (c : Bool) (a : Prop), (if h : c then a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_11" ] ∀ (c : Bool) (a : Prop), (if _h : c then a else a) = a ===> True

-- ∀ (c a : Prop), (if h : c then a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_12" ] ∀ (c a : Prop), [Decidable c] → (if _h : c then a else a) = a ===> True

-- ∀ (c : Bool) (a b : Prop), (if h : c then a ∧ b else b ∧ a) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_13" ] ∀ (c : Bool) (a b : Prop), (if _h : c then a ∧ b else b ∧ a) = (a ∧ b) ===> True

-- ∀ (c : Bool) (a : Prop), (if h : c then ¬ (¬ a) else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_14" ] ∀ (c : Bool) (a : Prop), (if _h : c then ¬ (¬ a) else a) = a ===> True

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), (if h : c then x else y) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_15" ] ∀ (c : Bool) (a b : Prop),
                                        let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
                                        (if _h : c then x else y) = (a ∧ b) ===> True

-- ∀ (a c : Bool), (if h : c then ! (!a) else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_16" ] ∀ (a c : Bool), (if _h : c then !(! a) else a) = a ===> True

-- ∀ (a b c : Bool), (if h : c then (!(!a)) = !(!(!b)) else a = !b) = (a = !b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_17" ] ∀ (a b c : Bool),
                                        (if _h : c then (!(!a)) = !(!(!b)) else a = !b) = (a = !b) ===> True

-- ∀ (c : Bool) (x y : Nat), ((if h : c then (x + 40) - 40 else x) < y) = (x < y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_18" ] ∀ (c : Bool) (x y : Nat),
                                        ((if _h : c then (x + 40) - 40 else x) < y) = (x < y) ===> True

-- ∀ (c : Bool), (if h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z) = ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_19" ] ∀ (c : Bool),
                                        (if _h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z) =
                                      ∀ (x y : Int), y < x ===> True

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- ∀ (c p q : Bool) (a b : Prop), (if h : c then x else y) = (if (p = q) then b else a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteAbsorption_20" ] ∀ (c p q : Bool) (a b : Prop),
                                        let x := if ¬ (p = q) then a else b;
                                        let y := if (q = p) then b else a;
                                        (if _h : c then x else y) = (if p = q then b else a) ===> True



/-! Test cases to ensure that simplification rule ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> e1 (if e1 =ₚₜᵣ e2)`
    is not applied wrongly.
-/

--  ∀ (c : Bool) (a b : Prop), if h : c then a else b ===>
--  ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)
#testOptimize [ "DIteAbsorptionUnchanged_1" ] ∀ (c : Bool) (a b : Prop), if _h : c then a else b ===>
                                              ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)

-- ∀ (c a b : Prop), if h : c then a else b ===>
-- ∀ (c a b : Prop), (c → a) ∧ (¬ c → b)
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteAbsorptionUnchanged_2" ] ∀ (c a b : Prop), [Decidable c] → if _h : c then a else b ===>
                                              ∀ (c a b : Prop), [Decidable c] → (c → a) ∧ (¬ c → b)

-- ∀ (c : Bool) (a b : Prop), if h : c then a ∧ b else ¬ a ∧ ¬ b ===>
-- ∀ (c : Bool) (a b : Prop), (false = c → ¬ a ∧ ¬ b) ∧ (true = c → a ∧ b)
#testOptimize [ "DIteAbsorptionUnchanged_3" ] ∀ (c : Bool) (a b : Prop), if _h : c then a ∧ b else ¬ a ∧ ¬ b ===>
                                              ∀ (c : Bool) (a b : Prop), (false = c → ¬ a ∧ ¬ b) ∧ (true = c → a ∧ b)

-- ∀ (c : Bool) (a b : Prop), if h : c then ¬ (¬ a) else b ===>
-- ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)
#testOptimize [ "DIteAbsorptionUnchanged_4" ] ∀ (c : Bool) (a b : Prop), if _h : c then ¬ (¬ a) else b ===>
                                              ∀ (c : Bool) (a b : Prop), (false = c → b) ∧ (true = c → a)

-- let x := ¬ a ∧ ¬ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), if h : c then x else y ===>
-- ∀ (c : Bool) (a b : Prop), (false = c → a ∧ b) ∧ (true = c → ¬ a ∧ ¬ b)
#testOptimize [ "DIteAbsorptionUnchanged_5" ] ∀ (c : Bool) (a b : Prop), let x := ¬ a ∧ ¬ b;
                                                let y := (¬ (¬ a)) ∧ b;
                                                if _h : c then x else y ===>
                                              ∀ (c : Bool) (a b : Prop), (false = c → a ∧ b) ∧ (true = c → ¬ a ∧ ¬ b)

-- ∀ (a b c : Bool), (if h : c then ! (!a) else b) = true ===>
-- ∀ (a b c : Bool), true = ((a || !c) && (b || c))
#testOptimize [ "DIteAbsorptionUnchanged_6" ] ∀ (a b c : Bool), (if _h : c then !(! a) else b) = true ===>
                                              ∀ (a b c : Bool), true = ((a || !c) && (b || c))


-- ∀ (a b c d : Bool), if h : c then (!(!a)) = !(!(!b)) else b = !d ===>
-- ∀ (a b c d : Bool), (false = c → b = !d) ∧ (true = c → a = !b)
#testOptimize [ "DIteAbsorptionUnchanged_7" ] ∀ (a b c d: Bool), if _h : c then (!(!a)) = !(!(!b)) else b = !d ===>
                                              ∀ (a b c d : Bool), (false = c → b = !d) ∧ (true = c → a = !b)

-- ∀ (c : Bool) (x y z : Nat), (if h : c then (x + 40) - 40 else y) < z ===>
-- ∀ (c : Bool) (x y z : Nat), (if true = c then x else y) < z

def diteAbsorptionUnchanged_8 : Expr :=
 Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.lam `_h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 3)
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.false []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default))))
          (Lean.Expr.bvar 0))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "diteAbsorptionUnchanged_8" : term => return diteAbsorptionUnchanged_8

#testOptimize [ "DIteAbsorptionUnchanged_8" ] ∀ (c : Bool) (x y z : Nat), (if _h : c then (x + 40) - 40 else y) < z ===> diteAbsorptionUnchanged_8

-- ∀ (c : Bool), if h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), (false = c → ∀ (z y : Int), z > y) ∧ (true = c → ∀ (x y : Int), y < x)
#testOptimize [ "DIteAbsorptionUnchanged_9" ] ∀ (c : Bool), if _h : c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                              ∀ (c : Bool), (false = c → ∀ (z y : Int), z < y) ∧ (true = c → ∀ (x y : Int), y < x)


/-! Test cases for simplification rule `dite True (fun h : True => e1) (fun h : False => e2)` ==> e1`. -/
-- ∀ (a b : Prop), if h : True then a else b ===> ∀ (a b : Prop), a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_1" ] ∀ (a b : Prop), if _h : True then a else b ===> ∀ (a _b : Prop), a

-- ∀ (a b : Bool), if h : True then !a else b ===> ∀ (a b : Bool), false = a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_2" ] ∀ (a b : Bool), if _h : True then !a else b ===> ∀ (a _b : Bool), false = a

-- ∀ (x y z : Nat), (if h : True then (x + 40) - 40 else y) < z ===> ∀ (x y z : Nat), x < z
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_3" ] ∀ (x y z : Nat), (if _h : True then (x + 40) - 40 else y) < z ===>
                                   ∀ (x _y z : Nat), x < z

-- if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===> ∀ (x y : Int), y < x
#testOptimize [ "DIteTrueCond_4" ] if _h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                   ∀ (x y : Int), y < x

-- ∀ (c : Bool) (a b : Prop), if h : (! c || c) then a else b ===> ∀ (_c : Bool) (a _b : Prop), a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_5" ] ∀ (c : Bool) (a b : Prop), if _h : (! c) || c then a else b ===>
                                   ∀ (_c : Bool) (a _b : Prop), a

-- ∀ (c a b : Prop), if h : (¬ c ∨ c) then a else b ===> ∀ (c a b : Prop), a
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteTrueCond_6" ] ∀ (c a b : Prop), [Decidable c] → if _h : (¬ c ∨ c) then a else b ===>
                                   ∀ (c a _b : Prop), [Decidable c] → a

-- let x := a || a in
-- let y := ! a || x in
-- ∀ (a : Bool) (b c : Prop), if h : y then b else c ===> ∀ (a : Bool) (b c : Prop), b
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "DIteTrueCond_7" ] ∀ (a : Bool) (b c : Prop), let x := a || a; let y := ! a || x; if _h : y then b else c ===>
                                   ∀ (_a : Bool) (b _c : Prop), b

-- ∀ (a b : Prop), (if h : True then a else b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_8" ] ∀ (a b : Prop), (if _h : True then a else b) = a ===> True

-- ∀ (a b : Bool), (if h : True then !a else b) = !a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_9" ] ∀ (a b : Bool), (if _h : True then !a else b) = !a ===> True

-- ∀ (x y z : Nat), ((if h : True then (x + 40) - 40 else y) < z) = x < z ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_10" ] ∀ (x y z : Nat), ((if _h : True then (x + 40) - 40 else y) < z) = (x < z) ===> True

-- (if h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_11" ] (if _h : True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (x y : Int), y < x ===> True

-- ∀ (c : Bool) (a b : Prop), (if h : (! c || c) then a else b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_12" ] ∀ (c : Bool) (a b : Prop), (if _h : (! c) || c then a else b) = a ===> True

-- ∀ (c a b : Prop), if h : (¬ c ∨ c) then a else b ===> ∀ (c a b : Prop), a
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_13" ] ∀ (c a b : Prop), [Decidable c] → (if _h : (¬ c ∨ c) then a else b) = a ===> True

-- let x := a || a in
-- let y := ! a || x in
-- ∀ (a : Bool) (b c : Prop), (if h : y then b else c) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteTrueCond_14" ] ∀ (a : Bool) (b c : Prop),
                                     let x := a || a; let y := ! a || x;
                                     (if _h : y then b else c) = b ===> True


/-! Test cases for simplification rule `dite False (fun h : True => e1) (fun h : False => e2)` ==> e2`. -/

-- ∀ (a b : Prop), if h : False then a else b ===> ∀ (a b : Prop), b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_1" ] ∀ (a b : Prop), if _h : False then a else b ===> ∀ (_a b : Prop), b

-- ∀ (a b : Bool), if h : False then !a else b ===> ∀ (a b : Bool), true = b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_2" ] ∀ (a b : Bool), if _h : False then !a else b ===> ∀ (_a b : Bool), true = b

-- ∀ (x y z : Nat), (if h : False then (x + 40) - 40 else y) < z ===> ∀ (x y z : Nat), y < z
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_3" ] ∀ (x y z : Nat), (if _h : False then (x + 40) - 40 else y) < z ===>
                                    ∀ (_x y z : Nat), y < z

-- if h : False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===> ∀ (z y : Int), z < y
#testOptimize [ "DIteFalseCond_4" ] if _h : False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                   ∀ (z y : Int), z < y

-- ∀ (c : Bool) (a b : Prop), if h : (! c && c) then a else b ===> ∀ (c : Bool) (a b : Prop), b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_5" ] ∀ (c : Bool) (a b : Prop), if _h : (! c) && c then a else b ===>
                                    ∀ (_c : Bool) (_a b : Prop), b

-- ∀ (c a b : Prop), if h : (¬ c ∧ c) then a else b ===> ∀ (c a b : Prop), b
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_6" ] ∀ (c a b : Prop), [Decidable c] → if _h : (¬ c ∧ c) then a else b ===>
                                    ∀ (c _a b : Prop), [Decidable c] → b

-- let x := a && a in
-- let y := ! a && x in
-- ∀ (a : Bool) (b c : Prop), if h : y then b else c ===> ∀ (a : Bool) (b c : Prop), c
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "DIteFalseCond_7" ] ∀ (a : Bool) (b c : Prop), let x := a && a; let y := ! a && x; if _h : y then b else c ===>
                                    ∀ (_a : Bool) (_b c : Prop), c

-- ∀ (a b : Prop), (if h : False then a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_8" ] ∀ (a b : Prop), (if _h : False then a else b) = b ===> True

-- ∀ (a b : Bool), (if h : False then !a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_9" ] ∀ (a b : Bool), (if _h : False then !a else b) = b ===> True

-- ∀ (x y z : Nat), ((if h : False then (x + 40) - 40 else y) < z) = (y < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_10" ] ∀ (x y z : Nat), ((if _h : False then (x + 40) - 40 else y) < z) = (y < z) ===> True

-- (if h : False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (z y : Int), z < y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_11" ] (if _h : False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (z y : Int), z < y ===> True

-- ∀ (c : Bool) (a b : Prop), (if h : (! c && c) then a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseCond_12" ] ∀ (c : Bool) (a b : Prop), (if _h : (! c) && c then a else b) = b ===> True

-- ∀ (c a b : Prop), (if h : (¬ c ∧ c) then a else b) = b ===> True
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteFalseCond_13" ] ∀ (c a b : Prop), [Decidable c] → (if _h : (¬ c ∧ c) then a else b) = b ===> True

-- let x := a && a in
-- let y := ! a && x in
-- ∀ (a : Bool) (b c : Prop), (if h : y then b else c) = c ===> True
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "DIteFalseCond_14" ] ∀ (a : Bool) (b c : Prop),
                                       let x := a && a; let y := ! a && x;
                                       (if _h : y then b else c) = c ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
     - ``dite True (fun h : True => e1) (fun h : False => e2)` ==> e1`
     - \`dite False (fun h : True => e1) (fun h : False => e2)` ==> e2`
 -/

-- ∀ (a b : Bool) (p q : Prop), if h : (! a || a) && b then p else q ===>
-- ∀ (a b : Bool) (p q : Prop), (false = b → q) ∧ (true = b → p)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteCondUnchanged_1" ] ∀ (a b : Bool) (p q : Prop), if _h : (! a || a) && b then p else q ===>
                                        ∀ (_a b : Bool) (p q : Prop), (false = b → q) ∧ (true = b → p)

-- ∀ (a b c d : Bool), (if h : (b && !b) || a then c else d) = true ===>
-- ∀ (a b c d : Bool), true = ((a || d) && (c || !a))
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "DIteCondUnchanged_2" ] ∀ (a b c d : Bool), (if _h : (b && !b) || a then c else d) = true ===>
                                        ∀ (a _b c d : Bool), true = ((a || d) && (c || !a))

-- ∀ (a b : Bool) (x y z : Nat), (if h : b && (a || !a) then (x + 40) - 40 else y) < z ===>
-- ∀ (a b : Bool) (x y z : Nat), (if h : true = b then x else y) < z
-- TODO: remove unused quantifier when COI performed on forall
def diteCondUnchanged_3 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `b
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `x
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `y
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE `z
          (Lean.Expr.const `Nat [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Bool []))
                          (Lean.Expr.const `Bool.true []))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.lam `_h
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 3)
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam `_h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.false []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2)
                  (Lean.BinderInfo.default))))
            (Lean.Expr.bvar 0))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteCondUnchanged_3" : term => return diteCondUnchanged_3

#testOptimize [ "DIteCondUnchanged_3" ] ∀ (a b : Bool) (x y z : Nat), (if _h : b && (a || !a) then (x + 40) - 40 else y) < z ===>
                                        diteCondUnchanged_3

-- ∀ (a b : Prop) (p q : Prop), if h : (¬ a ∨ a) ∧ b then p else q ===>
-- ∀ (a b : Prop) (p q : Prop), (b → p) ∧ (¬ b → q)
-- TODO: remove unused quantifier and constraints when COI performed on forall
#testOptimize [ "DIteCondUnchanged_4" ] ∀ (a b : Prop) (p q : Prop),
                                          [Decidable a] → [Decidable b] → if _h : (¬ a ∨ a) ∧ b then p else q ===>
                                        ∀ (a b : Prop) (p q : Prop),
                                          [Decidable a] → [Decidable b] → (b → p) ∧ (¬ b → q)

-- ∀ (a b : Prop) (c d : Bool), (if h : (b ∧ ¬ b) ∨ a then c else d) = true ===>
-- ∀ (a b : Prop) (c d : Bool), true = (if h : a then c else d)
-- TODO: remove unused quantifier and constraints when COI performed on forall
#testOptimize [ "DIteCondUnchanged_5" ] ∀ (a b : Prop) (c d : Bool),
                                          [Decidable a] → [Decidable b] → (if _h : (b ∧ ¬ b) ∨ a then c else d) = true===>
                                        ∀ (a b : Prop) (c d : Bool),
                                          [Decidable a] → [Decidable b] → true = (if _h : a then c else d)

-- ∀ (a b : Prop) (x y z : Nat), (if h : b ∧ (a ∨ ¬ a) then (x + 40) - 40 else y) < z ===>
-- ∀ (a b : Prop) (x y z : Nat), (if h : b then x else y) < z
-- TODO: remove unused quantifier and constraints when COI performed on forall
#testOptimize [ "DIteCondUnchanged_6" ] ∀ (a b : Prop) (x y z : Nat),
                                          [Decidable a] → [Decidable b] → (if _h : b ∧ (a ∨ ¬ a) then (x + 40) - 40 else y) < z ===>
                                        ∀ (a b : Prop) (x y z : Nat),
                                          [Decidable a] → [Decidable b] → (if _h : b then x else y) < z


/-! Test cases for simplification rule:
       ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')`.
-/

-- ∀ (a b c : Prop), if h : ¬ c then a else b ===>
-- ∀ (a b c : Prop), (c → b) ∧ (¬ c → a)
#testOptimize [ "DIteNegCond_1" ] ∀ (a b c : Prop), [Decidable c] → if _h : ¬ c then a else b ===>
                                  ∀ (a b c : Prop), [Decidable c] → (c → b) ∧ (¬ c → a)

-- ∀ (c : Prop) (a b : Bool), (if h : ¬ c then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), true = (if h : c then b else a)
#testOptimize [ "DIteNegCond_2" ] ∀ (c : Prop) (a b : Bool), [Decidable c] → (if _h : ¬ c then a else b) = true ===>
                                  ∀ (c : Prop) (a b : Bool), [Decidable c] → true = (if _h : c then b else a)

-- ∀ (c : Prop) (x y z : Nat), (if h : ¬ c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then y else x) < z
#testOptimize [ "DIteNegCond_3" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : ¬ c then x else y) < z ===>
                                  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then y else x) < z

-- ∀ (c : Prop), if h : ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop), (c → ∀ (z y : Int), z < y) ∧ (¬ c → ∀ (x y : Int), y < x)
#testOptimize [ "DIteNegCond_4" ] ∀ (c : Prop), [Decidable c] → if _h : ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                  ∀ (c : Prop), [Decidable c] → (c → ∀ (z y : Int), z < y) ∧ (¬ c → ∀ (x y : Int), y < x)

-- ∀ (c : Prop) (x y : Int), (if h : c = False then x else y) > x ===>
-- ∀ (c : Prop) (x y : Int), x < (if h : c then y else x)
#testOptimize [ "DIteNegCond_5" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c = False then x else y) > x ===>
                                  ∀ (c : Prop) (x y : Int), [Decidable c] → x < (if _h : c then y else x)

-- ∀ (a b : Prop) (x y : Int), (if h : ¬ ( a = b ) then x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int), x < (if h : a = b then y else x)
#testOptimize [ "DIteNegCond_6" ] ∀ (a b : Prop) (x y : Int),
                                    [Decidable a] → [Decidable b] → (if _h : ¬ (a = b) then x else y) > x ===>
                                  ∀ (a b : Prop) (x y : Int),
                                    [Decidable a] → [Decidable b] → x < (if _h : (a = b) then y else x)

-- ∀ (c : Prop) (x y z : Nat), (if h : ¬ (¬ (¬ c)) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then y else x) < z
#testOptimize [ "DIteNegCond_7" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : ¬ (¬ (¬ c)) then x else y) < z ===>
                                  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then y else x) < z

-- ∀ (a b c : Prop), (if h : ¬ c then a else b) = if h : c then b else a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_8" ] ∀ (a b c : Prop),
                                    [Decidable c] → (if _h : ¬ c then a else b) = if _h : c then b else a ===> True

-- ∀ (c : Prop) (a b : Bool), (if h : ¬ c then a else b) = (if h : c then b else a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_9" ] ∀ (c : Prop) (a b : Bool),
                                    [Decidable c] → (if _h : ¬ c then a else b) = (if _h : c then b else a) ===> True

-- ∀ (c : Prop) (x y z : Nat), ((if h : ¬ c then x else y) < z) = ((if h : c then y else x) < z) ==> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_10" ] ∀ (c : Prop) (x y z : Nat),
                                     [Decidable c] → ((if _h : ¬ c then x else y) < z) = ((if _h : c then y else x) < z) ===> True

-- ∀ (c : Prop),
-- if h : ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z =
-- if h : c then ∀ (z y : Int), y > z else ∀ (x y : Int), x > y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_11" ] ∀ (c : Prop),[Decidable c] →
                                     (if _h : ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
                                     (if _h : c then ∀ (z y : Int), y > z else ∀ (x y : Int), x > y) ===> True

-- ∀ (c : Prop) (x y : Int), ((if h : c = False then x else y) > x) = (x < (if h : c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_12" ] ∀ (c : Prop) (x y : Int), [Decidable c] →
                                     ((if _h : c = False then x else y) > x) = (x < (if _h : c then y else x)) ===> True

-- ∀ (a b : Prop) (x y : Int), ((if h : ¬ ( a = b ) then x else y) > x) = x < (if h : a = b then y else x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_13" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                     ((if _h : ¬ (a = b) then x else y) > x) = (x < (if _h : (a = b) then y else x)) ===> True

-- ∀ (c : Prop) (x y z : Nat), ((if h : ¬ (¬ (¬ c)) then x else y) < z) = ((if h : c then y else x) < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteNegCond_14" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] →
                                     ((if _h : ¬ (¬ (¬ c)) then x else y) < z) = ((if _h : c then y else x) < z) ===> True


/-! Test cases to ensure that simplification rule:
       `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> `dite c' (fun h : c' => e2) (fun h : ¬ c' => e1)` (if c = ¬ c')`
    is not applied wrongly.
-/

-- ∀ (a b c : Prop), if h : ¬ (¬ c) then a else b ===>
-- ∀ (a b c : Prop), (c → a) ∧ (¬ c → b)
#testOptimize [ "DIteNegCondUnchanged_1" ] ∀ (a b c : Prop), [Decidable c] → if _h : ¬ (¬ c) then a else b ===>
                                           ∀ (a b c : Prop), [Decidable c] → (c → a) ∧ (¬ c → b)

-- ∀ (c : Prop) (a b : Bool), (if h : ¬ (¬ c) then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), true = (if h : c then a else b)
#testOptimize [ "DIteNegCondUnchanged_2" ] ∀ (c : Prop) (a b : Bool), [Decidable c] → (if _h : ¬ (¬ c) then a else b) = true ===>
                                           ∀ (c : Prop) (a b : Bool), [Decidable c] → true = (if _h : c then a else b)

-- ∀ (c : Prop) (x y z : Nat), (if h : ¬ (¬ c) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then y else x) < z
#testOptimize [ "DIteNegCondUnchanged_3" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : ¬ (¬ c) then x else y) < z ===>
                                           ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then x else y) < z

-- ∀ (c : Prop), if ¬ (¬ c) then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop), (c → ∀ (x y : Int), y < x) ∧ (¬ c → ∀ (z y : Int), z < y)
#testOptimize [ "DIteNegCondUnchanged_4" ] ∀ (c : Prop),
                                             [Decidable c] → if _h : ¬ (¬ c) then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                           ∀ (c : Prop), [Decidable c] → (c → ∀ (x y : Int), y < x) ∧ (¬ c → ∀ (z y : Int), z < y)

-- ∀ (c : Prop) (x y : Int), (if h : c = True then x else y) > x ===>
-- ∀ (c : Prop) (x y : Int), x < (if h : c then x else y)
#testOptimize [ "DIteNegCondUnchanged_5" ] ∀ (c : Prop) (x y : Int), [Decidable c] → (if _h : c = True then x else y) > x ===>
                                           ∀ (c : Prop) (x y : Int), [Decidable c] → x < (if _h : c then x else y)

-- ∀ (a b : Prop) (x y : Int), (if h : ¬ (¬ ( a = b )) then x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int), x < (if h : a = b then x else y)
#testOptimize [ "DIteNegCondUnchanged_6" ] ∀ (a b : Prop) (x y : Int),
                                             [Decidable a] → [Decidable b] → (if _h : ¬ (¬ (a = b)) then x else y) > x ===>
                                           ∀ (a b : Prop) (x y : Int),
                                             [Decidable a] → [Decidable b] → x < (if _h : (a = b) then x else y)

-- ∀ (c : Prop) (x y z : Nat), (if h : ¬ (¬ (¬ (¬ c))) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then x else y) < z
#testOptimize [ "DIteNegCondUnchanged_7" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : ¬ (¬ (¬ (¬ c))) then x else y) < z ===>
                                           ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then x else y) < z



/-! Test cases for simplification rule
    ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
         `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')`.
-/

-- ∀ (c : Bool) (p q : Prop), (if h : c = false then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), (false = c → p) ∧ (true = c → q)
#testOptimize [ "DIteFalseEqCond_1" ] ∀ (c : Bool) (p q : Prop), (if _h : c = false then p else q) ===>
                                      ∀ (c : Bool) (p q : Prop), (false = c → p) ∧ (true = c → q)

-- ∀ (a b c : Bool), (if h : c = false then a else b) = true ===>
-- ∀ (a b c : Bool), true = ((a || c) && (b || !c))
#testOptimize [ "DIteFalseEqCond_2" ]  ∀ (a b c : Bool), (if _h : c = false then a else b) = true ===>
                                       ∀ (a b c : Bool), true = ((a || c) && (b || !c))

-- ∀ (c : Bool) (x y : Nat), (if h : c = false then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < (if h : true = c then y else x)
def diteFalseEqCond_3 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 2)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_3" : term => return diteFalseEqCond_3

#testOptimize [ "DIteFalseEqCond_3" ] ∀ (c : Bool) (x y : Nat), (if _h : c = false then x else y) > x ===> diteFalseEqCond_3

-- ∀ (c : Bool), if h : c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), (false = c → ∀ (x y : Int), y < x) ∧ (true = c → ∀ (z y : Int), z < y)
#testOptimize [ "DIteFalseEqCond_4" ] ∀ (c : Bool), if _h : c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                      ∀ (c : Bool), (false = c → ∀ (x y : Int), y < x) ∧ (true = c → ∀ (z y : Int), z < y)

-- ∀ (c : Bool) (x y : Int), (if h : !c then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < (if h : true = c then y else x)
def diteFalseEqCond_5 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 2)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_5" : term => return diteFalseEqCond_5

#testOptimize [ "DIteFalseEqCond_5" ] ∀ (c : Bool) (x y : Int), (if _h : !c then x else y) > x ===> diteFalseEqCond_5

-- ∀ (c : Bool) (x y : Int), (if h : c == false then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < (if h : true = c then y else x)
#testOptimize [ "DIteFalseEqCond_6" ] ∀ (c : Bool) (x y : Int), (if _h : c == false then x else y) > x ===> diteFalseEqCond_5

-- ∀ (c : Bool) (x y : Int), (if h : !(! (! c)) then x else y) > x ===> x < (if h : true = c then y else x)
#testOptimize [ "DIteFalseEqCond_7" ] ∀ (c : Bool) (x y : Int), (if _h : ! (! (! c)) then x else y) > x ===> diteFalseEqCond_5

-- ∀ (a b : Bool) (x y : Int), (if h : a = (! b && b ) then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < (if h : true = a then y else x)
-- TODO: remove unused quantifiers when COI performed on forall
def diteFalseEqCond_8 : Expr :=
 Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `b
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `x
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `y
        (Lean.Expr.const `Int [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `_h
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
elab "diteFalseEqCond_8" : term => return diteFalseEqCond_8

#testOptimize [ "DIteFalseEqCond_8" ] ∀ (a b : Bool) (x y : Int), (if _h : a = (! b && b) then x else y) > x ===> diteFalseEqCond_8


-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool) (m n : Int), (if h : y then m else n) > m ===>
-- ∀ (a : Bool) (m n : Int), m < (if h : true = a then n else m)
def diteFalseEqCond_9 : Expr :=
 Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `n
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 2)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCond_9" : term => return diteFalseEqCond_9

#testOptimize [ "DIteFalseEqCond_9" ] ∀ (a : Bool) (m n : Int),
                                        let x := a || a; let y := ! a || ! x;
                                        (if _h : y then m else n) > m ===> diteFalseEqCond_9


-- ∀ (c : Bool) (p q : Prop), (if h : c = false then p else q) = (if h : c then q else p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_10" ] ∀ (c : Bool) (p q : Prop), (if _h : c = false then p else q) = if _h : c then q else p ===> True

-- ∀ (a b c : Bool), (if h : c = false then a else b) = if h : c then b else a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_11" ]  ∀ (a b c : Bool), (if _h : c = false then a else b) = if _h : c then b else a ===> True

-- ∀ (c : Bool) (x y : Nat), ((if h : c = false then x else y) > x) = (x < (if h : c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_12" ] ∀ (c : Bool) (x y : Nat),
                                         ((if _h : c = false then x else y) > x) = (x < (if _h : c then y else x)) ===> True

-- ∀ (c : Bool),
-- (if h : c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
-- if h : c then  ∀ (z y : Int), z < y else ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_13" ] ∀ (c : Bool),
                                        (if _h : c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
                                        if _h : c then ∀ (z y : Int), z < y else ∀ (x y : Int), y < x ===> True


-- ∀ (c : Bool) (x y : Int), ((if h : !c then x else y) > x) = (x < if h : c then y else x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_14" ] ∀ (c : Bool) (x y : Int),
                                         ((if _h : !c then x else y) > x) = (x < (if _h : c then y else x)) ===> True

-- ∀ (c : Bool) (x y : Int), ((if h : c == false then x else y) > x) = (x < (if h : c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_15" ] ∀ (c : Bool) (x y : Int),
                                         ((if _h : c == false then x else y) > x) = (x < (if _h : true = c then y else x)) ===> True

-- ∀ (c : Bool) (x y : Int), ((if h : !(! (! c)) then x else y) > x) = (x < (if h : c then y else x))
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_16" ] ∀ (c : Bool) (x y : Int),
                                         ((if _h : ! (! (! c)) then x else y) > x) = (x < (if _h : c then y else x)) ===> True

-- ∀ (a b : Bool) (x y : Int), ((if h : a = (! b && b ) then x else y) > x) = (x < (if h : a then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_17" ] ∀ (a b : Bool) (x y : Int),
                                         ((if _h : a = (! b && b) then x else y) > x) = (x < (if _h : a then y else x)) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool) (m n : Int), ((if h : y then m else n) > m) = (m < (if h : a then n else m)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteFalseEqCond_18" ] ∀ (a : Bool) (m n : Int),
                                         let x := a || a; let y := ! a || ! x;
                                         ((if _h : y then m else n) > m) = (m < (if _h : a then n else m)) ===> True


/-! Test cases to ensure that simplification rule
       `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
          `dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1)` (if c := false = c')`
    is not applied wrongly.
-/

-- ∀ (c : Bool) (p q : Prop), (if h : c = true then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)
#testOptimize [ "DIteFalseEqCondUnchanged_1" ] ∀ (c : Bool) (p q : Prop), (if _h : c = true then p else q) ===>
                                               ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)

-- ∀ (a b c : Bool), (if h : c = true then a else b) = true ===>
-- ∀ (a b c : Bool), true = ((a || !c) && (b || c))
#testOptimize [ "DIteFalseEqCondUnchanged_2" ]  ∀ (a b c : Bool), (if _h : c = true then a else b) = true ===>
                                                ∀ (a b c : Bool), true = ((a || !c) && (b || c))

-- ∀ (c : Bool) (x y : Nat), (if h : c = true then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < (if h : true = c then x else y)
def diteFalseEqCondUnchanged_3 : Expr :=
 Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_3" : term => return diteFalseEqCondUnchanged_3

#testOptimize [ "DIteFalseEqCondUnchanged_3" ] ∀ (c : Bool) (x y : Nat), (if _h : c = true then x else y) > x ===> diteFalseEqCondUnchanged_3

-- ∀ (c : Bool), if h : c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), (false = c → ∀ (z y : Int), z < y) ∧ (true = c → ∀ (x y : Int), y < x)
#testOptimize [ "DIteFalseEqCondUnchanged_4" ] ∀ (c : Bool), if _h : c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                               ∀ (c : Bool), (false = c → ∀ (z y : Int), z < y) ∧ (true = c → ∀ (x y : Int), y < x)

-- ∀ (a b : Bool) (p q : Prop), (if h : a = b then p else q) ===>
-- ∀ (a b : Bool) (p q : Prop), ((¬ (a = b) → q) ∧ ((a = b) → p))
#testOptimize [ "DIteFalseEqCondUnchanged_5" ] ∀ (a b : Bool) (p q : Prop), (if _h : a = b then p else q) ===>
                                               ∀ (a b : Bool) (p q : Prop), ((¬ (a = b) → q) ∧ ((a = b) → p))

-- ∀ (a b c d : Bool), (if h : a = b then c else d) = true ===>
-- ∀ (a b c d : Bool), true = (if h : a = b then c else d)
#testOptimize [ "DIteFalseEqCondUnchanged_6" ]  ∀ (a b c d : Bool), (if _h : a = b then c else d) = true ===>
                                                ∀ (a b c d : Bool), true = (if _h : a = b then c else d)

-- ∀ (a b : Bool) (x y : Nat), (if h : a = b then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Nat), x < (if h : a = b then x else y)
#testOptimize [ "DIteFalseEqCondUnchanged_7" ] ∀ (a b : Bool) (x y : Nat), (if _h : a = b then x else y) > x ===>
                                               ∀ (a b : Bool) (x y : Nat), x < (if _h : a = b then x else y)

-- ∀ (c : Bool), if h : c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), (false = c → ∀ (z y : Int), z < y) ∧ (true = c → ∀ (x y : Int), y < x)
#testOptimize [ "DIteFalseEqCondUnchanged_8" ] ∀ (c : Bool), if _h : c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                               ∀ (c : Bool), (false = c → ∀ (z y : Int), z < y) ∧ (true = c → ∀ (x y : Int), y < x)


-- ∀ (c : Bool) (x y : Int), (if h : !(!c) then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < (if h : true = c then x else y)
def diteFalseEqCondUnchanged_9 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_9" : term => return diteFalseEqCondUnchanged_9

#testOptimize [ "DIteFalseEqCondUnchanged_9" ] ∀ (c : Bool) (x y : Int), (if _h : !(!c) then x else y) > x ===>
                                                 diteFalseEqCondUnchanged_9

-- ∀ (c : Bool) (x y : Int), (if h : c == true then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < (if h : true = c then x else y)
#testOptimize [ "DIteFalseEqCondUnchanged_10" ] ∀ (c : Bool) (x y : Int), (if _h : c == true then x else y) > x ===>
                                                  diteFalseEqCondUnchanged_9

-- ∀ (c : Bool) (x y : Int), (if h : !(!(! (! c))) then x else y) > x ===> x < (if h : true = c then x else y)
#testOptimize [ "DIteFalseEqCondUnchanged_11" ] ∀ (c : Bool) (x y : Int), (if _h : !(! (! (! c))) then x else y) > x ===>
                                                  diteFalseEqCondUnchanged_9


-- ∀ (a b : Bool) (x y : Int), (if h : a = (! b || b ) then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < (if h : true = a then x else y)
-- TODO: remove unused quantifiers when COI performed on forall
def diteFalseEqCondUnchanged_12 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `b
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `x
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `y
        (Lean.Expr.const `Int [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 1)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_12" : term => return diteFalseEqCondUnchanged_12

#testOptimize [ "DIteFalseEqCondUnchanged_12" ] ∀ (a b : Bool) (x y : Int), (if _h : a = (! b || b) then x else y) > x  ===>
                                                  diteFalseEqCondUnchanged_12

-- let x := a && a in
-- let y := a || x in
-- ∀ (a : Bool) (m n : Int), (if h : y then m else n) > m ===>
-- ∀ (a : Bool) (m n : Int), m < (if h : a then m else n)
def diteFalseEqCondUnchanged_13 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `n
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "diteFalseEqCondUnchanged_13" : term => return diteFalseEqCondUnchanged_13

#testOptimize [ "DIteFalseEqCondUnchanged_13" ] ∀ (a : Bool) (m n : Int),
                                                  let x := a && a; let y := a || x;
                                                  (if _h : y then m else n) > m ===> diteFalseEqCondUnchanged_13


/-! Test cases for simplification rule
      ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
         (! c' || e1) && (c' || e2) (if Type(e1) = Bool ∧ c := true = c')`.
-/


-- ∀ (c a b : Bool), (if h : c then a else b) = true ===>
-- ∀ (c a b : Bool), true = ((c || b) && (a || !c))
#testOptimize [ "DIteToBoolExpr_1" ] ∀ (c a b : Bool), (if _h : c then a else b) = true ===>
                                     ∀ (c a b : Bool), true = ((c || b) && (a || !c))

-- ∀ (a b : Bool), (if h : a then true else b) = true ===> ∀ (a b : Bool), true = (a || b)
#testOptimize [ "DIteToBoolExpr_2" ] ∀ (a b : Bool), (if _h : a then true else b) = true ===>
                                     ∀ (a b : Bool), true = (a || b)

-- ∀ (a b : Bool), (if h : a then b else true) = true ===> ∀ (a b : Bool), true = (b || !a)
#testOptimize [ "DIteToBoolExpr_3" ] ∀ (a b : Bool), (if _h : a then b else true) = true ===>
                                     ∀ (a b : Bool), true = (b || !a)

-- ∀ (a b : Bool), (if h : a then false else b) = true ===> ∀ (a b : Bool), true = (!a && (a || b))
#testOptimize [ "DIteToBoolExpr_4" ] ∀ (a b : Bool), (if _h : a then false else b) = true ===>
                                     ∀ (a b : Bool), true = (!a && (a || b))

-- ∀ (a b : Bool), (if h : a then b else false) = true ===> ∀ (a b : Bool), true = (a && (b || !a))
#testOptimize [ "DIteToBoolExpr_5" ] ∀ (a b : Bool), (if _h : a then b else false) = true ===>
                                     ∀ (a b : Bool), true = (a && (b || !a))

-- ∀ (a b : Bool), (if h : a then a else b) = true ===> ∀ (a b : Bool), true = (a || b)
#testOptimize [ "DIteToBoolExpr_6" ] ∀ (a b : Bool), true = (if _h : a then a else b) ===>
                                     ∀ (a b : Bool), true = (a || b)

-- ∀ (a b : Bool), (if h : a then b else a) = true ===> ∀ (a b : Bool), true = (a && (b || !a))
#testOptimize [ "DIteToBoolExpr_7" ] ∀ (a b : Bool), (if _h : a then b else a) = true ===>
                                     ∀ (a b : Bool), true = (a && (b || !a))

-- ∀ (c a b : Bool), (if h : !c then a else b) = true ===>
-- ∀ (c a b : Bool), true = ((c || a) && (b || !c))
#testOptimize [ "DIteToBoolExpr_8" ] ∀ (c a b : Bool), (if _h : !c then a else b) = true ===>
                                     ∀ (c a b : Bool), true = ((c || a) && (b || !c))

-- ∀ (c a b : Bool), (if h : c then a else b) = ((!c || a) && (c || b)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_9" ] ∀ (c a b : Bool), (if _h : c then a else b) = ((!c || a) && (c || b)) ===> True

-- ∀ (a b : Bool), (if h : a then true else b) = (b || a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_10" ] ∀ (a b : Bool), (if _h : a then true else b) = (b || a) ===> True

-- ∀ (a b : Bool), (if h : a then b else true) = (!a || b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_11" ] ∀ (a b : Bool), (if _h : a then b else true) = (!a || b) ===> True

-- ∀ (a b : Bool), (if h : a then false else b) = (!a && (a || b)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_12" ] ∀ (a b : Bool), (if _h : a then false else b) = (!a && (a || b)) ===> True

-- ∀ (a b : Bool), (if h : a then b else false) = ((!a || b) && a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_13" ] ∀ (a b : Bool), (if _h : a then b else false) = ((!a || b) && a) ===> True

-- ∀ (a b : Bool), (if h : a then a else b) = (a || b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_14" ] ∀ (a b : Bool), (if _h : a then a else b) = (a || b) ===> True

-- ∀ (a b : Bool), (if h : a then b else a) = ((!a || b) && a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_15" ] ∀ (a b : Bool), (if _h : a then b else a) = ((!a || b) && a) ===> True

-- ∀ (c a b : Bool), (if h : !c then a else b) = ((c || a) && (!c || b)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToBoolExpr_16" ] ∀ (c a b : Bool), (if _h : !c then a else b) = ((c || a) && (!c || b)) ===> True


/-! Test cases to ensure that simplification rule
      ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==>
          (! c' || e1) && (c' || e2) (if Type(e1) = Bool ∧ c := true = c')`
    is not applied wrongly.
-/

-- ∀ (a b c d : Bool), (if h : c = d then a else b) = true ===>
-- ∀ (a b c d : Bool), true = (if h : c = d then a else b)
#testOptimize [ "DIteToBoolExprUnchanged_1" ] ∀ (a b c d : Bool), (if _h : c = d then a else b) = true ===>
                                              ∀ (a b c d : Bool), true = (if _h : c = d then a else b)

-- ∀ (c : Prop) (a b : Bool), (if h : c then a else b) = true ===>
-- ∀ (c : Prop), true = (if h : c then a else b)
#testOptimize [ "DIteToBoolExprUnchanged_2" ] ∀ (c : Prop) (a b : Bool), [Decidable c] → (if _h : c then a else b) = true ===>
                                              ∀ (c : Prop) (a b : Bool), [Decidable c] → true = (if _h : c then a else b)

-- ∀ (a b c : Bool), (if h : a = c then true else b) = true ===>
-- ∀ (a b c : Bool), true = (if h : a = c then true else b)
#testOptimize [ "DIteToBoolExprUnchanged_3" ] ∀ (a b c : Bool), (if _h : a = c then true else b) = true ===>
                                              ∀ (a b c : Bool), true = (if _h : a = c then true else b)

-- ∀ (a b c : Bool), (if h : a = c then b else true) = true ===>
-- ∀ (a b c : Bool), true = (if h : a = c then b else true)
#testOptimize [ "DIteToBoolExprUnchanged_4" ] ∀ (a b c : Bool), (if _h : a = c then b else true) = true ===>
                                              ∀ (a b c : Bool), true = (if _h : a = c then b else true)

-- ∀ (a b c : Bool), (if h : a = c then false else b) = true ===>
-- ∀ (a b c : Bool), true = (if h : a = c then false else b)
#testOptimize [ "DIteToBoolExprUnchanged_5" ] ∀ (a b c : Bool), (if _h : a = c then false else b) = true ===>
                                              ∀ (a b c : Bool), true = (if _h : a = c then false else b)

-- ∀ (a b c : Bool), (if h : a = c then b else false) = true ===>
-- ∀ (a b c : Bool), true = (if h : a = c then b else false)
#testOptimize [ "DIteToBoolExprUnchanged_6" ] ∀ (a b c : Bool), (if _h : a = c then b else false) = true ===>
                                              ∀ (a b c : Bool), true = (if _h : a = c then b else false)

-- ∀ (a b c d : Bool), (if h : ¬ (c = d) then a else b) = true ===>
-- ∀ (a b c d : Bool), true = (if h : (c = d) then b else a)
#testOptimize [ "DIteToBoolExprUnchanged_7" ] ∀ (a b c d : Bool), (if _h : ¬ (c = d) then a else b) = true ===>
                                              ∀ (a b c d : Bool), true = (if _h : (c = d) then b else a)

-- ∀ (c : Bool) (x y : Nat), (if h : c then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < (if h : true = c then x else y)
#testOptimize [ "DIteToBoolExprUnchanged_8" ] ∀ (c : Bool) (x y : Nat), (if _h : c then x else y) > x ===>
                                                diteFalseEqCondUnchanged_3



/-! Test cases for simplification rule ``dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`. -/

-- ∀ (c p q : Prop), if h : c then p else q ===> ∀ (c p q : Prop), (c → p) ∧ (¬ c → q)
#testOptimize [ "DIteToPropExpr_1" ] ∀ (c p q : Prop), [Decidable c] → if _h : c then p else q ===>
                                     ∀ (c p q : Prop), [Decidable c] → (c → p) ∧ (¬ c → q)

-- ∀ (c p : Prop), if h : c then True else p ===> ∀ (c p : Prop), ¬ c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_2" ] ∀ (c p : Prop), [Decidable c] → if _h : c then True else p ===>
                                     ∀ (c p : Prop), [Decidable c] → (¬ c) → p

-- ∀ (c p : Prop), if h : c then p else True ===> ∀ (c p : Prop), c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_3" ] ∀ (c p : Prop), [Decidable c] → if _h : c then p else True ===>
                                     ∀ (c p : Prop), [Decidable c] → c → p


-- ∀ (c p : Prop), if h : c then False else p ===>
-- ∀ (c p : Prop), (c → False) ∧ (¬ c → p)
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_4" ] ∀ (c p : Prop), [Decidable c] → if _h : c then False else p ===>
                                     ∀ (c p : Prop), [Decidable c] → (c → False) ∧ (¬ c → p)

-- ∀ (c p : Prop), if h : c then p else False ===>
-- ∀ (c p : Prop), (c → p) ∧ (¬ c → False)
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_5" ] ∀ (c p : Prop), [Decidable c] → if _h : c then p else False ===>
                                     ∀ (c p : Prop), [Decidable c] → (c → p) ∧ (¬ c → False)

-- ∀ (c p : Prop), if h : c then c else p ===>
-- ∀ (c p : Prop), ¬ c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_6" ] ∀ (c p : Prop), [Decidable c] → if _h : c then c else p ===>
                                     ∀ (c p : Prop), [Decidable c] → ¬ c → p

-- ∀ (c p : Prop), if h : c then p else c ===>
-- ∀ (c p : Prop), c ∧ (c → p)
-- TODO: remove unused constraints when COI performed on forall
-- TODO: may be simplified to (c ∧ p)
#testOptimize [ "DIteToPropExpr_7" ] ∀ (c p : Prop), [Decidable c] → if _h : c then p else c ===>
                                     ∀ (c p : Prop), [Decidable c] → c ∧ (c → p)

-- ∀ (c p : Prop), if h : c then ¬ c else p ===>
-- ∀ (c p : Prop), ¬ c ∧ (¬ c → p)
-- TODO: remove unused constraints when COI performed on forall
-- TODO: may be simplified to (¬ c ∧ p)
#testOptimize [ "DIteToPropExpr_8" ] ∀ (c p : Prop), [Decidable c] → if _h : c then ¬ c else p ===>
                                     ∀ (c p : Prop), [Decidable c] → ¬ c ∧ (¬ c → p)

-- ∀ (c p : Prop), if h : c then p else ¬ c ===>
-- ∀ (c p : Prop), c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_9" ] ∀ (c p : Prop), [Decidable c] → if _h : c then p else ¬ c ===>
                                     ∀ (c p : Prop), [Decidable c] → c → p

-- ∀ (c p q : Prop), if h : ¬ c then p else q ===>
-- ∀ (c p q : Prop), (c → q) ∧ (¬ c → p)
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_10" ] ∀ (c p q : Prop), [Decidable c] → if _h : ¬ c then p else q ===>
                                      ∀ (c p q : Prop), [Decidable c] → (c → q) ∧ (¬ c → p)


-- ∀ (c : Bool) (p q : Prop), if h : c then p else q ===>
-- ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)
#testOptimize [ "DIteToPropExpr_11" ] ∀ (c : Bool) (p q : Prop), if _h : c then p else q ===>
                                      ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)

-- ∀ (c : Bool) (p : Prop), if h : c then True else p ===>
-- ∀ (c p : Prop), false = c → p
#testOptimize [ "DIteToPropExpr_12" ] ∀ (c : Bool) (p : Prop), if _h : c then True else p ===>
                                      ∀ (c : Bool) (p : Prop), false = c → p

-- ∀ (c : Bool) (p : Prop), if h : c then p else True ===>
-- ∀ (c : Bool) (p : Prop), true = c → p
#testOptimize [ "DIteToPropExpr_13" ] ∀ (c : Bool) (p : Prop), if _h : c then p else True ===>
                                      ∀ (c : Bool) (p : Prop), true = c → p

-- ∀ (c : Bool) (p : Prop), if h : c then False else p ===>
-- ∀ (c : Bool) (p : Prop), (false = c → p) ∧ (true = c → False)
#testOptimize [ "DIteToPropExpr_14" ] ∀ (c : Bool) (p : Prop), if _h : c then False else p ===>
                                      ∀ (c : Bool) (p : Prop), (false = c → p) ∧ (true = c → False)

-- ∀ (c : Bool) (p : Prop), if h : c then p else False ===>
-- ∀ (c : Bool) (p : Prop), (false = c → False) ∧ (true = c → p)
#testOptimize [ "DIteToPropExpr_15" ] ∀ (c : Bool) (p : Prop), if _h : c then p else False ===>
                                      ∀ (c : Bool) (p : Prop), (false = c → False) ∧ (true = c → p)

-- ∀ (c : Bool) (p : Prop), if h : c then c else p ===>
-- ∀ (c : Bool) p : Prop), false = c → p
#testOptimize [ "DIteToPropExpr_16" ] ∀ (c : Bool) (p : Prop), if _h : c then c else p ===>
                                      ∀ (c : Bool) (p : Prop), false = c → p

-- ∀ (c : Bool) (p : Prop), if h : c then p else c ===>
-- ∀ (c : Bool) (p : Prop), (true = c) ∧ (true = c → p)
-- TODO: may be simplified to (true = c ∧ p)
#testOptimize [ "DIteToPropExpr_17" ] ∀ (c : Bool) (p : Prop), if _h : c then p else c ===>
                                      ∀ (c : Bool) (p : Prop), (true = c) ∧ (true = c → p)

-- ∀ (c : Bool) (p : Prop), if h : c then !c else p ===>
-- ∀ (c : Bool) (p : Prop), (false = c) ∧ (false = c → p)
-- TODO: may be simplified to (false = c ∧ p)
#testOptimize [ "DIteToPropExpr_18" ] ∀ (c : Bool) (p : Prop), if _h : c then !c else p ===>
                                      ∀ (c : Bool) (p : Prop), (false = c) ∧ (false = c → p)

-- ∀ (c : Bool) (p : Prop), if h : c then p else !c ===>
-- ∀ (c : Bool) p : Prop), true = c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "DIteToPropExpr_19" ] ∀ (c : Bool) (p : Prop), if _h : c then p else !c ===>
                                      ∀ (c : Bool) (p : Prop), true = c → p

-- ∀ (c : Bool) (p q : Prop), (if h : !c then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), (false = c → p) ∧ (true = c → q)
#testOptimize [ "DIteToPropExpr_20" ] ∀ (c : Bool) (p q : Prop), if _h : !c then p else q ===>
                                     ∀ (c : Bool) (p q : Prop), (false = c → p) ∧ (true = c → q)


-- ∀ (c p q : Prop), (if h : c then p else q) = ((c → p) ∧ (¬ c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_21" ] ∀ (c p q : Prop),
                                       [Decidable c] → (if _h : c then p else q) = ((c → p) ∧ (¬ c → q)) ===> True

-- ∀ (c p : Prop), (if h : c then True else p) = (¬ c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_22" ] ∀ (c p : Prop),
                                        [Decidable c] → (if _h : c then True else p) = ((¬ c) → p) ===> True

-- ∀ (c p : Prop), (if h : c then p else True) = (c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_23" ] ∀ (c p : Prop),
                                        [Decidable c] → (if _h : c then p else True) = (c → p) ===> True

-- ∀ (c p : Prop), (if h : c then False else p) = ((c → False) ∧ (¬ c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_24" ] ∀ (c p : Prop),
                                        [Decidable c] → (if _h : c then False else p) = ((c → False) ∧ (¬ c → p)) ===> True

-- ∀ (c p : Prop), (if h : c then p else False) = ((c → p) ∧ (¬ c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_25" ] ∀ (c p : Prop),
                                        [Decidable c] → (if _h : c then p else False) = ((c → p) ∧ (¬ c → False)) ===> True

-- ∀ (c p : Prop), (if h : c then c else p) = (¬ c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_26" ] ∀ (c p : Prop), [Decidable c] → (if _h : c then c else p) = (¬ c → p) ===> True

-- ∀ (c p : Prop), (if h : c then p else c) = (c ∧ (c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_27" ] ∀ (c p : Prop), [Decidable c] → (if _h : c then p else c) = (c ∧ (c → p)) ===> True

-- ∀ (c p : Prop), (if h : c then ¬ c else p) = ((¬ c → p) ∧ ¬ c) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_28" ] ∀ (c p : Prop),
                                        [Decidable c] → (if _h : c then ¬ c else p) = ((¬ c → p) ∧ ¬ c) ===> True

-- ∀ (c p : Prop), (if h : c then p else ¬ c) = (c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_29" ] ∀ (c p : Prop), [Decidable c] → (if _h : c then p else ¬ c) = (c → p) ===> True

-- ∀ (c p q : Prop), (if h : ¬ c then p else q) = ((¬ c → p) ∧ (c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_30" ] ∀ (c p q : Prop),
                                        [Decidable c] → (if _h : ¬ c then p else q) = ((¬ c → p) ∧ (c → q)) ===> True

-- ∀ (c : Bool) (p q : Prop), (if h : c then p else q) = ((true = c → p) ∧ (false = c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_31" ] ∀ (c : Bool) (p q : Prop),
                                        (if _h : c then p else q) = ((true = c → p) ∧ (false = c → q)) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then True else p) = (false = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_32" ] ∀ (c : Bool) (p : Prop),
                                          (if _h : c then True else p) = (false = c → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then p else True) = (true = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_33" ] ∀ (c : Bool) (p : Prop),
                                          (if _h : c then p else True) = (true = c → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then False else p) = ((false = c → p) ∧ (true = c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_34" ] ∀ (c : Bool) (p : Prop),
                                        (if _h : c then False else p) = ((false = c → p) ∧ (true = c → False)) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then p else False) = ((false = c → False) ∧ (true = c → p)) ===> True
#testOptimize [ "DIteToPropExpr_35" ] ∀ (c : Bool) (p : Prop),
                                        (if _h : c then p else False) = ((false = c → False) ∧ (true = c → p)) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then true = c else p) = (false = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_36" ] ∀ (c : Bool) (p : Prop), (if _h : c then true = c else p) = ((false = c) → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then p else c) = ((true = c → p) ∧ (true = c)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_37" ] ∀ (c : Bool) (p : Prop),
                                       (if _h : c then p else c) = ((true = c → p) ∧ (true = c)) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then true = !c else p) = ((false = c) ∧ (false = c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_38" ] ∀ (c : Bool) (p : Prop),
                                       (if _h : c then true = !c else p) = ((false = c) ∧ (false = c → p)) ===> True

-- ∀ (c : Bool) (p : Prop), (if h : c then p else true = !c) = (true = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "DIteToPropExpr_39" ] ∀ (c : Bool) (p : Prop),
                                       (if _h : c then p else true = !c) = (true = c → p) ===> True

-- ∀ (c : Bool) (p q : Prop), (if h : !c then p else q) = ((false = c → p) ∧ (true = c → q)) ===> True
#testOptimize [ "DIteToPropExpr_40" ] ∀ (c : Bool) (p q : Prop),
                                       (if _h : !c then p else q) = ((true = c → q) ∧ (false = c → p)) ===> True


/-! Test cases to ensure that simplification rule
      `dite c (fun h : c => e1) (fun h : ¬ c => e2)` ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`
    is not applied wrongly.
 -/

-- ∀ (c : Prop) (a b : Bool), (if h : c then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), true = (if c then a else b)
def dIteToPropExprUnchanged_1 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.sort (Lean.Level.zero))
  (Lean.Expr.forallE `a
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `b
      (Lean.Expr.const `Bool [])
      (Lean.Expr.forallE
        (Lean.Name.mkNum `inst.Solver.Tests.Optimize.OptimizeITE.OptimizeDITE._hyg 13364)
        (Lean.Expr.app (Lean.Expr.const `Decidable []) (Lean.Expr.bvar 2))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
            (Lean.Expr.const `Bool.true []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 0))
              (Lean.Expr.lam `_h (Lean.Expr.bvar 3) (Lean.Expr.bvar 3) (Lean.BinderInfo.default)))
            (Lean.Expr.lam
              `_h
              (Lean.Expr.app (Lean.Expr.const `Not []) (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_1" : term => return dIteToPropExprUnchanged_1

#testOptimize [ "DIteToPropExprUnchanged_1" ] ∀ (c : Prop) (a b : Bool), [Decidable c] → (if _h : c then a else b) = true ===>
                                                dIteToPropExprUnchanged_1

-- ∀ (c : Prop) (x y z : Nat), (if h : c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then x else y) < z
#testOptimize [ "DIteToPropExprUnchanged_2" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then x else y) < z ===>
                                              ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then x else y) < z

-- ∀ (c : Bool) (x y z : Nat), (if h : c then x else y) < z ===>
-- ∀ (c : Bool) (x y z : Nat), (if h : true = c then x else y) < z
def dIteToPropExprUnchanged_3 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.lam `_h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 3)
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.false []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default))))
          (Lean.Expr.bvar 0))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_3" : term => return dIteToPropExprUnchanged_3

#testOptimize [ "DIteToPropExprUnchanged_3" ] ∀ (c : Bool) (x y z : Nat), (if _h : c then x else y) < z ===> dIteToPropExprUnchanged_3

-- ∀ (c : Prop) (a b : Bool), (if h : ¬ c then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), true = (if h : c then b else a)
#testOptimize [ "DIteToPropExprUnchanged_4" ] ∀ (c : Prop) (a b : Bool), [Decidable c] → (if _h : ¬ c then a else b) = true ===>
                                              ∀ (c : Prop) (a b : Bool), [Decidable c] → true = (if _h : c then b else a)

-- ∀ (c : Prop) (x y z : Nat), (if h : ¬ c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), (if h : c then y else x) < z
#testOptimize [ "DIteToPropExprUnchanged_5" ] ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : ¬ c then x else y) < z ===>
                                              ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if _h : c then y else x) < z

-- ∀ (c : Bool) (x y z : Nat), (if h : !c then x else y) < z ===>
-- ∀ (c : Bool) (x y z : Nat), (if h : true = c then y else x) < z
def dIteToPropExprUnchanged_6 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE `z
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.lam `_h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2)
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.false []))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 3)
                (Lean.BinderInfo.default))))
          (Lean.Expr.bvar 0))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_6" : term => return dIteToPropExprUnchanged_6

#testOptimize [ "DIteToPropExprUnchanged_6" ] ∀ (c : Bool) (x y z : Nat), (if _h : !c then x else y) < z ===> dIteToPropExprUnchanged_6


-- ∀ (c : Bool) (x y : Int), (if h : c then -x else x) > y ===>
-- ∀ (c : Bool) (x y : Int), y < (if h : true = c then Int.neg x else x)
def dIteToPropExprUnchanged_7 : Expr :=
 Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app (Lean.Expr.const `Int.neg []) (Lean.Expr.bvar 2))
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 2)
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_7" : term => return dIteToPropExprUnchanged_7

#testOptimize [ "DIteToPropExprUnchanged_7" ] ∀ (c : Bool) (x y : Int), (if _h : c then -x else x) > y ===> dIteToPropExprUnchanged_7

-- let p := x + y in
-- let q := x - y in
-- ∀ (c : Bool) (x y : Int), (if h : c then p else q) > x ===>
-- ∀ (c : Bool) (x y : Int), x < (if h : true = c then Int.add x y else Int.sub x y)
def dIteToPropExprUnchanged_8 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Int [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
            (Lean.Expr.const `Int.instLTInt []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.true []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Int.add []) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 1))
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam `_h
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.false []))
              (Lean.Expr.bvar 2))
            (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Int.sub []) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 1))
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_8" : term => return dIteToPropExprUnchanged_8

#testOptimize [ "DIteToPropExprUnchanged_8" ] ∀ (c : Bool) (x y : Int),
                                               let p := x + y; let q := x - y;
                                               (if _h : c then p else q) > x ===> dIteToPropExprUnchanged_8

-- ∀ (a b : Bool) (x y : Int), (if h : (! a || b) then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < (if h : true = (b || ! a) then x else y)
def dIteToPropExprUnchanged_9 : Expr :=
Lean.Expr.forallE `a
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `b
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `x
      (Lean.Expr.const `Int [])
      (Lean.Expr.forallE `y
        (Lean.Expr.const `Int [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.const `Int.instLTInt []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `or []) (Lean.Expr.bvar 2))
                      (Lean.Expr.app (Lean.Expr.const `not []) (Lean.Expr.bvar 3)))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instDecidableEqBool []) (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `or []) (Lean.Expr.bvar 2))
                    (Lean.Expr.app (Lean.Expr.const `not []) (Lean.Expr.bvar 3)))))
              (Lean.Expr.lam `_h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.true []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `or []) (Lean.Expr.bvar 2))
                    (Lean.Expr.app (Lean.Expr.const `not []) (Lean.Expr.bvar 3))))
                (Lean.Expr.bvar 2)
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam `_h
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                  (Lean.Expr.const `Bool.false []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `or []) (Lean.Expr.bvar 2))
                  (Lean.Expr.app (Lean.Expr.const `not []) (Lean.Expr.bvar 3))))
              (Lean.Expr.bvar 1)
              (Lean.BinderInfo.default))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "dIteToPropExprUnchanged_9" : term => return dIteToPropExprUnchanged_9

#testOptimize [ "DIteToPropExprUnchanged_9" ] ∀ (a b : Bool) (x y : Int),
                                                (if _h : (! a) || b then x else y) > x ===> dIteToPropExprUnchanged_9

-- ∀ (a b : Prop) (x y : Int), (if h : (¬ a ∨ b) then x else y) > x ===
-- ∀ (a b : Prop) (x y : Int), x < (if h : ( b ∨ ¬ a ) then x else y)
#testOptimize [ "DIteToPropExprUnchanged_10" ] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                                 (if _h : (¬ a ∨ b) then x else y) > x ===>
                                               ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                                 x < (if _h : (b ∨ ¬ a) then x else y)


end Test.OptimizeDITE
