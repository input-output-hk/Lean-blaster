import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeITE

/-! ## Test objectives to validate normalization and simplification rules on `ite` -/

/-! Test cases for simplification rule `if c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)`. -/

--  ∀ (c : Bool) (a : Prop), if c then a else a ===> ∀ (a : Prop), a
#testOptimize [ "IteAbsorption_1" ] ∀ (c : Bool) (a : Prop), if c then a else a ===>
                                    ∀ (a : Prop), a

-- ∀ (c a : Prop), if c then a else a ===> ∀ (a : Prop), a
#testOptimize [ "IteAbsorption_2" ] ∀ (c a : Prop), [Decidable c] → if c then a else a ===>
                                    ∀ (a : Prop), a

-- ∀ (c : Bool) (a b : Prop), if c then a ∧ b else b ∧ a ===> ∀ (a b : Prop), a ∧ b
#testOptimize [ "IteAbsorption_3" ] ∀ (c : Bool) (a b : Prop), if c then a ∧ b else b ∧ a ===>
                                    ∀ (a b : Prop), a ∧ b

-- ∀ (c : Bool) (a : Prop), if c then ¬ (¬ a) else a ===> ∀ (a : Prop), a
#testOptimize [ "IteAbsorption_4" ] ∀ (c : Bool) (a : Prop), if c then ¬ (¬ a) else a ===>
                                    ∀ (a : Prop), a

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), if c then x else y ===> ∀ (a b : Prop), a ∧ b
#testOptimize [ "IteAbsorption_5" ] ∀ (c : Bool) (a b : Prop),
                                      let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
                                      if c then x else y ===>
                                    ∀ (a b : Prop), a ∧ b

-- ∀ (a c : Bool), if c then ! (!a) else a ===> ∀ (a : Bool), true = a
#testOptimize [ "IteAbsorption_6" ] ∀ (a c : Bool), if c then !(! a) else a ===>
                                    ∀ (a : Bool), true = a


-- ∀ (a b c : Bool), if c then (!(!a)) = !(!(!b)) else a = !b ===> ∀ (a b : Bool), a = !b
#testOptimize [ "IteAbsorption_7" ] ∀ (a b c : Bool), if c then (!(!a)) = !(!(!b)) else a = !b ===>
                                    ∀ (a b : Bool), a = !b

-- ∀ (c : Bool) (x y : Nat), (if c then (40 + x) - 40 else x) < y ===>
-- ∀ (x y : Nat), x < y
#testOptimize [ "IteAbsorption_8" ] ∀ (c : Bool) (x y : Nat), (if c then (40 + x) - 40 else x) < y ===>
                                    ∀ (x y : Nat), x < y

-- ∀ (c : Bool), if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z ===>
-- ∀ (x y : Int), y < x
#testOptimize [ "IteAbsorption_9" ] ∀ (c : Bool), if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z ===>
                                    ∀ (x y : Int), y < x

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- ∀ (c p q : Bool) (a b : Prop), if c then x else y ===>
-- ∀ (p q : Bool) (a b : Prop), Blaster.dite' (p = q) (λ _ => b) (λ _ => a)
#testOptimize [ "IteAbsorption_10" ]
  ∀ (c p q : Bool) (a b : Prop),
   let x := if ¬ (p = q) then a else b;
   let y := if (q = p) then b else a;
   if c then x else y ===>
  ∀ (p q : Bool) (a b : Prop), Blaster.dite' (p = q) (λ _ => b) (λ _ => a)


--  ∀ (c : Bool) (a : Prop), (if c then a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_11" ] ∀ (c : Bool) (a : Prop), (if c then a else a) = a ===> True

-- ∀ (c a : Prop), (if c then a else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_12" ] ∀ (c a : Prop), [Decidable c] → (if c then a else a) = a ===> True

-- ∀ (c : Bool) (a b : Prop), (if c then a ∧ b else b ∧ a) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_13" ] ∀ (c : Bool) (a b : Prop), (if c then a ∧ b else b ∧ a) = (a ∧ b) ===> True

-- ∀ (c : Bool) (a : Prop), (if c then ¬ (¬ a) else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_14" ] ∀ (c : Bool) (a : Prop), (if c then ¬ (¬ a) else a) = a ===> True

-- let x := a ∧ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), (if c then x else y) = (a ∧ b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_15" ] ∀ (c : Bool) (a b : Prop),
                                      let x := a ∧ b; let y := (¬ (¬ a)) ∧ b;
                                      (if c then x else y) = (a ∧ b) ===> True

-- ∀ (a c : Bool), (if c then ! (!a) else a) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_16" ] ∀ (a c : Bool), (if c then !(! a) else a) = a ===> True

-- ∀ (a b c : Bool), (if c then (!(!a)) = !(!(!b)) else a = !b) = (a = !b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_17" ] ∀ (a b c : Bool),
                                       (if c then (!(!a)) = !(!(!b)) else a = !b) = (a = !b) ===> True

-- ∀ (c : Bool) (x y : Nat), ((if c then (40 + x) - 40 else x) < y) = (x < y) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_18" ] ∀ (c : Bool) (x y : Nat),
                                       ((if c then (40 + x) - 40  else x) < y) = (x < y) ===> True

-- ∀ (c : Bool), (if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z) = ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_19" ] ∀ (c : Bool),
                                     (if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y < z) =
                                     ∀ (x y : Int), y < x ===> True

-- let x := if ¬ (p = q) then a else b in
-- let y := if q = p then b else a in
-- ∀ (c p q : Bool) (a b : Prop), (if c then x else y) = (if (p = q) then b else a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteAbsorption_20" ] ∀ (c p q : Bool) (a b : Prop),
                                      let x := if ¬ (p = q) then a else b;
                                      let y := if (q = p) then b else a;
                                      (if c then x else y) = (if p = q then b else a) ===> True


/-! Test cases to ensure that simplification rule `if c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)` is not applied wrongly. -/

--  ∀ (c : Bool) (a b : Prop), if c then a else b ===>
--  ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a) (λ _=> b)
#testOptimize [ "IteAbsorptionUnchanged_1" ]
  ∀ (c : Bool) (a b : Prop), if c then a else b ===>
  ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a) (λ _=> b)

-- ∀ (c a b : Prop), if c then a else b ===>
-- ∀ (c a b : Prop), Blaster.dite' c (λ _ => a) (λ _ => b)
#testOptimize [ "IteAbsorptionUnchanged_2" ]
  ∀ (c a b : Prop), [Decidable c] → if c then a else b ===>
  ∀ (c a b : Prop), Blaster.dite' c (λ _ => a) (λ _ => b)

-- ∀ (c : Bool) (a b : Prop), if c then a ∧ b else ¬ a ∧ ¬ b ===>
-- ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a ∧ b) (λ _ =>  ¬ a ∧ ¬ b)
#testOptimize [ "IteAbsorptionUnchanged_3" ]
  ∀ (c : Bool) (a b : Prop), if c then a ∧ b else ¬ a ∧ ¬ b ===>
  ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a ∧ b) (λ _ =>  ¬ a ∧ ¬ b)

-- ∀ (c : Bool) (a b : Prop), if c then ¬ (¬ a) else b ===>
-- ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a) (λ _ => b)
#testOptimize [ "IteAbsorptionUnchanged_4" ]
  ∀ (c : Bool) (a b : Prop), if c then ¬ (¬ a) else b ===>
  ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => a) (λ _ => b)

-- let x := ¬ a ∧ ¬ b in
-- let y := (¬ (¬ a)) ∧ b in
-- ∀ (c : Bool) (a b : Prop), if c then x else y ===>
-- ∀ (c : Bool) (a b : Prop), Blaster.dite' (true = c) (λ _ => ¬ a ∧ ¬ b) (λ _ => a ∧ b)
#testOptimize [ "IteAbsorptionUnchanged_5" ]
  ∀ (c : Bool) (a b : Prop), let x := ¬ a ∧ ¬ b;
    let y := (¬ (¬ a)) ∧ b;
    if c then x else y ===>
  ∀ (c : Bool) (a b : Prop),
    Blaster.dite' (true = c) (λ _ => ¬ a ∧ ¬ b) (λ _ => a ∧ b)

-- ∀ (a b c : Bool), (if c then ! (!a) else b) = true ===>
-- ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = a) (λ _ => true = b)
#testOptimize [ "IteAbsorptionUnchanged_6" ]
  ∀ (a b c : Bool), (if c then !(! a) else b) = true ===>
  ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = a) (λ _ => true = b)


-- ∀ (a b c d : Bool), if c then (!(!a)) = !(!(!b)) else b = !d ===>
-- ∀ (a b c d : Bool), Blaster.dite' (true = c) (λ _ => a = !b) (λ _ => b = !d)
#testOptimize [ "IteAbsorptionUnchanged_7" ]
  ∀ (a b c d: Bool), if c then (!(!a)) = !(!(!b)) else b = !d ===>
  ∀ (a b c d : Bool), Blaster.dite' (true = c) (λ _ => a = !b) (λ _ => b = !d)

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if c then (40 + x) - 40 else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteAbsorptionUnchanged_8" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if c then (40 + x) - 40 else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z

-- ∀ (c : Bool), if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), Blaster.dite' (true = c) (λ _ =>  ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)
#testOptimize [ "IteAbsorptionUnchanged_9" ]
  ∀ (c : Bool), if c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool), Blaster.dite' (true = c) (λ _ =>  ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)


/-! Test cases for simplification rule `if True then e1 else e2 ==> e1`. -/

-- ∀ (a b : Prop), if True then a else b ===> ∀ (a : Prop), a
#testOptimize [ "IteTrueCond_1" ] ∀ (a b : Prop), if True then a else b ===> ∀ (a : Prop), a

-- ∀ (a b : Bool), if True then !a else b ===> ∀ (a : Bool), false = a
#testOptimize [ "IteTrueCond_2" ] ∀ (a b : Bool), if True then !a else b ===> ∀ (a : Bool), false = a

-- ∀ (x y z : Nat), (if True then (x + 40) - 40 else y) < z ===> ∀ (x y z : Nat), x < z
#testOptimize [ "IteTrueCond_3" ] ∀ (x y z : Nat), (if True then (x + 40) - 40 else y) < z ===>
                                  ∀ (x z : Nat), x < z

-- if True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===> ∀ (x y : Int), y < x
#testOptimize [ "IteTrueCond_4" ] if True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                  ∀ (x y : Int), y < x

-- ∀ (c : Bool) (a b : Prop), if (! c || c) then a else b ===> ∀ (a : Prop), a
#testOptimize [ "IteTrueCond_5" ] ∀ (c : Bool) (a b : Prop), if (! c) || c then a else b ===>
                                  ∀ (a : Prop), a

-- ∀ (c a b : Prop), if (¬ c ∨ c) then a else b ===> ∀ (a : Prop), a
#testOptimize [ "IteTrueCond_6" ] ∀ (c a b : Prop), [Decidable c] → if (¬ c ∨ c) then a else b ===>
                                  ∀ (a : Prop), a

-- let x := a || a in
-- let y := ! a || x in
-- ∀ (a : Bool) (b c : Prop), if y then b else c ===> ∀ (b : Prop), b
#testOptimize [ "IteTrueCond_7" ]
  ∀ (a : Bool) (b c : Prop), let x := a || a; let y := ! a || x; if y then b else c ===>
  ∀ (b : Prop), b

-- ∀ (a b : Prop), (if True then a else b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_8" ] ∀ (a b : Prop), (if True then a else b) = a ===> True

-- ∀ (a b : Bool), (if True then !a else b) = !a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_9" ] ∀ (a b : Bool), (if True then !a else b) = !a ===> True

-- ∀ (x y z : Nat), ((if True then (x + 40) - 40 else y) < z) = x < z ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_10" ] ∀ (x y z : Nat), ((if True then (x + 40) - 40 else y) < z) = (x < z) ===> True

-- (if True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_11" ] (if True then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (x y : Int), y < x ===> True

-- ∀ (c : Bool) (a b : Prop), (if (! c || c) then a else b) = a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_12" ] ∀ (c : Bool) (a b : Prop), (if (! c) || c then a else b) = a ===> True

-- ∀ (c a b : Prop), if (¬ c ∨ c) then a else b ===> ∀ (c a b : Prop), a
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_13" ] ∀ (c a b : Prop), [Decidable c] → (if (¬ c ∨ c) then a else b) = a ===> True

-- let x := a || a in
-- let y := ! a || x in
-- ∀ (a : Bool) (b c : Prop), (if y then b else c) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteTrueCond_14" ] ∀ (a : Bool) (b c : Prop),
                                     let x := a || a; let y := ! a || x;
                                     (if y then b else c) = b ===> True


/-! Test cases for simplification rule `if False then e1 else e2 ==> e2`. -/

-- ∀ (a b : Prop), if False then a else b ===> ∀ (b : Prop), b
#testOptimize [ "IteFalseCond_1" ] ∀ (a b : Prop), if False then a else b ===> ∀ (b : Prop), b

-- ∀ (a b : Bool), if False then !a else b ===> ∀ (b : Bool), true = b
#testOptimize [ "IteFalseCond_2" ] ∀ (a b : Bool), if False then !a else b ===> ∀ (b : Bool), true = b

-- ∀ (x y z : Nat), (if False then (x + 40) - 40 else y) < z ===> ∀ (y z : Nat), y < z
#testOptimize [ "IteFalseCond_3" ] ∀ (x y z : Nat), (if False then (x + 40) - 40 else y) < z ===>
                                   ∀ (y z : Nat), y < z

-- if False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===> ∀ (z y : Int), z < y
#testOptimize [ "IteFalseCond_4" ] if False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
                                   ∀ (z y : Int), z < y

-- ∀ (c : Bool) (a b : Prop), if (! c && c) then a else b ===> ∀ (b : Prop), b
#testOptimize [ "IteFalseCond_5" ] ∀ (c : Bool) (a b : Prop), if (! c) && c then a else b ===>
                                   ∀ (b : Prop), b

-- ∀ (c a b : Prop), if (¬ c ∧ c) then a else b ===> ∀ (b : Prop), b
#testOptimize [ "IteFalseCond_6" ] ∀ (c a b : Prop), [Decidable c] → if (¬ c ∧ c) then a else b ===>
                                   ∀ (b : Prop), b

-- let x := a && a in
-- let y := ! a && x in
-- ∀ (a : Bool) (b c : Prop), if y then b else c ===> ∀ (c : Prop), c
#testOptimize [ "IteFalseCond_7" ] ∀ (a : Bool) (b c : Prop), let x := a && a; let y := ! a && x; if y then b else c ===>
                                   ∀ (c : Prop), c

-- ∀ (a b : Prop), (if False then a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseCond_8" ] ∀ (a b : Prop), (if False then a else b) = b ===> True

-- ∀ (a b : Bool), (if False then !a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseCond_9" ] ∀ (a b : Bool), (if False then !a else b) = b ===> True

-- ∀ (x y z : Nat), ((if False then (x + 40) - 40 else y) < z) = (y < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseCond_10" ] ∀ (x y z : Nat), ((if False then (x + 40) - 40 else y) < z) = (y < z) ===> True

-- (if False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (z y : Int), z < y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseCond_11" ] (if False then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) = ∀ (z y : Int), z < y ===> True

-- ∀ (c : Bool) (a b : Prop), (if (! c && c) then a else b) = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseCond_12" ] ∀ (c : Bool) (a b : Prop), (if (! c) && c then a else b) = b ===> True

-- ∀ (c a b : Prop), (if (¬ c ∧ c) then a else b) = b ===> True
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "IteFalseCond_13" ] ∀ (c a b : Prop), [Decidable c] → (if (¬ c ∧ c) then a else b) = b ===> True

-- let x := a && a in
-- let y := ! a && x in
-- ∀ (a : Bool) (b c : Prop), (if y then b else c) = c ===> True
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "IteFalseCond_14" ] ∀ (a : Bool) (b c : Prop),
                                     let x := a && a; let y := ! a && x;
                                     (if y then b else c) = c ===> True



/-! Test cases to ensure that the following simplification rules are not wrongly applied:
     - `if True then e1 else e2 ==> e1`
     - `if False then e1 else e2 ==> e2`
 -/

-- ∀ (a b : Bool) (p q : Prop), if (! a || a) && b then p else q ===>
-- ∀ (b : Bool) (p q : Prop), Blaster.dite' (true = b) (λ _ => p) (λ _ => q)
#testOptimize [ "IteCondUnchanged_1" ]
  ∀ (a b : Bool) (p q : Prop), if (! a || a) && b then p else q ===>
  ∀ (b : Bool) (p q : Prop), Blaster.dite' (true = b) (λ _ => p) (λ _ => q)

-- ∀ (a b c d : Bool), (if (b && !b) || a then c else d) = true ===>
-- ∀ (a c d : Bool), Blaster.dite' (true = a) (λ _ => true = c) (λ _ => true = d)
#testOptimize [ "IteCondUnchanged_2" ]
  ∀ (a b c d : Bool), (if (b && !b) || a then c else d) = true ===>
  ∀ (a c d : Bool), Blaster.dite' (true = a) (λ _ => true = c) (λ _ => true = d)

-- ∀ (a : Bool) (b : Prop) (x y z : Nat), [Decidable b] →
--   (if b && (a || !a) then (x + 40) - 40 else y) < z ===>
-- ∀ (b : Prop) (x y z : Nat), Blaster.dite' b (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteCondUnchanged_3" ]
  ∀ (a : Bool) (b : Prop) (x y z : Nat), [Decidable b] →
    (if b && (a || !a) then (x + 40) - 40 else y) < z ===>
  ∀ (b : Prop) (x y z : Nat), Blaster.dite' b (λ _ => x) (λ _ => y) < z

-- ∀ (a b : Prop) (p q : Prop), if (¬ a ∨ a) ∧ b then p else q ===>
-- ∀ (b : Prop) (p q : Prop), Blaster.dite' b (λ _ => p) (λ _ => q)
#testOptimize [ "IteCondUnchanged_4" ]
  ∀ (a b : Prop) (p q : Prop), [Decidable a] → [Decidable b] → if (¬ a ∨ a) ∧ b then p else q ===>
  ∀ (b : Prop) (p q : Prop), Blaster.dite' b (λ _ => p) (λ _ => q)

-- ∀ (a b : Prop) (c d : Bool), (if (b ∧ ¬ b) ∨ a then c else d) = true ===>
-- ∀ (a : Prop) (c d : Bool), Blaster.dite' a (λ _ => true = c) (λ _ => true = d)
#testOptimize [ "IteCondUnchanged_5" ]
  ∀ (a b : Prop) (c d : Bool),
    [Decidable a] → [Decidable b] → (if (b ∧ ¬ b) ∨ a then c else d) = true ===>
  ∀ (a : Prop) (c d : Bool), Blaster.dite' a (λ _ => true = c) (λ _ => true = d)

-- ∀ (a b : Prop) (x y z : Nat), [Decidable a] → [Decidable b] →
--   (if b ∧ (a ∨ ¬ a) then (x + 40) - 40 else y) < z ===>
-- ∀ (b : Prop) (x y z : Nat), Blaster.dite' b (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteCondUnchanged_6" ]
  ∀ (a b : Prop) (x y z : Nat), [Decidable a] → [Decidable b] →
    (if b ∧ (a ∨ ¬ a) then (x + 40) - 40 else y) < z ===>
  ∀ (b : Prop) (x y z : Nat), Blaster.dite' b (λ _ => x) (λ _ => y) < z


/-! Test cases for simplification rule `if c then e1 else e2 ==> if c' then e2 else e1 (if c := ¬ c')`. -/

-- ∀ (a b c : Prop), if ¬ c then a else b ===>
-- ∀ (a b c : Prop), Blaster.dite' c (λ _ => b) (λ _ => a)
#testOptimize [ "IteNegCond_1" ]
  ∀ (a b c : Prop), [Decidable c] → if ¬ c then a else b ===>
  ∀ (a b c : Prop), Blaster.dite' c (λ _ => b) (λ _ => a)

-- ∀ (c : Prop) (a b : Bool), (if ¬ c then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), Blaster.dite' c (λ _ => true = b) (λ _ => true = a)
#testOptimize [ "IteNegCond_2" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if ¬ c then a else b) = true ===>
  ∀ (c : Prop) (a b : Bool), Blaster.dite' c (λ _ => true = b) (λ _ => true = a)

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z
#testOptimize [ "IteNegCond_3" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ c then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z

-- ∀ (c : Prop), if ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop), Blaster.dite' c (λ _ => ∀ (z y : Int), z < y) (λ _ => ∀ (x y : Int), y < x)
#testOptimize [ "IteNegCond_4" ]
  ∀ (c : Prop), [Decidable c] → if ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Prop), Blaster.dite' c (λ _ => ∀ (z y : Int), z < y) (λ _ => ∀ (x y : Int), y < x)

-- ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = False then x else y) > x ===>
-- ∀ (c : Prop) (x y : Int), x < Blaster.dite' c (λ _ => y) (λ _ => x)
#testOptimize [ "IteNegCond_5" ]
  ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = False then x else y) > x ===>
  ∀ (c : Prop) (x y : Int), x < Blaster.dite' c (λ _ => y) (λ _ => x)

-- ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
--   (if ¬ (a = b) then x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int), x <Blaster.dite' (a = b) (λ _ => y) (λ _ => x)
#testOptimize [ "IteNegCond_6" ]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
    (if ¬ (a = b) then x else y) > x ===>
  ∀ (a b : Prop) (x y : Int), x <Blaster.dite' (a = b) (λ _ => y) (λ _ => x)

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ (¬ c)) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z
#testOptimize [ "IteNegCond_7" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ (¬ c)) then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z

-- ∀ (a b c : Prop), [Decidable c] → (if ¬ c then a else b) = if c then b else a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_8" ] ∀ (a b c : Prop), [Decidable c] → (if ¬ c then a else b) = if c then b else a ===> True

-- ∀ (c : Prop) (a b : Bool), (if ¬ c then a else b) = (if c then b else a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_9" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if ¬ c then a else b) = (if c then b else a) ===> True

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] →
--   ((if ¬ c then x else y) < z) = ((if c then y else x) < z) ==> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_10" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] →
    ((if ¬ c then x else y) < z) = ((if c then y else x) < z) ===> True

-- ∀ (c : Prop), [Decidable c] →
-- if ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z =
-- if c then ∀ (z y : Int), y > z else ∀ (x y : Int), x > y ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_11" ]
  ∀ (c : Prop), [Decidable c] →
    (if ¬ c then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
    (if c then ∀ (z y : Int), y > z else ∀ (x y : Int), x > y) ===> True

-- ∀ (c : Prop) (x y : Int), ((if c = False then x else y) > x) = (x < (if c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_12" ]
  ∀ (c : Prop) (x y : Int), [Decidable c] →
    ((if c = False then x else y) > x) = (x < (if c then y else x)) ===> True

-- ∀ (a b : Prop) (x y : Int), ((if ¬ ( a = b ) then x else y) > x) = x < (if a = b then y else x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_13" ]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
    ((if ¬ (a = b) then x else y) > x) = (x < (if (a = b) then y else x)) ===> True

-- ∀ (c : Prop) (x y z : Nat), ((if ¬ (¬ (¬ c)) then x else y) < z) = ((if c then y else x) < z) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteNegCond_14" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] →
    ((if ¬ (¬ (¬ c)) then x else y) < z) = ((if c then y else x) < z) ===> True


/-! Test cases to ensure that simplification rule `if c then e1 else e2 ==> if c' then e2 else e1 (if c := ¬ c')`
    is not applied wrongly.
-/

-- ∀ (a b c : Prop), if ¬ (¬ c) then a else b ===>
-- ∀ (a b c : Prop), Blaster.dite' c (λ _ => a) (λ _ => b)
#testOptimize [ "IteNegCondUnchanged_1" ]
  ∀ (a b c : Prop), [Decidable c] → if ¬ (¬ c) then a else b ===>
  ∀ (a b c : Prop), Blaster.dite' c (λ _ => a) (λ _ => b)

-- ∀ (c : Prop) (a b : Bool), (if ¬ (¬ c) then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), Blaster.dite' c (λ _ => true = a) (λ _ => true = b)
#testOptimize [ "IteNegCondUnchanged_2" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if ¬ (¬ c) then a else b) = true ===>
  ∀ (c : Prop) (a b : Bool), Blaster.dite' c (λ _ => true = a) (λ _ => true = b)

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ c) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteNegCondUnchanged_3" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ c) then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z

-- ∀ (c : Prop), [Decidable c] → if ¬ (¬ c) then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Prop), Blaster.dite' c (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)
#testOptimize [ "IteNegCondUnchanged_4" ]
  ∀ (c : Prop), [Decidable c] → if ¬ (¬ c) then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Prop), Blaster.dite' c (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)

-- ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = True then x else y) > x ===>
-- ∀ (c : Prop) (x y : Int), x < Blaster.dite' c (λ _ => x) (λ _ => y)
#testOptimize [ "IteNegCondUnchanged_5" ]
  ∀ (c : Prop) (x y : Int), [Decidable c] → (if c = True then x else y) > x ===>
  ∀ (c : Prop) (x y : Int), x < Blaster.dite' c (λ _ => x) (λ _ => y)

-- ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if ¬ (¬ (a = b)) then x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int), x < Blaster.dite' (a = b) (λ _ => x) (λ _ => y)
#testOptimize [ "IteNegCondUnchanged_6" ]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → (if ¬ (¬ (a = b)) then x else y) > x ===>
  ∀ (a b : Prop) (x y : Int), x < Blaster.dite' (a = b) (λ _ => x) (λ _ => y)

-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ (¬ (¬ c))) then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteNegCondUnchanged_7" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ (¬ (¬ (¬ c))) then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z



/-! Test cases for simplification rule `if c then e1 else e2 ==> if true = c' then e2 else e1 (if c := false = c')`. -/

-- ∀ (c : Bool) (p q : Prop), (if c = false then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => q) (λ _ => p)
#testOptimize [ "IteFalseEqCond_1" ]
  ∀ (c : Bool) (p q : Prop), (if c = false then p else q) ===>
  ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => q) (λ _ => p)

-- ∀ (a b c : Bool), (if c = false then a else b) = true ===>
-- ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = b) (λ _ => true = a)
#testOptimize [ "IteFalseEqCond_2" ]
  ∀ (a b c : Bool), (if c = false then a else b) = true ===>
  ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = b) (λ _ => true = a)

-- ∀ (c : Bool) (x y : Nat), (if c = false then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)
#testOptimize [ "IteFalseEqCond_3" ]
  ∀ (c : Bool) (x y : Nat), (if c = false then x else y) > x ===>
  ∀ (c : Bool) (x y : Nat),
    x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)


-- ∀ (c : Bool), if c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (z y : Int), z < y) (λ _ => ∀ (x y : Int), y < x)
#testOptimize [ "IteFalseEqCond_4" ]
  ∀ (c : Bool), if c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (z y : Int), z < y) (λ _ => ∀ (x y : Int), y < x)


-- ∀ (c : Bool) (x y : Int), (if !c then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)
#testOptimize [ "IteFalseEqCond_5" ]
  ∀ (c : Bool) (x y : Int), (if !c then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)

-- ∀ (c : Bool) (x y : Int), (if c == false then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)
#testOptimize [ "IteFalseEqCond_6" ]
  ∀ (c : Bool) (x y : Int), (if c == false then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)


-- ∀ (c : Bool) (x y : Int), (if !(! (! c)) then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)
#testOptimize [ "IteFalseEqCond_7" ]
  ∀ (c : Bool) (x y : Int), (if ! (! (! c)) then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)

-- ∀ (a b : Bool) (x y : Int), (if a = (! b && b ) then x else y) > x ===>
-- ∀ (a : Bool) (x y : Int), x < Blaster.dite' (true = a) (λ _ => y) (λ _ => x)
#testOptimize [ "IteFalseEqCond_8" ]
  ∀ (a b : Bool) (x y : Int), (if a = (! b && b) then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool) (m n : Int), (if y then m else n) > m ===>
-- ∀ (a : Bool) (m n : Int), m < Blaster.dite' (true = a) (λ _ => n) (λ _ => m)
#testOptimize [ "IteFalseEqCond_9" ]
  ∀ (a : Bool) (m n : Int), let x := a || a; let y := ! a || ! x;
    (if y then m else n) > m ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => y) (λ _ => x)


-- ∀ (c : Bool) (p q : Prop), (if c = false then p else q) = (if c then q else p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_10" ]
  ∀ (c : Bool) (p q : Prop), (if c = false then p else q) = if c then q else p ===> True

-- ∀ (a b c : Bool), (if c = false then a else b) = if c then b else a ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_11" ]
  ∀ (a b c : Bool), (if c = false then a else b) = if c then b else a ===> True

-- ∀ (c : Bool) (x y : Nat), ((if c = false then x else y) > x) = (x < (if c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_12" ]
  ∀ (c : Bool) (x y : Nat), ((if c = false then x else y) > x) = (x < (if c then y else x)) ===> True

-- ∀ (c : Bool),
-- (if c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
-- if c then  ∀ (z y : Int), z < y else ∀ (x y : Int), y < x ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_13" ]
  ∀ (c : Bool),
    (if c = false then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z) =
    if c then ∀ (z y : Int), z < y else ∀ (x y : Int), y < x ===> True


-- ∀ (c : Bool) (x y : Int), ((if !c then x else y) > x) = (x < if c then y else x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_14" ]
  ∀ (c : Bool) (x y : Int),
    ((if !c then x else y) > x) = (x < (if c then y else x)) ===> True

-- ∀ (c : Bool) (x y : Int), ((if c == false then x else y) > x) = (x < (if c then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_15" ]
  ∀ (c : Bool) (x y : Int),
    ((if c == false then x else y) > x) = (x < (if true = c then y else x)) ===> True

-- ∀ (c : Bool) (x y : Int), ((if !(! (! c)) then x else y) > x) = (x < (if c then y else x))
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_16" ]
  ∀ (c : Bool) (x y : Int),
    ((if ! (! (! c)) then x else y) > x) = (x < (if c then y else x)) ===> True

-- ∀ (a b : Bool) (x y : Int), ((if a = (! b && b ) then x else y) > x) = (x < (if a then y else x)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_17" ]
  ∀ (a b : Bool) (x y : Int),
    ((if a = (! b && b) then x else y) > x) = (x < (if a then y else x)) ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ∀ (a : Bool) (m n : Int), ((if y then m else n) > m) = (m < (if a then n else m)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteFalseEqCond_18" ]
  ∀ (a : Bool) (m n : Int),
    let x := a || a; let y := ! a || ! x;
    ((if y then m else n) > m) = (m < (if a then n else m)) ===> True



/-! Test cases to ensure that simplification rule `if c then e1 else e2 ==> if true = c' then e2 else e1 (if c := false = c')`
    is not applied wrongly.
-/

-- ∀ (c : Bool) (p q : Prop), (if c = true then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => p) (λ _ => q)
#testOptimize [ "IteFalseEqCondUnchanged_1" ]
  ∀ (c : Bool) (p q : Prop), (if c = true then p else q) ===>
  ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => p) (λ _ => q)

-- ∀ (a b c : Bool), (if c = true then a else b) = true ===>
-- ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = a) (λ _ => true = b)
#testOptimize [ "IteFalseEqCondUnchanged_2" ]
  ∀ (a b c : Bool), (if c = true then a else b) = true ===>
  ∀ (a b c : Bool), Blaster.dite' (true = c) (λ _ => true = a) (λ _ => true = b)

-- ∀ (c : Bool) (x y : Nat), (if c = true then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteFalseEqCondUnchanged_3" ]
  ∀ (c : Bool) (x y : Nat), (if c = true then x else y) > x ===>
  ∀ (c : Bool) (x y : Nat), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)

-- ∀ (c : Bool), if c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)
#testOptimize [ "IteFalseEqCondUnchanged_4" ]
  ∀ (c : Bool), if c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)

-- ∀ (a b : Bool) (p q : Prop), (if a = b then p else q) ===>
-- ∀ (a b : Bool) (p q : Prop), Blaster.dite' (a = b) (λ _ => p) (λ _ => q)
#testOptimize [ "IteFalseEqCondUnchanged_5" ]
  ∀ (a b : Bool) (p q : Prop), (if a = b then p else q) ===>
  ∀ (a b : Bool) (p q : Prop), Blaster.dite' (a = b) (λ _ => p) (λ _ => q)

-- ∀ (a b c d : Bool), (if a = b then c else d) = true ===>
-- ∀ (a b c d : Bool), Blaster.dite' (a = b) (λ _ => true = c) (λ _ => true = d)
#testOptimize [ "IteFalseEqCondUnchanged_6" ]
  ∀ (a b c d : Bool), (if a = b then c else d) = true ===>
  ∀ (a b c d : Bool), Blaster.dite' (a = b) (λ _ => true = c) (λ _ => true = d)

-- ∀ (a b : Bool) (x y : Nat), (if a = b then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Nat), x < Blaster.dite' (a = b) (λ _ => x) (λ _ => y)
#testOptimize [ "IteFalseEqCondUnchanged_7" ]
  ∀ (a b : Bool) (x y : Nat), (if a = b then x else y) > x ===>
  ∀ (a b : Bool) (x y : Nat), x < Blaster.dite' (a = b) (λ _ => x) (λ _ => y)

-- ∀ (c : Bool), if c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
-- ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)
#testOptimize [ "IteFalseEqCondUnchanged_8" ]
  ∀ (c : Bool), if c = true then ∀ (x y : Int), x > y else ∀ (z y : Int), y > z ===>
  ∀ (c : Bool), Blaster.dite' (true = c) (λ _ => ∀ (x y : Int), y < x) (λ _ => ∀ (z y : Int), z < y)


-- ∀ (c : Bool) (x y : Int), (if !(!c) then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteFalseEqCondUnchanged_9" ]
  ∀ (c : Bool) (x y : Int), (if !(!c) then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)

-- ∀ (c : Bool) (x y : Int), (if c == true then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteFalseEqCondUnchanged_10" ]
  ∀ (c : Bool) (x y : Int), (if c == true then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)

-- ∀ (c : Bool) (x y : Int), (if !(!(! (! c))) then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteFalseEqCondUnchanged_11" ]
  ∀ (c : Bool) (x y : Int), (if !(! (! (! c))) then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)


-- ∀ (a b : Bool) (x y : Int), (if a = (! b || b ) then x else y) > x ===>
-- ∀ (a : Bool) (x y : Int), x < Blaster.dite' (true = a) (λ _ => x) (λ _ => y)
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "IteFalseEqCondUnchanged_12" ]
  ∀ (a b : Bool) (x y : Int), (if a = (! b || b) then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)

-- let x := a && a in
-- let y := a || x in
-- ∀ (a : Bool) (m n : Int), (if y then m else n) > m ===>
-- ∀ (a : Bool) (m n : Int), m < Blaster.dite' (true = a) (λ _ => m) (λ _ => n)
#testOptimize [ "IteFalseEqCondUnchanged_13" ]
  ∀ (a : Bool) (m n : Int), let x := a && a; let y := a || x;
      (if y then m else n) > m ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)



/-! Test cases for simplification rule `if c then e1 else e2 ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`.
    NOTE: No more applicable. We keep ite to reduce complexity.
    NOTE: Additional simplification will be handled via the implementation of by_cases in Blaster.
-/

-- ∀ (c p q : Prop), if c then p else q ===>
-- ∀ (c p q : Prop), Blaster.dite' c (λ _ => p) (λ _ => q)
#testOptimize [ "IteToPropExpr_1" ]
  ∀ (c p q : Prop), [Decidable c] → if c then p else q ===>
  ∀ (c p q : Prop), Blaster.dite' c (λ _ => p) (λ _ => q)

-- ∀ (c p : Prop), if c then True else p ===> ∀ (c p : Prop), ¬ c → p
#testOptimize [ "IteToPropExpr_2" ]
  ∀ (c p : Prop), [Decidable c] → if c then True else p ===>
  ∀ (c p : Prop),  (¬ c) → p

-- ∀ (c p : Prop), if c then p else True ===> ∀ (c p : Prop), c → p
#testOptimize [ "IteToPropExpr_3" ] ∀ (c p : Prop), [Decidable c] → if c then p else True ===>
                                    ∀ (c p : Prop),  c → p


-- ∀ (c p : Prop), if c then False else p ===>
-- ∀ (c p : Prop), p ∧ ¬ c
#testOptimize [ "IteToPropExpr_4" ] ∀ (c p : Prop), [Decidable c] → if c then False else p ===>
                                    ∀ (c p : Prop), p ∧ ¬ c

-- ∀ (c p : Prop), if c then p else False ===>
-- ∀ (c p : Prop), c ∧ p
#testOptimize [ "IteToPropExpr_5" ] ∀ (c p : Prop), [Decidable c] → if c then p else False ===>
                                    ∀ (c p : Prop), c ∧ p

-- ∀ (c p : Prop), if c then c else p ===>
-- ∀ (c p : Prop), ¬ c → p
#testOptimize [ "IteToPropExpr_6" ] ∀ (c p : Prop), [Decidable c] → if c then c else p ===>
                                    ∀ (c p : Prop), ¬ c → p

-- ∀ (c p : Prop), if c then p else c ===>
-- ∀ (c p : Prop), c ∧ p
#testOptimize [ "IteToPropExpr_7" ] ∀ (c p : Prop), [Decidable c] → if c then p else c ===>
                                    ∀ (c p : Prop), c ∧ p

-- ∀ (c p : Prop), if c then ¬ c else p ===>
-- ∀ (c p : Prop), p ∧ ¬ c
#testOptimize [ "IteToPropExpr_8" ] ∀ (c p : Prop), [Decidable c] → if c then ¬ c else p ===>
                                    ∀ (c p : Prop), p ∧ ¬ c

-- ∀ (c p : Prop), if c then p else ¬ c ===>
-- ∀ (c p : Prop), c → p
#testOptimize [ "IteToPropExpr_9" ] ∀ (c p : Prop), [Decidable c] → if c then p else ¬ c ===>
                                    ∀ (c p : Prop), c → p

-- ∀ (c p q : Prop), if ¬ c then p else q ===>
-- ∀ (c p q : Prop), Blaster.dite' c (λ _ => q) (λ _ => p)
#testOptimize [ "IteToPropExpr_10" ]
  ∀ (c p q : Prop), [Decidable c] → if ¬ c then p else q ===>
  ∀ (c p q : Prop), Blaster.dite' c (λ _ => q) (λ _ => p)


-- ∀ (c : Bool) (p q : Prop), if c then p else q ===>
-- ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => p) (λ _ => q)
#testOptimize [ "IteToPropExpr_11" ]
  ∀ (c : Bool) (p q : Prop), if c then p else q ===>
  ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => p) (λ _ => q)

-- ∀ (c : Bool) (p : Prop), if c then True else p ===>
-- ∀ (c p : Prop), false = c → p
#testOptimize [ "IteToPropExpr_12" ] ∀ (c : Bool) (p : Prop), if c then True else p ===>
                                     ∀ (c : Bool) (p : Prop), false = c → p

-- ∀ (c : Bool) (p : Prop), if c then p else True ===>
-- ∀ (c : Bool) (p : Prop), true = c → p
#testOptimize [ "IteToPropExpr_13" ] ∀ (c : Bool) (p : Prop), if c then p else True ===>
                                     ∀ (c : Bool) (p : Prop), true = c → p

-- ∀ (c : Bool) (p : Prop), if c then False else p ===>
-- ∀ (c : Bool) (p : Prop), p ∧ false = c
#testOptimize [ "IteToPropExpr_14" ] ∀ (c : Bool) (p : Prop), if c then False else p ===>
                                     ∀ (c : Bool) (p : Prop), p ∧ false = c

-- ∀ (c : Bool) (p : Prop), if c then p else False ===>
-- ∀ (c : Bool) (p : Prop), p ∧ true = c
#testOptimize [ "IteToPropExpr_15" ] ∀ (c : Bool) (p : Prop), if c then p else False ===>
                                     ∀ (c : Bool) (p : Prop), p ∧ true = c

-- ∀ (c : Bool) (p : Prop), if c then c else p ===>
-- ∀ (c : Bool) p : Prop), false = c → p
#testOptimize [ "IteToPropExpr_16" ] ∀ (c : Bool) (p : Prop), if c then c else p ===>
                                     ∀ (c : Bool) (p : Prop), false = c → p

-- ∀ (c : Bool) (p : Prop), if c then p else c ===>
-- ∀ (c : Bool) (p : Prop), p ∧ true = c
#testOptimize [ "IteToPropExpr_17" ] ∀ (c : Bool) (p : Prop), if c then p else c ===>
                                     ∀ (c : Bool) (p : Prop), p ∧ true = c

-- ∀ (c : Bool) (p : Prop), if c then !c else p ===>
-- ∀ (c : Bool) (p : Prop), p ∧ false = c
#testOptimize [ "IteToPropExpr_18" ] ∀ (c : Bool) (p : Prop), if c then !c else p ===>
                                     ∀ (c : Bool) (p : Prop), p ∧ false = c

-- ∀ (c : Bool) (p : Prop), if c then p else !c ===>
-- ∀ (c : Bool) p : Prop), true = c → p
-- TODO: remove unused constraints when COI performed on forall
#testOptimize [ "IteToPropExpr_19" ] ∀ (c : Bool) (p : Prop), if c then p else !c ===>
                                     ∀ (c : Bool) (p : Prop), true = c → p

-- ∀ (c : Bool) (p q : Prop), (if !c then p else q) ===>
-- ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => q) (λ _ => p)
#testOptimize [ "IteToPropExpr_20" ]
  ∀ (c : Bool) (p q : Prop), if !c then p else q ===>
  ∀ (c : Bool) (p q : Prop), Blaster.dite' (true = c) (λ _ => q) (λ _ => p)


-- ∀ (c p q : Prop), (if c then p else q) → ((c → p) ∧ (¬ c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_21" ]
  ∀ (c p q : Prop), [Decidable c] → (if c then p else q) → ((c → p) ∧ (¬ c → q)) ===> True

-- ∀ (c p : Prop), (if c then True else p) = (¬ c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_22" ]
∀ (c p : Prop), [Decidable c] → (if c then True else p) = ((¬ c) → p) ===> True

-- ∀ (c p : Prop), (if c then p else True) = (c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_23" ]
  ∀ (c p : Prop), [Decidable c] → (if c then p else True) = (c → p) ===> True

-- ∀ (c p : Prop), (if c then False else p) = ((c → False) ∧ (¬ c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_24" ]
  ∀ (c p : Prop), [Decidable c] → (if c then False else p) = ((c → False) ∧ (¬ c → p)) ===> True

-- ∀ (c p : Prop), (if c then p else False) = ((c → p) ∧ (¬ c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_25" ]
∀ (c p : Prop), [Decidable c] → (if c then p else False) = ((c → p) ∧ (¬ c → False)) ===> True

-- ∀ (c p : Prop), (if c then c else p) = (¬ c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_26" ]
  ∀ (c p : Prop), [Decidable c] → (if c then c else p) = (¬ c → p) ===> True

-- ∀ (c p : Prop), (if c then p else c) = (c ∧ (c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_27" ]
  ∀ (c p : Prop), [Decidable c] → (if c then p else c) = (c ∧ (c → p)) ===> True

-- ∀ (c p : Prop), (if c then ¬ c else p) = ((¬ c → p) ∧ ¬ c) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_28" ]
  ∀ (c p : Prop), [Decidable c] → (if c then ¬ c else p) = ((¬ c → p) ∧ ¬ c) ===> True

-- ∀ (c p : Prop), (if c then p else ¬ c) = (c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_29" ]
  ∀ (c p : Prop), [Decidable c] → (if c then p else ¬ c) = (c → p) ===> True

-- ∀ (c p q : Prop), (if ¬ c then p else q) → ((¬ c → p) ∧ (c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_30" ]
  ∀ (c p q : Prop), [Decidable c] → (if ¬ c then p else q) → ((¬ c → p) ∧ (c → q)) ===> True

-- ∀ (c : Bool) (p q : Prop), (if c then p else q) → ((true = c → p) ∧ (false = c → q)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_31" ]
  ∀ (c : Bool) (p q : Prop), (if c then p else q) → ((true = c → p) ∧ (false = c → q)) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then True else p) = (false = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_32" ]
  ∀ (c : Bool) (p : Prop), (if c then True else p) = (false = c → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then p else True) = (true = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_33" ]
  ∀ (c : Bool) (p : Prop), (if c then p else True) = (true = c → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then False else p) = ((false = c → p) ∧ (true = c → False)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_34" ]
  ∀ (c : Bool) (p : Prop),
    (if c then False else p) = ((false = c → p) ∧ (true = c → False)) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then p else False) = ((false = c → False) ∧ (true = c → p)) ===> True
#testOptimize [ "IteToPropExpr_35" ]
  ∀ (c : Bool) (p : Prop),
    (if c then p else False) = ((false = c → False) ∧ (true = c → p)) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then true = c else p) = (false = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_36" ]
  ∀ (c : Bool) (p : Prop), (if c then true = c else p) = ((false = c) → p) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then p else c) = ((true = c → p) ∧ (true = c)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_37" ]
  ∀ (c : Bool) (p : Prop), (if c then p else c) = ((true = c → p) ∧ (true = c)) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then true = !c else p) = ((false = c) ∧ (false = c → p)) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_38" ]
  ∀ (c : Bool) (p : Prop), (if c then true = !c else p) = ((false = c) ∧ (false = c → p)) ===> True

-- ∀ (c : Bool) (p : Prop), (if c then p else true = !c) = (true = c → p) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "IteToPropExpr_39" ]
  ∀ (c : Bool) (p : Prop), (if c then p else true = !c) = (true = c → p) ===> True

-- ∀ (c : Bool) (p q : Prop), (if !c then p else q) → ((false = c → p) ∧ (true = c → q)) ===> True
#testOptimize [ "IteToPropExpr_40" ]
  ∀ (c : Bool) (p q : Prop), (if !c then p else q) → ((true = c → q) ∧ (false = c → p)) ===> True

/-! Test cases to ensure that simplification rule `if c then e1 else e2 ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)`
    is not applied wrongly.
 -/


-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteToPropExprUnchanged_1" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if c then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => x) (λ _ => y) < z

-- ∀ (a b : Bool) (x y z : Nat), (if a = b then x else y) < z ===>
-- ∀ (a b : Bool) (x y z : Nat), Blaster.dite' (a = b) (λ _ => x) (λ _ => y) < z
#testOptimize [ "IteToPropExprUnchanged_2" ]
  ∀ (a b : Bool) (x y z : Nat), (if a = b then x else y) < z ===>
  ∀ (a b : Bool) (x y z : Nat), Blaster.dite' (a = b) (λ _ => x) (λ _ => y) < z


-- ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ c then x else y) < z ===>
-- ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z
#testOptimize [ "IteToPropExprUnchanged_3" ]
  ∀ (c : Prop) (x y z : Nat), [Decidable c] → (if ¬ c then x else y) < z ===>
  ∀ (c : Prop) (x y z : Nat), Blaster.dite' c (λ _ => y) (λ _ => x) < z

-- ∀ (a b : Bool) (x y z : Nat), (if !(a == b) then x else y) < z ===>
-- ∀ (a b : Bool) (x y z : Nat), Blaster.dite' (a = b) (λ _ => y) (λ _ => x) < z
#testOptimize [ "IteToPropExprUnchanged_4" ]
  ∀ (a b : Bool) (x y z : Nat), (if !(a == b) then x else y) < z ===>
  ∀ (a b : Bool) (x y z : Nat), Blaster.dite' (a = b) (λ _ => y) (λ _ => x) < z

-- ∀ (a b : Bool) (x y : Int), (if a = b then -x else x) > y ===>
-- ∀ (a b : Bool) (x y : Int), y < Blaster.dite' (a = b) (λ _ => Int.neg x) (λ _ => x)
#testOptimize [ "IteToPropExprUnchanged_5" ]
  ∀ (a b : Bool) (x y : Int), (if a = b then -x else x) > y ===>
  ∀ (a b : Bool) (x y : Int), y < Blaster.dite' (a = b) (λ _ => Int.neg x) (λ _ => x)

-- ∀ (a b : Bool) (x y : Int), let p := x + y; let q := x - y;
--   (if a = b then p else q) > x ===>
-- ∀ (a b : Bool) (x y : Int),
--   x < Blaster.dite' (a = b) (λ _ => Int.add x y) (λ _ => Int.add x (Int.neg y))
#testOptimize [ "IteToPropExprUnchanged_6" ]
  ∀ (a b : Bool) (x y : Int), let p := x + y; let q := x - y;
    (if a = b then p else q) > x ===>
  ∀ (a b : Bool) (x y : Int),
    x < Blaster.dite' (a = b) (λ _ => Int.add x y) (λ _ => Int.add x (Int.neg y))

-- ∀ (a b c : Bool) (x y : Int), (if c = ((! a) || b) then x else y) > x ===>
-- ∀ (a b c : Bool) (x y : Int), x < Blaster.dite' (c = ( b || !a)) (λ _ => x) (λ _ => y)
#testOptimize [ "IteToPropExprUnchanged_7" ]
  ∀ (a b c : Bool) (x y : Int), (if c = ((! a) || b) then x else y) > x ===>
  ∀ (a b c : Bool) (x y : Int), x < Blaster.dite' (c = ( b || !a)) (λ _ => x) (λ _ => y)

-- ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
--   (if (¬ a ∨ b) then x else y) > x ===>
-- ∀ (a b : Prop) (x y : Int), x < Blaster.dite' (b ∨ ¬ a) (λ _ => x) (λ _ => y)
#testOptimize [ "IteToPropExprUnchanged_8" ]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
    (if (¬ a ∨ b) then x else y) > x ===>
  ∀ (a b : Prop) (x y : Int), x < Blaster.dite' (b ∨ ¬ a) (λ _ => x) (λ _ => y)

-- ∀ (a : Prop) (c b : Bool), [Decidable a] → (if c then a else b) = (if c then decide a else b) ===> True
#testOptimize [ "IteToPropExprUnchanged_9" ]
  ∀ (a : Prop) (c b : Bool), [Decidable a] → (if c then a else b) = if c then decide a else b ===> True


-- ∀ (c : Bool) (x y : Nat), (if c then x else y) > x ===>
-- ∀ (c : Bool) (x y : Nat), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteToPropExprUnchanged_10" ]
  ∀ (c : Bool) (x y : Nat), (if c then x else y) > x ===>
  ∀ (c : Bool) (x y : Nat), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)

-- ∀ (c : Bool) (x y : Int), (if c then x else y) > x ===>
-- ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)
#testOptimize [ "IteToPropExprUnchanged_11" ]
  ∀ (c : Bool) (x y : Int), (if c then x else y) > x ===>
  ∀ (c : Bool) (x y : Int), x < Blaster.dite' (true = c) (λ _ => x) (λ _ => y)


-- ∀ (a b : Bool) (s t : String), (if a = b then s else t) > s ===>
-- ∀ (a b : Bool) (s t : String), s < Blaster.dite' (a = b) (λ _ => s) (λ _ => t)
#testOptimize [ "IteToPropExprUnchanged_12" ]
  ∀ (a b : Bool) (s t : String), (if a = b then s else t) > s ===>
  ∀ (a b : Bool) (s t : String), s < Blaster.dite' (a = b) (λ _ => s) (λ _ => t)


end Test.OptimizeITE
