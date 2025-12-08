import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.DecideBoolAnd

/-! ## Test objectives to validate `Decidable.decide` simplification rules on Boolean `and`. -/


/-! Test cases for simplification rule `decide e1 && decide e2 ===> decide (e1 ∧ e2)`. -/

variable (x : Int)
variable (y : Int)
variable (z : Int)

-- x ≤ y && z ≥ y ===> Blaster.decide' (¬ y < x ∧ ¬ z < y)
#testOptimize [ "DecideAndDecide_1" ] x ≤ y && z ≥ y ===> Blaster.decide' (¬ y < x ∧ ¬ z < y)

-- (x ≤ y && z ≥ y) = decide (x ≤ y ∧ y ≤ z) ===> True
#testOptimize [ "DecideAndDecide_2" ] (x ≤ y && z ≥ y) = decide (x ≤ y ∧ y ≤ z) ===> True

-- ∀ (x y z : Nat), x ≤ y && z ≥ y ===> ∀ (x y z : Nat), ¬ y < x ∧ ¬ z < y
#testOptimize [ "DecideAndDecide_3" ]
  ∀ (x y z : Nat), x ≤ y && z ≥ y ===> ∀ (x y z : Nat), ¬ y < x ∧ ¬ z < y

-- (x ≤ y && x ≤ y) = decide (x ≤ y) ===> True
#testOptimize [ "DecideAndDecide_4" ] (x ≤ y && x ≤ y) = decide (x ≤ y) ===> True

-- ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), ¬ y < x
#testOptimize [ "DecideAndDecide_5" ] ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- ∀ (x y : Nat), !(x ≤ y) && x ≤ y ===> False
#testOptimize [ "DecideAndDecide_6" ] ∀ (x y : Nat), !x ≤ y && x ≤ y ===> False

-- ∀ (x y : Nat), (x = y) && (x ≠ y) ===> False
#testOptimize [ "DecideAndDecide_7" ] ∀ (x y : Nat), x = y && x ≠ y ===> False

-- ∀ (x y : Nat), !x = y && x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)
#testOptimize [ "DecideAndDecide_8" ] ∀ (x y : Nat), !x = y && x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)

-- ∀ (x y z: Nat), !x = y && x ≠ y && z > y ===> ∀ (x y z : Nat), ¬ (x = y) ∧ y < z
#testOptimize [ "DecideAndDecide_9" ] ∀ (x y z : Nat), !x = y && x ≠ y && z > y ===>
                                      ∀ (x y z : Nat), ¬ (x = y) ∧ (y < z)

-- ∀ (x y m n : Nat), (!x = y && n ≥ m) && (x ≠ y && m ≤ n) ===>
-- ∀ (x y m n : Nat), ¬ (x = y) ∧ ¬ n < m
#testOptimize [ "DecideAndDecide_10" ] ∀ (x y m n : Nat), (!x = y && n ≥ m) && (x ≠ y && m ≤ n) ===>
                                       ∀ (x y m n : Nat), ¬ (x = y) ∧ ¬ n < m


-- ∀ (x y z m n : Nat), (!x = y && n ≥ m) && (x ≠ z && m ≤ z) ===>
-- ∀ (x y z m n : Nat), (¬ (x = y) ∧ ¬ n < m) ∧ (¬ (x = z) ∧ ¬ z < m)
#testOptimize [ "DecideAndDecide_11" ] ∀ (x y z m n : Nat), (!x = y && n ≥ m) && (x ≠ z && m ≤ z) ===>
                                       ∀ (x y z m n : Nat), (¬ (x = y) ∧ ¬ n < m) ∧ (¬ (x = z) ∧ ¬ z < m)

-- ∀ (x y z m n : Nat), x < y && (n ≥ m && (!x > z && m ≤ z)) ===>
-- ∀ (x y z m n : Nat), (¬ n < m ∧ (¬ z < x ∧ ¬ z < m)) ∧ x < y
#testOptimize [ "DecideAndDecide_12" ] ∀ (x y z m n : Nat), x < y && (n ≥ m && (!x > z && m ≤ z)) ===>
                                       ∀ (x y z m n : Nat), (¬ n < m ∧ (¬ z < x ∧ ¬ z < m)) ∧ x < y


-- ∀ (x y z : Nat), (x ≤ y && z ≥ y) = x ≤ y ∧ y ≤ z ===> True
#testOptimize [ "DecideAndDecide_13" ] ∀ (x y z : Nat), (x ≤ y && z ≥ y) = (x ≤ y ∧ y ≤ z) ===> True

-- ∀ (x y : Nat), (x ≤ y && y ≥ x) = x ≤ y ===> True
#testOptimize [ "DecideAndDecide_14" ] ∀ (x y : Nat), (x ≤ y && y ≥ x) = (x ≤ y) ===> True

-- ∀ (x y : Nat), (!x = y && x ≠ y) = ¬ (x = y) ===> True
#testOptimize [ "DecideAndDecide_15" ] ∀ (x y : Nat), (!x = y && x ≠ y) = ¬ (x = y) ===> True


-- ∀ (x y z: Nat), (!x = y && x ≠ y && z > y) = (y < z ∧ ¬ (x = y)) ===> True
#testOptimize [ "DecideAndDecide_16" ] ∀ (x y z: Nat),
                                         (!x = y && x ≠ y && z > y) = (y < z ∧ ¬ (x = y)) ===> True

-- ∀ (x y m n : Nat), ((!x = y && n ≥ m) && (x ≠ y && m ≤ n)) = (n ≥ m ∧ (x ≠ y)) ===> True
#testOptimize [ "DecideAndDecide_17" ] ∀ (x y m n : Nat),
                                         ((!x = y && n ≥ m) && (x ≠ y && m ≤ n)) = (n ≥ m ∧ (x ≠ y)) ===> True


-- ∀ (x y z m n : Nat),
-- ((!x = y && n ≥ m) && (x ≠ z && m ≤ z)) = ((m ≤ n ∧ ¬ (y = x)) ∧ (z ≥ m ∧ (z ≠ x))) ===> True
#testOptimize [ "DecideAndDecide_18" ] ∀ (x y z m n : Nat),
                                         ((!x = y && n ≥ m) && (x ≠ z && m ≤ z)) =
                                         ((m ≤ n ∧ ¬ (y = x)) ∧ (z ≥ m ∧ (z ≠ x))) ===> True

-- ∀ (x y z m n : Nat),
-- (x < y && (n ≥ m && (!x > z && m ≤ z))) = (((¬ (z < x) ∧ z ≥ m) ∧ m ≤ n) ∧ x < y) ===> True
#testOptimize [ "DecideAndDecide_19" ] ∀ (x y z m n : Nat),
                                         (x < y && (n ≥ m && (!x > z && m ≤ z))) =
                                         (((¬ (z < x) ∧ z ≥ m) ∧ m ≤ n) ∧ x < y) ===> True

variable (w : Int)

-- ((decide (x < y) && decide (x < z)) && decide (x < w)) = decide (((x < y) ∧ (x < z)) ∧ (x < w)) ===> True
#testOptimize [ "DecideAndDecide_20" ]
  ((decide (x < y) && decide (x < z)) && decide (x < w)) = decide (((x < y) ∧ (x < z)) ∧ (x < w)) ===> True

-- (decide (x < y) && (decide (x < z) && decide (x < w))) = decide ((x < y) ∧ (x < z) ∧ (x < w)) ===> True
#testOptimize [ "DecideAndDecide_21" ]
  (decide (x < y) && (decide (x < z) && decide (x < w))) = decide ((x < y) ∧ (x < z) ∧ (x < w)) ===> True


/-! Test cases for simplification rule `decide e1 && e2 | e2 && decide e1 ===> decide (e1 ∧ true = e2)`. -/

variable (b : Bool)

-- x ≤ y && b ===> Blaster.decide' (¬ y < x ∧ true = b)
#testOptimize [ "DecideAndBool_1" ] x ≤ y && b ===> Blaster.decide' (¬ y < x ∧ true = b)

-- b && x ≤ y ===> Blaster.decide' (¬ y < x ∧ true = b)
#testOptimize [ "DecideAndBool_2" ] b && x ≤ y ===> Blaster.decide' (¬ y < x ∧ true = b)

-- !b && x ≤ y ===> Blaster.decide' (¬ y < x ∧ false = b)
#testOptimize [ "DecideAndBool_3" ] !b && x ≤ y ===> Blaster.decide' (¬ y < x ∧ false = b)

-- ∀ (x y m n : Nat), x < y && (m == n) ===> ∀ (x y m n : Nat), m = n ∧ x < y
#testOptimize [ "DecideAndBool_4" ] ∀ (x y m n : Nat), x < y && (m == n) ===>
                                    ∀ (x y m n : Nat), m = n ∧ x < y

-- ∀ (m n : Nat), (m = n) && (m == n) ===> ∀ (m n : Nat), m = n
#testOptimize [ "DecideAndBool_5" ] ∀ (m n : Nat), (m = n) && (m == n) ===>
                                    ∀ (m n : Nat), m = n

-- ∀ (x y m n : Nat), x < y && (m != n) ===> ∀ (x y m n : Nat), ¬ m = n ∧ x < y
#testOptimize [ "DecideAndBool_6" ] ∀ (x y m n : Nat), x < y && (m != n) ===>
                                    ∀ (x y m n : Nat), ¬ m = n ∧ x < y

-- ∀ (m n : Nat), (m = n) && (m != n) ===> False
#testOptimize [ "DecideAndBool_7" ] ∀ (m n : Nat), (m = n) && (m != n) ===> False

-- ∀ (m n : Nat), (m ≠ n) && (m == n) ===> False
#testOptimize [ "DecideAndBool_8" ] ∀ (m n : Nat), (m ≠ n) && (m == n) ===> False

-- ∀ (m n : Nat), (m ≠ n) && (m != n) ===> ∀ (m n : Nat), ¬ m = n
#testOptimize [ "DecideAndBool_9" ] ∀ (m n : Nat), (m ≠ n) && (m != n) ===>
                                    ∀ (m n : Nat), ¬ m = n

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (((a ∧ b) ∧ (b ∨ ¬ b)) && c) ===>
-- ∀ (a b : Prop) (c : Bool), (a ∧ b) ∧ true = c
#testOptimize [ "DecideAndBool_10" ] ∀ (a b : Prop) (c : Bool),
                                        [Decidable a] → [Decidable b] → (((a ∧ b) ∧ (b ∨ ¬ b)) && c) ===>
                                     ∀ (a b : Prop) (c : Bool), (a ∧ b) ∧ true = c

-- ∀ (x y z : Nat) (a b c : Bool),
--   (if (x ≤ y ∧ y ≥ x) && ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
-- ∀ (x y z : Nat) (a : Bool),
--   Blaster.dite' (¬ y < x ∧ true = a)
--     (fun _ : ¬ y < x ∧ true = a => x)
--     (fun _ : ¬ (¬ y < x ∧ true = a) => y) < z
#testOptimize [ "DecideAndBool_11" ]
  ∀ (x y z : Nat) (a b c : Bool),
    (if (x ≤ y ∧ y ≥ x) && ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
  ∀ (x y z : Nat) (a : Bool),
    Blaster.dite' (¬ y < x ∧ true = a)
      (fun _ : ¬ y < x ∧ true = a => x)
      (fun _ : ¬ (¬ y < x ∧ true = a) => y) < z

-- ∀ (x y z: Nat), x != y && x ≠ y && Nat.ble z y ===>
-- ∀ (x y z : Nat), ¬ (x = y) ∧ ¬ y < z
#testOptimize [ "DecideAndBool_12" ] ∀ (x y z : Nat), x != y && x ≠ y && Nat.ble z y ===>
                                     ∀ (x y z : Nat), ¬ (x = y) ∧ ¬ y < z


-- ∀ (x y m n : Nat), (x != y && n ≥ m) && (x ≠ y && m ≤ n) ===>
-- ∀ (x y m n : Nat), ¬ (x = y) ∧ ¬ n < m
#testOptimize [ "DecideAndBool_13" ] ∀ (x y m n : Nat), (x != y && n ≥ m) && (x ≠ y && m ≤ n) ===>
                                     ∀ (x y m n : Nat), ¬ (x = y) ∧ ¬ n < m

-- ∀ (x y z m n : Nat), (x != y && Nat.ble n m) && (x ≠ z && m == z) ===>
-- ∀ (x y z m n : Nat), (¬ (x = y) ∧ ¬ m < n) ∧ (¬ (x = z) ∧ z = m)
#testOptimize [ "DecideAndBool_14" ]
  ∀ (x y z m n : Nat), (x != y && Nat.ble n m) && (x ≠ z && m == z) ===>
  ∀ (x y z m n : Nat), (¬ (x = y) ∧ ¬ m < n) ∧ (¬ (x = z) ∧ z = m)


-- ∀ (x y z m n : Nat), ((x != y && m < n) && m == z) && x ≠ z ===>
-- ∀ (x y z m n : Nat), ¬ (x = z) ∧ ((¬ (x = y) ∧ m < n) ∧ z = m)
#testOptimize [ "DecideAndBool_15" ] ∀ (x y z m n : Nat), ((x != y && m < n) && m == z) && x ≠ z ===>
                                     ∀ (x y z m n : Nat), ¬ (x = z) ∧ ((¬ (x = y) ∧ m < n) ∧ z = m)

-- (x ≤ y && b) = decide (true = b ∧ y ≥ x) ===> True
#testOptimize [ "DecideAndBool_16" ] (x ≤ y && b) = decide (true = b ∧ y ≥ x) ===> True

-- (!b && x ≤ y) = decide (y ≥ x ∧ false = b) ===> True
#testOptimize [ "DecideAndBool_17" ] (!b && x ≤ y) = decide (y ≥ x ∧ false = b) ===> True

--  ∀ (x y m n : Nat), (x < y && (m == n)) = (n = m ∧ y > x) ===> True
#testOptimize [ "DecideAndBool_18" ] ∀ (x y m n : Nat), (x < y && (m == n)) = (n = m ∧ y > x) ===> True

-- ∀ (m n : Nat), ((m = n) && (n == m)) = (n = m) ===> True
#testOptimize [ "DecideAndBool_19" ] ∀ (m n : Nat), ((m = n) && (n == m)) = (n = m) ===> True

-- ∀ (x y m n : Nat), (x < y && (m != n)) = (n ≠ m ∧ y > x) ===> True
#testOptimize [ "DecideAndBool_20" ] ∀ (x y m n : Nat), (x < y && (m != n)) = (n ≠ m ∧ y > x) ===> True

-- ∀ (m n : Nat), ((n ≠ m) && (m != n)) = (m ≠ n) ===> True
#testOptimize [ "DecideAndBool_21" ] ∀ (m n : Nat), ((n ≠ m) && (m != n)) = (m ≠ n) ===> True

-- ∀ (a b : Prop) (c : Bool),
--  [Decidable a] → [Decidable b] → (((a ∧ b) ∧ (b ∨ ¬ b)) && c) = (c ∧ (b ∧ a)) ===> True
#testOptimize [ "DecideAndBool_22" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                      (((a ∧ b) ∧ (b ∨ ¬ b)) && c) = (c ∧ (b ∧ a)) ===> True

-- ∀ (x y : Nat) (a b c : Bool),
--  (if (x ≤ y ∧ y ≥ x) && ((a || ((b || c) && !(c || b)))) then x else y) =
--  (if a ∧ (x ≤ y) then x else y) ===> True
#testOptimize [ "DecideAndBool_23" ] ∀ (x y : Nat) (a b c : Bool),
                                       (if (x ≤ y ∧ y ≥ x) && ((a || ((b || c) && !(c || b)))) then x else y) =
                                       (if a ∧ (x ≤ y) then x else y) ===> True

-- ∀ (x y z: Nat), (x != y && x ≠ y && Nat.ble z y) = (Nat.ble z y ∧ (y ≠ x)) ===> True
#testOptimize [ "DecideAndBool_24" ] ∀ (x y z : Nat),
                                       (x != y && x ≠ y && Nat.ble z y) = (Nat.ble z y ∧ (y ≠ x)) ===> True

-- ∀ (x y m n : Nat), ((x != y && n ≥ m) && (x ≠ y && m ≤ n)) = (n ≥ m ∧ (x ≠ y)) ===> True
#testOptimize [ "DecideAndBool_25" ] ∀ (x y m n : Nat),
                                       ((x != y && n ≥ m) && (x ≠ y && m ≤ n)) = (n ≥ m ∧ (x ≠ y)) ===> True

-- ∀ (x y z m n : Nat),
--  ((x != y && Nat.ble n m) && (x ≠ z && m == z)) =
--  (((z ≠ x) ∧ z = m) ∧ ((y != x) && Nat.ble n m)) ===> True
#testOptimize [ "DecideAndBool_26" ] ∀ (x y z m n : Nat),
                                        ((x != y && Nat.ble n m) && (x ≠ z && m == z)) =
                                        (((z ≠ x) ∧ z = m) ∧ ((y != x) && Nat.ble n m)) ===> True

-- ∀ (x y z m n : Nat),
--  (((x != y && m < n) && m == z) && x ≠ z) =
--  (z ≠ x ∧ ((y ≠ x) ∧ n > m) ∧ z = m) ===> True
#testOptimize [ "DecideAndBool_27" ] ∀ (x y z m n : Nat),
                                       (((x != y && m < n) && m == z) && x ≠ z) =
                                       (z ≠ x ∧ ((y ≠ x) ∧ n > m) ∧ z = m) ===> True


end Test.DecideBoolAnd
