import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.DecideBoolOr

/-! ## Test objectives to validate `Decidable.decide` simplification rules on Boolean `or`. -/


/-! Test cases for simplification rule `decide e1 || decide e2 ===> decide (e1 ∨ e2)`. -/

variable (x : Int)
variable (y : Int)
variable (z : Int)

-- x ≤ y || z ≥ y ===> Solver.decide' (¬ y < x ∨ ¬ z < y)
#testOptimize [ "DecideOrDecide_1" ]  x ≤ y || z ≥ y ===> Solver.decide' (¬ y < x ∨ ¬ z < y)

-- (x ≤ y || z ≥ y) = decide (x ≤ y ∨ y ≤ z) ===> True
#testOptimize [ "DecideOrDecide_2" ] (x ≤ y || z ≥ y) = decide (x ≤ y ∨ y ≤ z) ===> True

-- ∀ (x y z : Nat), x ≤ y || z ≥ y ===> ∀ (x y z : Nat), ¬ y < x ∨ ¬ z < y
#testOptimize [ "DecideOrDecide_3" ]
  ∀ (x y z : Nat), x ≤ y || z ≥ y ===> ∀ (x y z : Nat), ¬ y < x ∨ ¬ z < y

-- (x ≤ y || x ≤ y) = decide (x ≤ y) ===> True
#testOptimize [ "DecideOrDecide_4" ] (x ≤ y || x ≤ y) = decide (x ≤ y) ===> True

-- ∀ (x y : Nat), x ≤ y || x ≤ y ===> ∀ (x y : Nat), ¬ y < x
#testOptimize [ "DecideOrDecide_5" ] ∀ (x y : Nat), x ≤ y || x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- ∀ (x y : Nat), !(x ≤ y) || x ≤ y ===> True
#testOptimize [ "DecideOrDecide_6" ] ∀ (x y : Nat), !x ≤ y || x ≤ y ===> True

-- ∀ (x y : Nat), (x = y) || (x ≠ y) ===> False
#testOptimize [ "DecideOrDecide_7" ] ∀ (x y : Nat), x = y || x ≠ y ===> True

-- ∀ (x y : Nat), !x = y || x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)
#testOptimize [ "DecideOrDecide_8" ] ∀ (x y : Nat), !x = y || x ≠ y ===> ∀ (x y : Nat), ¬ (x = y)

-- ∀ (x y z: Nat), !x = y || x ≠ y || z > y ===> ∀ (x y z : Nat), ¬ (x = y) ∨ y < z
#testOptimize [ "DecideOrDecide_9" ] ∀ (x y z : Nat), !x = y || x ≠ y || z > y ===>
                                     ∀ (x y z : Nat), ¬ (x = y) ∨ (y < z)

-- ∀ (x y m n : Nat), (!x = y || n ≥ m) || (x ≠ y || m ≤ n) ===>
-- ∀ (x y m n : Nat), ¬ (x = y) ∨ ¬ n < m
#testOptimize [ "DecideOrDecide_10" ] ∀ (x y m n : Nat), (!x = y || n ≥ m) || (x ≠ y || m ≤ n) ===>
                                      ∀ (x y m n : Nat), ¬ (x = y) ∨ ¬ n < m


-- ∀ (x y z m n : Nat), (!x = y || n ≥ m) || (x ≠ z || m ≤ z) ===>
-- ∀ (x y z m n : Nat), (¬ (x = y) ∨ ¬ n < m) ∨ (¬ (x = z) ∨ ¬ z < m)
#testOptimize [ "DecideOrDecide_11" ] ∀ (x y z m n : Nat), (!x = y || n ≥ m) || (x ≠ z || m ≤ z) ===>
                                      ∀ (x y z m n : Nat), (¬ (x = y) ∨ ¬ n < m) ∨ (¬ (x = z) ∨ ¬ z < m)

-- ∀ (x y z m n : Nat), x < y || (n ≥ m || (!x > z || m ≤ z)) ===>
-- ∀ (x y z m n : Nat), (¬ n < m ∨ (¬ z < x ∨ ¬ z < m)) ∨ x < y
#testOptimize [ "DecideOrDecide_12" ] ∀ (x y z m n : Nat), x < y || (n ≥ m || (!x > z || m ≤ z)) ===>
                                      ∀ (x y z m n : Nat), (¬ n < m ∨ (¬ z < x ∨ ¬ z < m)) ∨ x < y


-- ∀ (x y z : Nat), (x ≤ y || z ≥ y) = x ≤ y ∨ y ≤ z ===> True
#testOptimize [ "DecideOrDecide_13" ] ∀ (x y z : Nat), (x ≤ y || z ≥ y) = (x ≤ y ∨ y ≤ z) ===> True

-- ∀ (x y : Nat), (x ≤ y || y ≥ x) = x ≤ y ===> True
#testOptimize [ "DecideOrDecide_14" ] ∀ (x y : Nat), (x ≤ y || y ≥ x) = (x ≤ y) ===> True

-- ∀ (x y : Nat), (!x = y || x ≠ y) = ¬ (x = y) ===> True
#testOptimize [ "DecideOrDecide_15" ] ∀ (x y : Nat), (!x = y || x ≠ y) = ¬ (x = y) ===> True


-- ∀ (x y z: Nat), (!x = y || x ≠ y || z > y) = (y < z ∨ ¬ (x = y)) ===> True
#testOptimize [ "DecideOrDecide_16" ] ∀ (x y z: Nat),
                                         (!x = y || x ≠ y || z > y) = (y < z ∨ ¬ (x = y)) ===> True

-- ∀ (x y m n : Nat), ((!x = y || n ≥ m) || (x ≠ y || m ≤ n)) = (n ≥ m ∨ (x ≠ y)) ===> True
#testOptimize [ "DecideOrDecide_17" ]
  ∀ (x y m n : Nat), ((!x = y || n ≥ m) || (x ≠ y || m ≤ n)) = (n ≥ m ∨ (x ≠ y)) ===> True


-- ∀ (x y z m n : Nat),
-- ((!x = y || n ≥ m) || (x ≠ z || m ≤ z)) = ((m ≤ n ∨ ¬ (y = x)) ∨ (z ≥ m ∨ (z ≠ x))) ===> True
#testOptimize [ "DecideOrDecide_18" ]
  ∀ (x y z m n : Nat),
    ((!x = y || n ≥ m) || (x ≠ z || m ≤ z)) = ((m ≤ n ∨ ¬ (y = x)) ∨ (z ≥ m ∨ (z ≠ x))) ===> True

-- ∀ (x y z m n : Nat),
-- (x < y || (n ≥ m || (!x > z || m ≤ z))) = (((¬ (z < x) ∨ z ≥ m) ∨ m ≤ n) ∨ x < y) ===> True
#testOptimize [ "DecideOrDecide_19" ]
  ∀ (x y z m n : Nat),
    (x < y || (n ≥ m || (!x > z || m ≤ z))) = (((¬ (z < x) ∨ z ≥ m) ∨ m ≤ n) ∨ x < y) ===> True

variable (w : Int)

-- ((decide (x < y) || decide (x < z)) || decide (x < w)) = decide (((x < y) ∨ (x < z)) ∨ (x < w)) ===> True
#testOptimize [ "DecideOrDecide_20" ]
  ((decide (x < y) || decide (x < z)) || decide (x < w)) = decide (((x < y) ∨ (x < z)) ∨ (x < w)) ===> True

-- (decide (x < y) || (decide (x < z) || decide (x < w))) = decide ((x < y) ∨ (x < z) ∨ (x < w)) ===> True
#testOptimize [ "DecideOrDecide_21" ]
  (decide (x < y) || (decide (x < z) || decide (x < w))) = decide ((x < y) ∨ (x < z) ∨ (x < w)) ===> True


/-! Test cases for simplification rule `decide e1 || e2 | e2 || decide e1 ===> decide (e1 ∨ true = e2)`. -/

variable (b : Bool)

-- x ≤ y || b ===> Solver.decide' (¬ y < x ∨ true = b)
#testOptimize [ "DecideOrBool_1" ] x ≤ y || b ===> Solver.decide' (¬ y < x ∨ true = b)

-- b || x ≤ y ===> Solver.decide' (¬ y < x ∨ true = b)
#testOptimize [ "DecideOrBool_2" ] b || x ≤ y ===> Solver.decide' (¬ y < x ∨ true = b)

-- !b || x ≤ y ===> Solver.decide' (¬ y < x ∨ false = b)
#testOptimize [ "DecideOrBool_3" ] !b || x ≤ y ===> Solver.decide' (¬ y < x ∨ false = b)

-- ∀ (x y m n : Nat), x < y || (m == n) ===> ∀ (x y m n : Nat), m = n ∨ x < y
#testOptimize [ "DecideOrBool_4" ] ∀ (x y m n : Nat), x < y || (m == n) ===>
                                   ∀ (x y m n : Nat), m = n ∨ x < y

-- ∀ (m n : Nat), (m = n) || (m == n) ===> ∀ (m n : Nat), m = n
#testOptimize [ "DecideOrBool_5" ] ∀ (m n : Nat), (m = n) || (m == n) ===>
                                   ∀ (m n : Nat), m = n

-- ∀ (x y m n : Nat), x < y || (m != n) ===> ∀ (x y m n : Nat), ¬ m = n ∨ x < y
#testOptimize [ "DecideOrBool_6" ] ∀ (x y m n : Nat), x < y || (m != n) ===>
                                   ∀ (x y m n : Nat), ¬ m = n ∨ x < y

-- ∀ (m n : Nat), (m = n) || (m != n) ===> False
#testOptimize [ "DecideOrBool_7" ] ∀ (m n : Nat), (m = n) || (m != n) ===> True

-- ∀ (m n : Nat), (m ≠ n) || (m == n) ===> False
#testOptimize [ "DecideOrBool_8" ] ∀ (m n : Nat), (m ≠ n) || (m == n) ===> True

-- ∀ (m n : Nat), (m ≠ n) || (m != n) ===> ∀ (m n : Nat), ¬ m = n
#testOptimize [ "DecideOrBool_9" ] ∀ (m n : Nat), (m ≠ n) || (m != n) ===>
                                   ∀ (m n : Nat), ¬ m = n

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (((a ∨ b) ∨ (b ∧ ¬ b)) || c) ===>
-- ∀ (a b : Prop) (c : Bool), (a ∨ b) ∨ true = c
#testOptimize [ "DecideOrBool_10" ]
  ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (((a ∨ b) ∨ (b ∧ ¬ b)) || c) ===>
  ∀ (a b : Prop) (c : Bool), (a ∨ b) ∨ true = c

-- ∀ (x y z : Nat) (a b c : Bool),
--     (if (x ≤ y ∨ y ≥ x) || ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
-- ∀ (x y z : Nat) (a : Bool),
--     Solver.dite' ((¬ y < x) ∨ true = a)
--      (fun _ :  (¬ y < x) ∨ true = a => x)
--      (fun _ : ¬ ((¬ y < x) ∨ true = a) => y) < z
#testOptimize [ "DecideOrBool_11" ]
  ∀ (x y z : Nat) (a b c : Bool),
      (if (x ≤ y ∨ y ≥ x) || ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
  ∀ (x y z : Nat) (a : Bool),
      Solver.dite' ((¬ y < x) ∨ true = a)
       (fun _ :  (¬ y < x) ∨ true = a => x)
       (fun _ : ¬ ((¬ y < x) ∨ true = a) => y) < z

-- ∀ (x y z: Nat), x != y || x ≠ y || Nat.ble z y ===>
-- ∀ (x y z : Nat), ¬ (x = y) ∨ ¬ y < z
#testOptimize [ "DecideOrBool_12" ]
  ∀ (x y z : Nat), x != y || x ≠ y || Nat.ble z y ===>
  ∀ (x y z : Nat), ¬ (x = y) ∨ ¬ y < z


-- ∀ (x y m n : Nat), (x != y || n ≥ m) || (x ≠ y || m ≤ n) ===>
-- ∀ (x y m n : Nat), ¬ (x = y) ∨ ¬ n < m
#testOptimize [ "DecideOrBool_13" ]
  ∀ (x y m n : Nat), (x != y || n ≥ m) || (x ≠ y || m ≤ n) ===>
  ∀ (x y m n : Nat), ¬ (x = y) ∨ ¬ n < m

-- ∀ (x y z m n : Nat), (x != y || Nat.ble n m) || (x ≠ z || m == z) ===>
-- ∀ (x y z m n : Nat), (¬ (x = y) ∨ ¬ m < n) ∨ (¬ (x = z) ∨ z = m)
#testOptimize [ "DecideOrBool_14" ]
  ∀ (x y z m n : Nat), (x != y || Nat.ble n m) || (x ≠ z || m == z) ===>
  ∀ (x y z m n : Nat), (¬ (x = y) ∨ ¬ m < n) ∨ (¬ (x = z) ∨ z = m)


-- ∀ (x y z m n : Nat), ((x != y || m < n) || m == z) || x ≠ z ===>
-- ∀ (x y z m n : Nat), ¬ (x = z) ∨ ((¬ (x = y) ∨ m < n) ∨ z = m)
#testOptimize [ "DecideOrBool_15" ] ∀ (x y z m n : Nat), ((x != y || m < n) || m == z) || x ≠ z ===>
                                    ∀ (x y z m n : Nat), ¬ (x = z) ∨ ((¬ (x = y) ∨ m < n) ∨ z = m)

-- (x ≤ y || b) = decide (true = b ∨ y ≥ x) ===> True
#testOptimize [ "DecideOrBool_16" ] (x ≤ y || b) = decide (true = b ∨ y ≥ x) ===> True

-- (!b || x ≤ y) = decide (y ≥ x ∨ false = b) ===> True
#testOptimize [ "DecideOrBool_17" ] (!b || x ≤ y) = decide (y ≥ x ∨ false = b) ===> True

--  ∀ (x y m n : Nat), (x < y || (m == n)) = (n = m ∨ y > x) ===> True
#testOptimize [ "DecideOrBool_18" ] ∀ (x y m n : Nat), (x < y || (m == n)) = (n = m ∨ y > x) ===> True

-- ∀ (m n : Nat), ((m = n) || (n == m)) = (n = m) ===> True
#testOptimize [ "DecideOrBool_19" ] ∀ (m n : Nat), ((m = n) || (n == m)) = (n = m) ===> True

-- ∀ (x y m n : Nat), (x < y || (m != n)) = (n ≠ m ∨ y > x) ===> True
#testOptimize [ "DecideOrBool_20" ] ∀ (x y m n : Nat), (x < y || (m != n)) = (n ≠ m ∨ y > x) ===> True

-- ∀ (m n : Nat), ((n ≠ m) || (m != n)) = (m ≠ n) ===> True
#testOptimize [ "DecideOrBool_21" ] ∀ (m n : Nat), ((n ≠ m) || (m != n)) = (m ≠ n) ===> True

-- ∀ (a b : Prop) (c : Bool),
--  [Decidable a] → [Decidable b] → (((a ∨ b) ∨ (b ∧ ¬ b)) || c) = (c ∨ (b ∨ a)) ===> True
#testOptimize [ "DecideOrBool_22" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                      (((a ∨ b) ∨ (b ∧ ¬ b)) || c) = (c ∨ (b ∨ a)) ===> True

-- ∀ (x y : Nat) (a b c : Bool),
--  (if (x ≤ y ∨ y ≥ x) || ((a || ((b || c) && !(c || b)))) then x else y) =
--  (if a ∨ (x ≤ y) then x else y) ===> True
#testOptimize [ "DecideOrBool_23" ] ∀ (x y : Nat) (a b c : Bool),
                                       (if (x ≤ y ∨ y ≥ x) || ((a || ((b || c) && !(c || b)))) then x else y) =
                                       (if a ∨ (x ≤ y) then x else y) ===> True

-- ∀ (x y z: Nat), (x != y || x ≠ y || Nat.blt z y) = (Nat.blt z y ∨ (y ≠ x)) ===> True
#testOptimize [ "DecideOrBool_24" ] ∀ (x y z : Nat),
                                       (x != y || x ≠ y || Nat.blt z y) = (Nat.blt z y ∨ (y ≠ x)) ===> True

-- ∀ (x y m n : Nat), ((x != y || n ≥ m) || (x ≠ y || m ≤ n)) = (n ≥ m ∨ (x ≠ y)) ===> True
#testOptimize [ "DecideOrBool_25" ] ∀ (x y m n : Nat),
                                       ((x != y || n ≥ m) || (x ≠ y || m ≤ n)) = (n ≥ m ∨ (x ≠ y)) ===> True

-- ∀ (x y z m n : Nat),
--  ((x != y || Nat.blt n m) || (x ≠ z || m == z)) =
--  (((z ≠ x) ∨ z = m) ∨ ((y != x) || Nat.blt n m)) ===> True
#testOptimize [ "DecideOrBool_26" ] ∀ (x y z m n : Nat),
                                        ((x != y || Nat.blt n m) || (x ≠ z || m == z)) =
                                        (((z ≠ x) ∨ z = m) ∨ ((y != x) || Nat.blt n m)) ===> True

-- ∀ (x y z m n : Nat),
--  (((x != y || m < n) || m == z) || x ≠ z) =
--  (z ≠ x ∨ ((y ≠ x) ∨ n > m) ∨ z = m) ===> True
#testOptimize [ "DecideOrBool_27" ] ∀ (x y z m n : Nat),
                                       (((x != y || m < n) || m == z) || x ≠ z) =
                                       (z ≠ x ∨ ((y ≠ x) ∨ n > m) ∨ z = m) ===> True


end Test.DecideBoolOr
