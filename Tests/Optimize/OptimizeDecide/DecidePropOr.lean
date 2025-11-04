import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.DecidePropOr

/-! ## Test objectives to validate `Decidable.decide` simplification rules on `And` propositional expressions . -/


/-! Test cases for simplification rules
     - `B1 = e1 ∨ B2 = e2 ==> true = (NOP(B1, e1) || NOP(B2, e2)) (if B1 ∨ B2)`.
     - `B1 = e1 ∨ B2 = e2 ==> false = (e1 || e2) (if ¬ B1 ∨ ¬ B2)`.
-/

variable (a : Bool)
variable (b : Bool)

-- true = a ∨ true = b ===> true = (a || b)
#testOptimize [ "EqBoolOrEqBool_1" ] true = a ∨ true = b ===> true = (a || b)

-- true = a ∨ false = b ===> true = (a || !b)
#testOptimize [ "EqBoolOrEqBool_2" ] true = a ∨ false = b ===> true = (a || !b)

-- false = a ∨ true = b ===> true = (b || !a)
#testOptimize [ "EqBoolOrEqBool_3" ] false = a ∨ true = b ===> true = (b || !a)

-- false = a ∨ false = b ===> false = (a && b)
#testOptimize [ "EqBoolOrEqBool_4" ] false = a ∨ false = b ===> false = (a && b)

-- a ∨ b ===> true = (a || b)
#testOptimize [ "EqBoolOrEqBool_5" ] a ∨ b ===> true = (a || b)

-- a ∨ ¬ b ===> true = (a || !b)
#testOptimize [ "EqBoolOrEqBool_6" ] a ∨ ¬ b ===> true = (a || !b)

-- ¬ a ∨ b ===> true = (b || !a)
#testOptimize [ "EqBoolOrEqBool_7" ] ¬ a ∨ b ===> true = (b || !a)

-- ¬ a ∨ ¬ b ===> false = (a || b)
#testOptimize [ "EqBoolOrEqBool_8" ] ¬ a ∨ ¬ b ===> false = (a && b)

-- false = a ∨ true = a ===> True
#testOptimize [ "EqBoolOrEqBool_9" ] false = a ∨ true = a ===> True

-- true = a ∨ false = a ===> True
#testOptimize [ "EqBoolOrEqBool_10" ] true = a ∨ false = a ===> True

-- ¬ a ∨ true = a ===> True
#testOptimize [ "EqBoolOrEqBool_11" ] ¬ a ∨ true = a ===> True

-- true = a ∨ ¬ a ===> True
#testOptimize [ "EqBoolOrEqBool_12" ] true = a ∨ ¬ a ===> True

variable (c : Bool)

-- ¬ a ∨ b ∨ c ===> true = (!a || (b || c))
#testOptimize [ "EqBoolOrEqBool_13" ] ¬ a ∨ b ∨ c ===> true = (!a || (b || c))

-- a ∨ ¬ b ∨ ¬ c ===> true = (a || !(b && c))
#testOptimize [ "EqBoolOrEqBool_14" ] a ∨ ¬ b ∨ ¬ c ===> true = (a || !(b && c))


-- a ∨ (¬ b ∨ ¬ c) ∨ (b ∧ c) ===> True
#testOptimize [ "EqBoolOrEqBool_15" ] a ∨ (¬ b ∨ ¬ c) ∨ (b ∧ c) ===> True

variable (d : Bool)

-- (a ∨ ¬ b) ∨ c ∨ ¬ d ===> true = ((a || !b) || (c || !d))
#testOptimize [ "EqBoolOrEqBool_16" ] (a ∨ ¬ b) ∨ c ∨ ¬ d ===> true = ((a || !b) || (c || !d))


-- a ∨ (¬ b ∨ (c ∨ ¬ d)) ===> true = (a || (!b || (c || !d)))
#testOptimize [ "EqBoolOrEqBool_17" ] a ∨ (¬ b ∨ (c ∨ ¬ d)) ===> true = (a || (!b || (c || !d)))

-- (true = a ∨ true = b) = (b || a) ===> True
#testOptimize [ "EqBoolOrEqBool_18" ] (true = a ∨ true = b) = (b || a) ===> True

-- (true = a ∨ false = b) = (!b || a) ===> True
#testOptimize [ "EqBoolOrEqBool_19" ] (true = a ∨ false = b) = (!b || a) ===> True

-- (false = a ∨ true = b) = (b || !a) ===> True
#testOptimize [ "EqBoolOrEqBool_20" ] (false = a ∨ true = b) = (b || !a) ===> True

-- false = a ∨ false = b = !(b && a) ===> True
#testOptimize [ "EqBoolOrEqBool_21" ] (false = a ∨ false = b) = !(b && a) ===> True

-- (a ∨ b) = (a || b) ===> True
#testOptimize [ "EqBoolOrEqBool_22" ] (a ∨ b) = (b || a) ===> True

-- (a ∨ ¬ b) = (!b || a) ===> True
#testOptimize [ "EqBoolOrEqBool_23" ] (a ∨ ¬ b) = (!b || a) ===> True

-- (¬ a ∨ b) = (b || !a) ===> True
#testOptimize [ "EqBoolOrEqBool_24" ] (¬ a ∨ b) = (b || !a) ===> True

-- (¬ a ∨ ¬ b) = !(b && a) ===> True
#testOptimize [ "EqBoolOrEqBool_25" ] (¬ a ∨ ¬ b) = !(b && a) ===> True

-- (¬ a ∨ b ∨ c) = ((c || b) || !a) ===> True
#testOptimize [ "EqBoolOrEqBool_26" ] (¬ a ∨ b ∨ c) = ((c || b) || !a) ===> True

-- (a ∨ ¬ b ∨ ¬ c) = (!(c && b) || a) ===> True
#testOptimize [ "EqBoolOrEqBool_27" ] (a ∨ ¬ b ∨ ¬ c) = (!(c && b) || a) ===> True

-- ((a ∨ ¬ b) ∨ c ∨ ¬ d) = ((!b || a) || (!d || c)) ===> True
#testOptimize [ "EqBoolOrEqBool_28" ] ((a ∨ ¬ b) ∨ c ∨ ¬ d) = ((!b || a) || (!d || c)) ===> True

-- (a ∨ (¬ b ∨ (c ∨ ¬ d))) = (((!d || c) || !b) || a) ===> True
#testOptimize [ "EqBoolOrEqBool_29" ] (a ∨ (¬ b ∨ (c ∨ ¬ d))) = (((!d || c) || !b) || a) ===> True

-- ∀ (a b c : Bool), ¬ ((a ∨ b) ∨ c) ===> ∀ (a b c : Bool), false = (c || (a || b))
#testOptimize [ "EqBoolOrEqBool_30" ] ∀ (a b c : Bool), ¬ ((a ∨ b) ∨ c) ===>
                                        ∀ (a b c : Bool), false = (c || (a || b))

-- ∀ (a b c : Bool), ¬ ((a ∨ b) ∨ c) = !(c || (b || a)) ===> True
#testOptimize [ "EqBoolOrEqBool_31" ] ∀ (a b c : Bool), ¬ ((a ∨ b) ∨ c) = !(c || (b || a)) ===> True

-- ∀ (a b c d : Bool), ¬ ((a ∨ b) ∨ (c ∨ d)) ===>
-- ∀ (a b c d : Bool), false = ((a || b) || (c || d))
#testOptimize [ "EqBoolOrEqBool_32" ] ∀ (a b c d : Bool), ¬ ((a ∨ b) ∨ (c ∨ d)) ===>
                                       ∀ (a b c d : Bool), false = ((a || b) || (c || d))

-- ∀ (a b c d : Bool), ¬ ((a ∨ b) ∨ (c ∨ d)) = !((d || c) || (b || a)) ===> True
#testOptimize [ "EqBoolOrEqBool_33" ] ∀ (a b c d : Bool),
                                         ¬ ((a ∨ b) ∨ (c ∨ d)) = !((d || c) || (b || a)) ===> True

-- (!(a || b)) = ¬ (b ∨ a) ===> True
#testOptimize [ "EqBoolOrEqBool_34" ] (!(a || b)) = ¬ (b ∨ a) ===> True


-- ∀ (x y : Int) (a b c d : Bool),
--  (if ((x < y) ∨ (a ∨ (b ∨ c))) = d then x else y) =
--  (if ((x < y) || (a || (b || c))) == d then x else y) ===> True
#testOptimize [ "EqBoolOrEqBool_35"] ∀ (x y : Int) (a b c d : Bool),
                                       (if ((x < y) ∨ (a ∨ (b ∨ c))) = d then x else y) =
                                       (if ((x < y) || (a || (b || c))) == d then x else y) ===> True

-- false = a ∨ a ===> True
#testOptimize [ "EqBoolAndEqBool_36" ] false = a ∨ a ===> True

-- a ∨ false = a ===> True
#testOptimize [ "EqBoolAndEqBool_37" ] a ∨ false = a ===> True

-- false = (a && b) ∨ (a && b) ===> True
#testOptimize [ "EqBoolAndEqBool_38" ] false = (a && b) ∨ (a && b) ===> True


/-! Test cases to ensure that the following simplifications rules are not wrongly applied:
     - `B1 = e1 ∨ B2 = e2 ==> true = (NOP(B1, e1) || NOP(B2, e2)) (if B1 ∨ B2)`
     - `B1 = e1 ∨ B2 = e2 ==> false = (e1 || e2) (if ¬ B1 ∨ ¬ B2)`.
-/

-- ∀ (x y : Int), x < y ∨ a ===> ∀ (x y : Int), true = a ∨ x < y
#testOptimize [ "EqBoolOrEqBoolUnchanged_1" ] ∀ (x y : Int), x < y ∨ a ===>
                                               ∀ (x y : Int), true = a ∨ x < y

-- ∀ (x y : Int), a ∨ x < y ===> ∀ (x y : Int), true = a ∨ x < y
#testOptimize [ "EqBoolOrEqBoolUnchanged_2" ] ∀ (x y : Int), a ∨  x < y ===>
                                               ∀ (x y : Int), true = a ∨ x < y

-- ∀ (x y z : Int), (a ∨ x > z) ∨ x < y ===>
-- ∀ (x y z : Int), (true = a ∨ z < x) ∨ x < y
#testOptimize [ "EqBoolOrEqBoolUnchanged_3" ] ∀ (x y z : Int), (a ∨ x > z) ∨ x < y ===>
                                               ∀ (x y z : Int), (true = a ∨ z < x) ∨ x < y

-- ∀ (x y z : Int), (a ∨ x > z) ∨ (x < y ∨ b) ===>
-- ∀ (x y z : Int), (true = a ∨ z < x) ∨ (true = b ∨ x < y)
#testOptimize [ "EqBoolOrEqBoolUnchanged_4" ] ∀ (x y z : Int), (a ∨ x > z) ∨ (x < y ∨ b) ===>
                                               ∀ (x y z : Int), (true = a ∨ z < x) ∨ (true = b ∨ x < y)



-- ∀ (a b c d : Bool),
--  (true = ((a || b == c) || (c == a || d))) = ((a = c ∨ true = d) ∨ (b = c ∨ true = a)) ===>
-- ∀ (a b c d : Bool),
--  (((a = c) ∨ true = d) ∨ ((b = c) ∨ true = a)) =
--  (true = ((a || b == c) || (d || a == c)))
-- NOTE: can be simplified to `True`. See list of TODO in OptimizeBoolPropBinary.
#testOptimize [ "EqBoolOrEqBoolUnchanged_5" ] ∀ (a b c d : Bool),
                                                 (true = ((a || b == c) || (c == a || d))) =
                                                 (((a = c) ∨ d) ∨ ((b = c) ∨ a)) ===>
                                               ∀ (a b c d : Bool),
                                                 (((a = c) ∨ true = d) ∨ ((b = c) ∨ true = a)) =
                                                 (true = ((a || b == c) || (d || a == c)))

-- ∀ (a b c d : Bool),
--  (true = ((a || !(b == c)) || (!(c == a) || d))) =
--  ((¬ (a = c) ∨ d) ∨ (¬ (b = c) ∨ a)) ===>
-- ∀ (a b c d : Bool),
--  ((¬ (a = c) ∨ true = d) ∨ (¬ (b = c) ∨ true = a)) =
--  (true = ((a || !(b == c)) || (d || !(a == c))))

-- NOTE: can be simplified to `True`. See list of TODO in OptimizeBoolPropBinary and OptimizeEq.
#testOptimize [ "EqBoolOrEqBoolUnchanged_6" ] ∀ (a b c d : Bool),
                                                 (true = ((a || !(b == c)) || (!(c == a) || d))) =
                                                 ((¬ (a = c) ∨ d) ∨ (¬ (b = c) ∨ a)) ===>
                                               ∀ (a b c d : Bool),
                                                 ((¬ (a = c) ∨ true = d) ∨ (¬ (b = c) ∨ true = a)) =
                                                 (true = ((a || !(b == c)) || (d || !(a == c))))

-- ∀ (a b c : Bool), (false = (a == b || c == b)) = ¬ (b = a ∨ c = b) ===>
-- ∀ (a b c : Bool), (¬ (a = b ∨ b = c)) = (false = (a == b || b == c))
-- NOTE: can be simplified to `True`. See list of TODO in OptimizeBoolPropBinary and OptimizeEq.
#testOptimize [ "EqBoolOrEqBoolUnchanged_7" ] ∀ (a b c : Bool),
                                                  (!(a == b || c == b)) = ¬ (b = a ∨ c = b) ===>
                                               ∀ (a b c : Bool),
                                                  (¬ (a = b ∨ b = c)) = (false = (a == b || b == c))

-- ∀ (a b c d : Bool),
--  (!((a || !(b == c)) || (!(c == a) || d))) = ¬ ((¬ (a = c) ∨ d) ∨ (¬ (b = c) ∨ a)) ===>
-- ∀ (a b c d : Bool),
--  (¬ ((¬ (a = c) ∨ true = d) ∨ (¬ (b = c) ∨ true = a))) =
--  (false = ((a || !(b == c)) || (d || !(a == c))))
-- NOTE: can be simplified to `True`. See list of TODO in OptimizeBoolPropBinary and OptimizeEq.
#testOptimize [ "EqBoolOrEqBoolUnchanged_8" ] ∀ (a b c d : Bool),
                                                 (!((a || !(b == c)) || (!(c == a) || d))) =
                                                 ¬ ((¬ (a = c) ∨ d) ∨ (¬ (b = c) ∨ a)) ===>
                                               ∀ (a b c d : Bool),
                                                 (¬ ((¬ (a = c) ∨ true = d) ∨ (¬ (b = c) ∨ true = a))) =
                                                 (false = ((a || !(b == c)) || (d || !(a == c))))

-- ∀ (a b c : Bool), (!(!(a == b) || c == b)) = ¬ (c = b ∨ ¬ (b = a)) ===>
-- ∀ (a b c : Bool), (¬ (¬ (a = b) ∨ b = c)) = (false = (!(a == b) || b == c))
-- NOTE: can be simplified to `True`. See list of TODO in OptimizeBoolPropBinary and OptimizeEq.
#testOptimize [ "EqBoolOrEqBoolUnchanged_9" ] ∀ (a b c : Bool),
                                                  (!(!(a == b) || c == b)) = ¬ (c = b ∨ ¬ (b = a)) ===>
                                               ∀ (a b c : Bool),
                                                 (¬ (¬ (a = b) ∨ b = c)) = (false = (!(a == b) || b == c))

end Test.DecidePropOr
