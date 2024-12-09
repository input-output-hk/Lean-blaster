import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.BEqBool
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance for ``Bool. -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- false == true ===> false
#testOptimize [ "BEqBoolCst_1" ] false == true ===> false

-- true == false ===> false
#testOptimize [ "BEqBoolCst_2" ] true == false ===> false

-- true == true ===> true
#testOptimize [ "BEqBoolCst_3" ] true == true ===> true

-- false == false ===> true
#testOptimize [ "BEqBoolCst_4" ] false == false ===> true

-- ! true == false ===> true
#testOptimize [ "BEqBoolCst_5" ] ! true == false ===> true

-- ! false == true ===> true
#testOptimize [ "BEqBoolCst_6" ] ! false == true ===> true

-- ! false == false ===> false
#testOptimize [ "BEqBoolCst_7" ] ! false == false ===> false

-- true = ! true ===> false
#testOptimize [ "BEqBoolCst_8" ] true == ! true ===> false


/-! Test cases for simplification rule `false == e ==> not e`. -/

-- false == a ===> not a (i.e., false = a)
#testOptimize [ "BEqFalse_1" ] ∀ (a : Bool), (false == a) ===> ∀ (a : Bool), false = a

-- (false == a) = not a ===> True
#testOptimize [ "BEqFalse_2" ] ∀ (a : Bool), (false == a) = not a ===> True

-- (a == false) = not a ===> True
#testOptimize [ "BEqFalse_3" ] ∀ (a : Bool), (a == false) = not a ===> True

-- ((false && a) == b) = !b ===> True
#testOptimize [ "BEqFalse_4" ] ∀ (a b : Bool), ((false && a) == b) = !b ===> True

-- (b == (false && a)) = !b ===> True
#testOptimize [ "BEqFalse_5" ] ∀ (a b : Bool), (b == (false && a)) = !b ===> True

-- (b == (a && !a)) = !b ===> True
#testOptimize [ "BEqFalse_6" ] ∀ (a b : Bool), (b == (a && !a)) = !b ===> True

-- let x := a || a
-- let y := a && !x
-- (y == b) = !b ===> True
#testOptimize [ "BEqFalse_7" ] ∀ (a b : Bool), let x := a || a; let y := a && !x; (y == b) = !b ===> True

-- false == not a ===> a
#testOptimize [ "BEqFalse_8" ] ∀ (a : Bool), false == not a ===> ∀ (a : Bool), true = a

-- false == (not (not a)) ===> not a (i.e., false = a)
#testOptimize [ "BEqFalse_9" ] ∀ (a : Bool), false == (not (not a)) ===> ∀ (a : Bool), false = a

-- false == (not (not (not a)) ===> a
#testOptimize [ "BEqFalse_10" ] ∀ (a : Bool), false == (not (not (not a))) ===> ∀ (a : Bool), true = a


/-! Test cases for simplification rule `true == e ==> e`. -/

-- true == a ===> a (i.e., true = a)
#testOptimize [ "BEqTrue_1" ] ∀ (a : Bool), true == a ===>  ∀ (a : Bool), true = a

-- (true == a) = a ===> True
#testOptimize [ "BEqTrue_2" ] ∀ (a : Bool), (true == a) = a ===> True

-- (a == true) = a ===> True
#testOptimize [ "BEqTrue_3" ] ∀ (a : Bool), (a == true) = a ===> True

-- (a == (b || true) = a ===> True
#testOptimize [ "BEqTrue_4" ] ∀ (a b : Bool), (a == (b || true)) = a ===> True

-- ((b || true) == a) = a ===> True
#testOptimize [ "BEqTrue_5" ] ∀ (a b : Bool), ((b || true) = a) = a ===> True

-- ((b || !b) == a) = a ===> True
#testOptimize [ "BEqTrue_6" ] ∀ (a b : Bool), ((b || !b) = a) = a ===> True

-- (a == (b || !((c && !c) || b)) = a ===> True
#testOptimize [ "BEqTrue_7" ] ∀ (a b c : Bool), (a == (b || !((c && !c) || b))) = a ===> True

-- let x := a && a
-- let y := a || !x
-- (y == b) = b ===> True
#testOptimize [ "BEqTrue_8" ] ∀ (a b : Bool), let x := a && a; let y := a || !x; (y == b) = b ===> True

-- true == not a ===> not a (i.e., false = a)
#testOptimize [ "BEqTrue_9" ] ∀ (a : Bool), true == not a ===> ∀ (a : Bool), false = a

-- true == (not (not a) ===> a
#testOptimize [ "BEqTrue_10" ] ∀ (a : Bool), true == (not (not a)) ===> ∀ (a : Bool), true = a

-- true == (not (not (not a)) ===> not a (i.e., false = a)
#testOptimize [ "BEqTrue_11" ] ∀ (a : Bool), true == (not (not (not a))) ===> ∀ (a : Bool), false = a


/-! Test cases for simplification rule `e == not e ==> false`. -/

-- a == not a ===> False
#testOptimize [ "BEqNot_1" ] ∀ (a : Bool), a == not a ===> False

-- (a == not a) = false ===> True
#testOptimize [ "BEqNot_2" ] ∀ (a : Bool), (a == not a) = false ===> True

-- a == !a ===> False
#testOptimize [ "BEqNot_3" ] ∀ (a : Bool), a == !a ===> False

-- (a == !a) = false ===> True
#testOptimize [ "BEqNot_4" ] ∀ (a : Bool), (a == !a) = false ===> True

-- (a || b) == !(b || a) ===> False
#testOptimize [ "BEqNot_5" ] ∀ (a b : Bool), (a || b) == !(b || a) ===> False

-- (a && b) == !(b && a) ===> False
#testOptimize [ "BEqNot_6" ] ∀ (a b : Bool), (a && b) == !(b && a) ===> False

-- a == !(! (! a)) ===> False
#testOptimize [ "BEqNot_7" ] ∀ (a : Bool), a == !(! (! a)) ===> False

-- not a == a ===> False
#testOptimize [ "BEqNot_8" ] ∀ (a : Bool), not a == a ===> False

-- (not a == a) = false ===> True
#testOptimize [ "BEqNot_9" ] ∀ (a : Bool), (not a == a) = false ===> True

-- !a == a ===> False
#testOptimize [ "BEqNot_10" ] ∀ (a : Bool), !a == a ===> False

-- (!a == a) = false ===> True
#testOptimize [ "BEqNot_11" ] ∀ (a : Bool), (!a == a) = false ===> True

-- !(a || b) == (b || a) ===> False
#testOptimize [ "BEqNot_12" ] ∀ (a b : Bool), !(a || b) == (b || a) ===> False

-- !(a && b) == (b && a) ===> False
#testOptimize [ "BEqNot_13" ] ∀ (a b : Bool), !(a && b) == (b && a) ===> False

-- !(!(!a)) == a ===> False
#testOptimize [ "BEqNot_14" ] ∀ (a : Bool), !(! (! a)) == a ===> False


/-! Test cases to ensure that simplification rule `e == not e ==> false` is not applied wrongly. -/

-- a == not b ===> a = not b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_1" ] ∀ (a b : Bool), (a == not b) ===>
                                      ∀ (a b : Bool), (a = not b)

-- not b == a ===> a = not b
-- NOTE: reordering applied on operands
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_2" ] ∀ (a b : Bool), (not b == a) ===>
                                      ∀ (a b : Bool), (a = not b)

-- a == !b ===> a = !b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_3" ] ∀ (a b : Bool), (a == !b) ===>
                                      ∀ (a b : Bool), a = !b

-- !a == b ===> !a = b
-- NOTE: reordering applied on operands
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_4" ] ∀ (a b : Bool), ((!a) == b) ===>
                                      ∀ (a b : Bool), b = !a

-- a == (! (! a)) ===> True
#testOptimize [ "BEqNotUnchanged_5" ] ∀ (a : Bool), (a == !(!a)) ===> True


-- a == !(b && c) ===> a = !(b && c)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_6" ] ∀ (a b c : Bool), (a == !(b && c)) ===>
                                      ∀ (a b c : Bool), a = !(b && c)

-- (a && b) == !(c && d) ===> (!(c && d)) = (a && b)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqNotUnchanged_7" ] ∀ (a b c d : Bool), (a && b) == !(c && d) ===>
                                      ∀ (a b c d : Bool), (!(c && d)) = (a && b)


/-! Test cases for simplification rule `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`. -/

-- a == a = true ===> True (with Type(a) = Bool)
#testOptimize [ "BEqBoolReflexive_1" ] ∀ (a : Bool), (a == a) = true ===> True

-- a == a ===> True (with Type(a) = Bool)
#testOptimize [ "BEqBoolReflexive_2" ] ∀ (a : Bool), (a == a) ===> True

-- a == (a || a) ===> True
#testOptimize [ "BEqBoolReflexive_3" ] ∀ (a : Bool), a == (a || a) ===> True

-- (a || a) == a ===> True
#testOptimize [ "BEqBoolReflexive_4" ] ∀ (a : Bool), (a || a) == a ===> True

-- a == ((b && ! b) || a) ===> True
#testOptimize [ "BEqBoolReflexive_5" ] ∀ (a b : Bool), (((b && ! b) || a) == a) ===> True

-- (a && b) == (b && a) ===> True
#testOptimize [ "BEqBoolReflexive_6" ] ∀ (a b : Bool), (a && b) == (b && a) ===> True

-- (a && b) == ((b || b) && (c || !c) && a) ===> True
#testOptimize [ "BEqBoolReflexive_7" ] ∀ (a b c : Bool), (a && b) == ((b || b) && (c || !c) && a) ===> True


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `false == e ==> not e`
     - `true == e ==> e`
     - `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`
-/

-- a == b ===> a = b (with Type(a) = Type(b) = Bool)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqBoolUnchanged_1" ] ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), a = b

-- c == (a && b) ===> c = (a && b)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqBoolUnchanged_2" ] ∀ (a b c : Bool), c == (a && b) ===>
                                       ∀ (a b c : Bool), c = (a && b)

-- (a && b) == c ===> c = (a && b)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqBoolUnchanged_3" ] ∀ (a b c : Bool), (a && b) == c ===>
                                       ∀ (a b c : Bool), c = (a && b)

-- (a || b) == (c && ( b || !b)) ===> c = (a || b)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqBoolUnchanged_4" ] ∀ (a b c : Bool), (a || b) == (c && (b || !b)) ===>
                                       ∀ (a b c : Bool), c = (a || b)


/-! Test cases for simplification rule `not e1 == not e2 ==> e1 == e2`. -/

-- not a == not b ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_1" ] ∀ (a b : Bool), not a == not b ===> ∀ (a b : Bool), a = b

-- not a == not (not b) ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_2" ] ∀ (a b : Bool), not a == not (not b) ===> ∀ (a b : Bool), b = not a

-- not a == not (not (not b)) ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_3" ] ∀ (a b : Bool), not a == not (not (not b)) ===> ∀ (a b : Bool), a = b

-- not (not a) == not (not b) ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_4" ] ∀ (a b : Bool), not (not a) == not (not b) ===> ∀ (a b : Bool), a = b

-- not (not (not a)) == not (not (not b)) ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_5" ] ∀ (a b : Bool), not (not (not a)) == not (not (not b)) ===>
                                ∀ (a b : Bool), a = b

-- not (not (not a)) = b ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_6" ] ∀ (a b : Bool), not (not (not a)) == b ===> ∀ (a b : Bool), b = not a

-- !a == !b ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_7" ] ∀ (a b : Bool), (!a) == !b ===> ∀ (a b : Bool), a = b

-- !a == !(!b) ===> b = !a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_8" ] ∀ (a b : Bool), (!a) == !(!b) ===> ∀ (a b : Bool), b = !a

-- !a == !(!(!b)) ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_9" ] ∀ (a b : Bool), (!a) == !(!(!b)) ===> ∀ (a b : Bool), a = b

-- !(a && b) == !(c && d) ===> (a && b) = (c && d)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_10" ] ∀ (a b c d : Bool), (!(a && b)) == !(c && d) ===>
                                 ∀ (a b c d : Bool), (a && b) = (c && d)

-- !(a || b) == ! c ===> c = (a || b)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNot_11" ] ∀ (a b c : Bool), (!(a || b)) == !c ===>
                                 ∀ (a b c : Bool), c = (a || b)

-- !(a || b) == ! c = (c == (b || a)) ===> True
#testOptimize [ "NotBEqNot_12" ] ∀ (a b c : Bool), ((!(a || b)) == !c) = (c == (b || a)) ===> True

-- (!(d || c) == !(b || a)) = ((a || b) == (c || d)) ===> True
#testOptimize [ "NotBEqNot_13" ] ∀ (a b c d : Bool), ((!(d || c)) == !(b || a)) = ((a || b) == (c || d)) ===> True


/-! Test cases to ensure that simplification rule `not e1 == not e2 ==> e1 == e2` is not applied wrongly. -/

-- not a == b ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_1" ] ∀ (a b : Bool), not a == b ===>
                                         ∀ (a b : Bool), b = not a

-- (not ((not a)) == b ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_2" ] ∀ (a b : Bool), (not (not a)) == b ===>
                                         ∀ (a b : Bool), a = b


-- (not ((not ((not a))) == b ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_3" ] ∀ (a b : Bool), (not (not (not a))) == b ===>
                                         ∀ (a b : Bool), b = not a

-- b == not a ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_4" ] ∀ (a b : Bool), b == not a ===>
                                         ∀ (a b : Bool), b = not a

-- b == (not ((not a)) ===> a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_5" ] ∀ (a b : Bool), b == (not (not a)) ===>
                                         ∀ (a b : Bool), a = b


-- b == (not ((not ((not a))) ===> b = not a
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "NotBEqNotUnchanged_6" ] ∀ (a b : Bool), b == (not (not (not a))) ===>
                                         ∀ (a b : Bool), b = not a


/-! Test cases for simplification rule `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`. -/

-- a == b = a == b ===> True (with Type(a) = Bool)
#testOptimize [ "BEqBoolCommut_1" ] ∀ (a b : Bool), (a == b) = (a == b) ===> True


-- a == b = b == a ===> True (with Type(a) = Bool)
#testOptimize [ "BEqBoolCommut_2" ] ∀ (a b : Bool), (a == b) = (b == a) ===> True


-- b == a ===> a = b (with Type(a) = Bool and when `a` declared first)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "BEqBoolCommut_3" ] ∀ (a b : Bool), (b == a) ===>
                                    ∀ (a b : Bool), a = b

-- a == (b == c) = ((c == b) == a) ===> True (with Type(a) = Bool)
#testOptimize [ "BEqBoolCommut_4" ] ∀ (a b c : Bool), (a == (b == c)) = ((c == b) == a) ===> True


/-! Test cases to ensure that constant propagation is properly performed
    when `BEq.beq` operands are reduced to constant values via optimization. -/

variable (a : Bool)
variable (b : Bool)
variable (c : Bool)

-- false == (a && false) ===> true
#testOptimize [ "BEqBoolReduce_1"] false == (a && false) ===> true

-- false == (a || true) ===> false
#testOptimize [ "BEqBoolReduce_2"] false == (a || true) ===> false

-- (a || true) == false ===> false
#testOptimize [ "BEqBoolReduce_3"] (a || true) == false ===> false

-- (a == !a) == (b == !b) ===> true
#testOptimize [ "BEqBoolReduce_4"] (a == !a) == (b == !b) ===> true

-- ((a && b) == !(b && a)) == (b == !(b || b)) ===> true
#testOptimize [ "BEqBoolReduce_5"] ((a && b) == !(b && a)) == (b == !(b || b)) ===> true

-- ((a == ((b || c) == !(c || b))) == !a) == ((b && a) == !(a && b)) ===> false
#testOptimize [ "BEqBoolReduce_6"] ((a == ((b || c) == !(c || b))) == !a) == ((b && a) == !(a && b)) ===> false

end Test.BEqBool
