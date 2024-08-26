import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeNot
/-! ## Test objectives to validate normalization and simplification rules on ``Not -/

-- ¬ False ===> True
#testOptimize [ "NotFalse" ] ¬ False ===> True

-- ¬ True ===> False
#testOptimize [ "NotTrue" ] ¬ True ===> False

-- ¬ (¬ a) ===> a
#testOptimize [ "NotNot_1" ] ∀ (a : Prop), ¬ (¬ a) ===> ∀ (a : Prop), a

-- ¬ (¬ (¬ a)) ===> ¬ a
#testOptimize [ "NotNot_2" ] ∀ (a : Prop), ¬ (¬ (¬ a)) ===> ∀ (a : Prop), ¬ a

-- ¬ (¬ (¬ (¬ a))) ===> a
#testOptimize [ "NotNot_3" ] ∀ (a : Prop), ¬ (¬ (¬ (¬ a))) ===> ∀ (a : Prop), a

-- ¬ (false = a) ===> a (with Type(a) = Prop)
-- NOTE that `false = a` is interpreted as `(false = true) = a`
-- which is reduced to `False = a` and then to `¬ a`.
#testOptimize [ "NotNot_4" ]  ∀ (a : Prop), ¬ (false = a) ===> ∀ (a : Prop), a

-- ¬ (false = a) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_1" ] ∀ (a : Bool), ¬ (false = a) ===> ∀ (a : Bool), true = a

-- ¬ (a = false) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_2" ] ∀ (a : Bool), ¬ (a = false) ===> ∀ (a : Bool), true = a

-- ¬ (false = a) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_3" ] ∀ (a : Bool), ¬ (false = a) = a ===> True

-- ¬ (a = false) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_4" ] ∀ (a : Bool), ¬ (a = false) = a ===> True

-- ¬ (a = (b && ! b)) ===> true = a (with Type(a) = Bool)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NotEqFalse_5" ] ∀ (a b : Bool), ¬ (a = (b && !b)) ===> ∀ (a _b : Bool), true = a

-- ¬ (a = (b && ! b)) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_6" ] ∀ (a b : Bool), ¬ (a = (b && !b)) = a ===> True

-- let x := a || a in
-- let y := ! a || ! x in
-- ¬ y ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_7" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; ¬ y ===> ∀ (a : Bool), true = a

-- let x := a || a in
-- let y := ! a || ! x in
-- (¬ y) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_8" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; (¬ y) = a ===> True


-- ¬ (true = a) ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_1" ] ∀ (a : Bool), ¬ (true = a) ===> ∀ (a : Bool), false = a

-- ¬ (a = true) ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_2" ] ∀ (a : Bool), ¬ (a = true) ===> ∀ (a : Bool), false = a

-- ¬ (true = a) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_3" ] ∀ (a : Bool), ¬ (true = a) = not a ===> True

-- ¬ (a = false) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_4" ] ∀ (a : Bool), ¬ (a = true) = not a ===> True

-- ¬ (a = (b || ! b)) ===> false = a (with Type(a) = Bool)
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NotEqTrue_5" ] ∀ (a b : Bool), ¬ (a = (b || !b)) ===> ∀ (a _b : Bool), false = a

-- ¬ (a = (b || ! b)) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_6" ] ∀ (a b : Bool), ¬ (a = (b || !b)) = not a ===> True

-- let x := a && a in
-- let y := a || x in
-- ¬ y ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_7" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y ===> ∀ (a : Bool), false = a

-- let x := a && a in
-- let y := a || x in
-- (¬ y) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_8" ] ∀ (a : Bool), let x := a && a; let y := a || x; (¬ y) = not a ===> True

-- ¬ a ===> ¬ a
#testOptimize [ "NotUnchanged_1" ] ∀ (a : Prop), ¬ a ===> ∀ (a : Prop), ¬ a

-- (¬ (¬ (¬ a)) = ¬ a ===> True
#testOptimize [ "NotUnchanged_2" ] ∀ (a : Prop), ¬ (¬ (¬ a)) = ¬ a ===> True

-- ¬ (a = b) ===> ¬ (a = b)
#testOptimize [ "NotUnchanged_3" ] ∀ (a b : Prop), ¬ (a = b) ===> ∀ (a b : Prop), ¬ (a = b)

-- ¬ ((¬ a) = b) ===> ¬ ((¬ a) = b)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotUnchanged_4" ] ∀ (a b : Prop), ¬ ((¬ a) = b) ===> ∀ (a b : Prop), ¬ (b = ¬ a)

end Tests.OptimizeNot
