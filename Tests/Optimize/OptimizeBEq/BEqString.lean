import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.BEqString
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance for `String. -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- "xyz" == "xyz" ===> true
#testOptimize [ "BEqStringCst_1", proof ] "xyz" == "xyz" ===> true

-- "xyz" == "zxyz" ===> false
#testOptimize [ "BEqStringCst_2", proof ] "xyz" == "zxyz" ===> false

-- "xyz" == "xyza" ===> false
#testOptimize [ "BEqStringCst_3", proof ] "xyz" == "xyza" ===> false

-- "test" ++ "Optimize" == "testOptimize" ===> true
#testOptimize [ "BEqStringCst_4", proof ] "test" ++ "Optimize" == "testOptimize" ===> true

-- "testOptimize".take 4 == "test" ===> true
#testOptimize [ "BEqStringCst_5", proof ] "testOptimize".take 4 == "test" ===> true

-- "testOptimize".take 0 == "" ===> true
#testOptimize [ "BEqStringCst_6", proof ] "testOptimize".take 0 == "" ===> true

/-! Test cases for simplification rule `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`. -/

-- s == s ===> True
#testOptimize [ "BEqStringReflexive_1", proof ] ∀ (s : String), (s == s) ===> True

-- (s ++ t) == (s ++ t) ===> True (with Type(s) = String)
#testOptimize [ "BEqStringReflexive_2", proof ] ∀ (s t : String), (s ++ t == s ++ t) ===> True

-- TODO: add other reflexive test cases

-- (s ++ "") == s ===> True
#testOptimize [ "BEqStringReflexive_3", proof ] ∀ (s : String), (s ++ "" == s) ===> True


/-! Test cases to ensure that simplification rules `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)` is not applied wrongly. -/

-- TODO: add other test cases when opacifying String functions for SMT lib transation

-- s == t ===> s = t
-- NOTE `true = (s == t)` is normalized to `s = t`.
#testOptimize [ "BEqStringUnchanged_1", proof ] ∀ (s t : String), s == t ===> ∀ (s t : String), s = t

-- ∀ (x : String), (x == "xyz") ===> ∀ (x : String), x = "xyz"
-- NOTE `true = (s == t)` is normalized to `s = t`.
def beqStringUnchanged_2 : Expr :=
 Lean.Expr.forallE
  `x
  (Lean.Expr.const `String [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `String []))
      (Lean.Expr.lit (Lean.Literal.strVal "xyz")))
    (Lean.Expr.bvar 0))
  (Lean.BinderInfo.default)

elab "beqStringUnchanged_2" : term => return beqStringUnchanged_2

#testOptimize [ "BEqStringUnchanged_2", proof ] ∀ (x : String), x == "xyz" ===> beqStringUnchanged_2


/-! Test cases for simplification rule `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`. -/

-- s == t = s == t ===> True
#testOptimize [ "BEqStringCommut_1", proof ] ∀ (s t : String), (s == t) = (s == t) ===> True

-- s == t = t == s ===> True
#testOptimize [ "BEqStringCommut_2", proof ] ∀ (s t : String), (s == t) = (t == s) ===> True

-- t == s ===> s == t (when `s` declared first)
-- NOTE `true = (s == t)` is normalized to `s = t`.
#testOptimize [ "BEqStringCommut_3", proof ] ∀ (s t : String), (t == s) ===> ∀ (s t : String), s = t

-- (s ++ t) == v = (v == (s ++ t)) ===> True
#testOptimize [ "BEqStringCommut_4", proof ] ∀ (s t v : String), ((s ++ t) == v) = (v == (s ++ t)) ===> True


/-! Test cases to ensure that `reduceApp` is properly called
    when `BEq.beq` operands are reduced to constant values via optimization. -/

-- TODO : add reduction test cases when normalization and simplification rules are introduced for String

end Test.BEqString
