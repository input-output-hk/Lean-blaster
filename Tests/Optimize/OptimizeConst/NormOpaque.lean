import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.NormOpaque

/-! ## Test objectives to validate normalization rules on constant declared at top level using the `opaque` keyword -/


/-! Test cases to ensure that opaque variables are replaced with their expected values -/

opaque x : Nat
-- x = 0 ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_1" ] x = 0 ===> True

-- x ===> 0
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
def constOpaque_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "constOpaque_2" : term => return constOpaque_2

#testOptimize [ "ConstOpaque_2" ] x ===> constOpaque_2

opaque y : Int
-- y = 0 ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_3" ] y = 0 ===> True

-- y ===> 0
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
def constOpaque_4 : Expr :=
  Lean.Expr.app (Lean.Expr.const `Int.ofNat []) (Lean.Expr.lit (Lean.Literal.natVal 0))
elab "constOpaque_4" : term => return constOpaque_4

#testOptimize [ "ConstOpaque_4" ] y ===> constOpaque_4

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Inhabited

opaque c : Color

-- c = Color.transparent ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_5" ] c = Color.transparent ===> True

-- c ===> Color.transparent
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_6" ] c ===> Color.transparent

opaque l : List Nat

-- l = [] ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_7" ] l = [] ===> True

-- l ===> []
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_8" ] l ===> ([] : List Nat)


-- l = List.nil ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_9" ] l = List.nil ===> True

-- l ===> List.nil
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_10" ] l ===> (List.nil : List Nat)

opaque s : String
-- s = "" ===> True
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_11" ] s = "" ===> True

-- s ===> ""
-- NOTE: Test cases to validate that opaque with no assignment is reduced to default value
#testOptimize [ "ConstOpaque_12" ] s ===> ""


opaque n : Nat := 100
-- n = 100 ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_13" ] n = 100 ===> True

-- n ===> 100
-- NOTE: Test cases to validate assigned opaque
def constOpaque_14 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "constOpaque_14" : term => return constOpaque_14

#testOptimize [ "ConstOpaque_14" ] n ===> constOpaque_14

opaque m : Int := -45
-- m = -45 ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_15" ] y = 0 ===> True

-- m ===> -45
-- NOTE: Test cases to validate assigned opaque
def constOpaque_16 : Expr :=
  Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 44))
elab "constOpaque_16" : term => return constOpaque_16

#testOptimize [ "ConstOpaque_16" ] m ===> constOpaque_16

opaque red : Color := Color.red Color.transparent

-- red = Color.red Color.transparent ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_17" ] red = Color.red Color.transparent ===> True

-- red ===> Color.red Color.transparent
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_18" ] red ===> Color.red Color.transparent

opaque xs : List Nat := [1, 2, 3]

-- xs = [1, 2, 3] ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_19" ] xs = [1, 2, 3] ===> True

-- xs ===> [1, 2, 3]
-- NOTE: Test cases to validate assigned opaque
def constOpaque_20 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.lit (Lean.Literal.natVal 1)))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
      (Lean.Expr.lit (Lean.Literal.natVal 2)))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.lit (Lean.Literal.natVal 3)))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat []))))
elab "constOpaque_20" : term => return constOpaque_20

#testOptimize [ "ConstOpaque_20" ] xs ===> constOpaque_20

opaque str : String := "testOptimize"
-- str = "testOptimize" ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_21" ] str = "testOptimize" ===> True

-- str ===> "testOptimize"
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_22" ] str ===> "testOptimize"

-- x + n = 100 ===> True
#testOptimize [ "ConstOpaque_23" ] x + n = 100 ===> True

-- x + n ===> 100
#testOptimize [ "ConstOpaque_24" ] x + n ===> constOpaque_14

-- y + m = -45 ===> True
#testOptimize [ "ConstOpaque_25" ] y + m = -45 ===> True

-- y + m ===> -45
#testOptimize [ "ConstOpaque_24" ] y + m ===> constOpaque_16

-- red = c ===> False
#testOptimize [ "ConstOpaque_25" ] red = c ===> False

-- l = xs ===> False
#testOptimize [ "ConstOpaque_26" ] l = xs ===> False

-- List.length xs = 3 ===> True
#testOptimize [ "ConstOpaque_27" ] List.length xs = 3 ===> True

-- s = str ===> False
#testOptimize [ "ConstOpaque_28" ] s = str ===> False

-- String.length str = 12 ===> True
#testOptimize [ "ConstOpaque_29" ] String.length str = 12 ===> True


/-! Test cases to ensure that non-opaque variables are properly handled as free variables. -/

variable (z : Nat)
-- z ===> z
#testOptimize [ "ConstOpaqueUnchanged_1" ] z ===> z

variable (p : Int)
-- p ===> p
#testOptimize [ "ConstOpaqueUnchanged_2" ] p ===> p

variable (ys : List Int)
-- ys ===> ys
#testOptimize [ "ConstOpaqueUnchanged_3" ] ys ===> ys

variable (anyColor : Color)
-- anyColor ===> anyColor
#testOptimize [ "ConstOpaqueUnchanged_4" ] anyColor ===> anyColor

variable (t : String)
-- t ===> t
#testOptimize [ "ConstOpaqueUnchanged_5" ] t ===> t

-- z + n = 100 + z ===> True
#testOptimize [ "ConstOpaqueUnchanged_6" ] z + n = 100 + z ===> True

-- p + m = -45 + p ===> True
#testOptimize [ "ConstOpaqueUnchanged_7" ] p + m = -45 + p ===> True

-- List.length ys + List.length xs = 3 + List.length ys ===> True
#testOptimize [ "ConstOpaqueUnchanged_8" ] List.length ys + List.length xs = 3 + List.length ys ===> True

-- String.append str t = String.append "testOptimize" t ===> True
#testOptimize [ "ConstOpaqueUnchanged_9" ] String.append str t = String.append "testOptimize" t ===> True

end Test.NormOpaque

