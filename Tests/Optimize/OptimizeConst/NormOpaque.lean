import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.NormOpaque

/-! ## Test objectives to validate `opaque` variables shall not be replaced with their default value -/


/-! Test cases to ensure that opaque variables shall not be replaced with their default value -/

opaque x : Nat
-- x = 0 ===> 0 = x
#testOptimize [ "ConstOpaque_1", proof ] (norm-result: 1) x = 0 ===> 0 = x

-- x ===> x
#testOptimize [ "ConstOpaque_2", proof ] x ===> x

opaque y : Int := 10

-- y = 10 ===> 10 = y
#testOptimize [ "ConstOpaque_3", proof ] (norm-result: 1) y = 10  ===> 10 = y

-- x ===> x
#testOptimize [ "ConstOpaque_4", proof ] y ===> y

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Inhabited

opaque c : Color

-- c = Color.transparent ===> Color.transparent = c
#testOptimize [ "ConstOpaque_5", proof ] c = Color.transparent ===> Color.transparent = c

-- c ===> c
#testOptimize [ "ConstOpaque_6", proof ] c ===> c

opaque l : List Nat

-- l = [] ===> [] = l
#testOptimize [ "ConstOpaque_7", proof ] l = [] ===> [] = l

-- l ===> l
#testOptimize [ "ConstOpaque_8", proof ] l ===> l


-- l = List.nil ===> List.nil = l
#testOptimize [ "ConstOpaque_9", proof ] l = List.nil ===> List.nil = l

opaque l' : List Nat := [10]
-- l' ===> l'
#testOptimize [ "ConstOpaque_10", proof ] l' ===> l'

opaque s : String
#testOptimize [ "ConstOpaque_11", proof ] s = "" ===> "" = s

-- s ===> s
#testOptimize [ "ConstOpaque_12", proof ] s ===> s

opaque n : Nat := 100
-- n = 100 ===> 100 = n
#testOptimize [ "ConstOpaque_13", proof ] (norm-result: 1) n = 100 ===> 100 = n

-- n ===> n
#testOptimize [ "ConstOpaque_14", proof ] n ===> n

opaque m : Int := -45
-- m = -45 ===> -45 = m
def constOpaque_15 : Expr :=
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
    (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 44))))
  (Lean.Expr.const `Test.NormOpaque.m [])
elab "constOpaque_15" : term => return constOpaque_15

#testOptimize [ "ConstOpaque_15", proof ] (norm-result: 1) m = (-45) ===> constOpaque_15

-- m ===> m
#testOptimize [ "ConstOpaque_16", proof ] m ===> m

opaque red : Color := Color.red Color.transparent

-- red = Color.red Color.transparent ===> Color.red Color.transparent = red
#testOptimize [ "ConstOpaque_17", proof ] red = Color.red Color.transparent ===> Color.red Color.transparent = red

-- red ===> red
#testOptimize [ "ConstOpaque_18", proof ] red ===> red

opaque xs : List Nat := [1, 2, 3]

-- xs = [1, 2, 3] ===> True
-- NOTE: Test cases to validate assigned opaque
#testOptimize [ "ConstOpaque_19", proof ] (norm-result: 1) xs = [1, 2, 3] ===> [1, 2, 3] = xs

-- xs ===> xs
#testOptimize [ "ConstOpaque_20", proof ] xs ===> xs

opaque str : String := "testOptimize"
-- str = "testOptimize" ===> "testOptimize" = str
#testOptimize [ "ConstOpaque_21", proof ] str = "testOptimize" ===> "testOptimize" = str

-- str ===> str
#testOptimize [ "ConstOpaque_22", proof ] str ===> str

-- x + n = 100 ===> 100 = Nat.add n x
#testOptimize [ "ConstOpaque_23", proof ] (norm-result: 1) x + n = 100 ===> 100 = Nat.add n x

-- x + n ===> Nat.add n x
#testOptimize [ "ConstOpaque_24", proof ] x + n ===> Nat.add n x

-- y + m = -45 ===> -45 = m + y
def constOpaque_25 : Expr :=
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
    (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 44))))
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Int.add []) (Lean.Expr.const `Test.NormOpaque.m []))
    (Lean.Expr.const `Test.NormOpaque.y []))
elab "constOpaque_25" : term => return constOpaque_25
#testOptimize [ "ConstOpaque_25", proof ] y + m = -45 ===> constOpaque_25

-- y + m ===> Int.add m y
#testOptimize [ "ConstOpaque_24", proof ] y + m ===> Int.add m y

-- red = c ===> c = red
#testOptimize [ "ConstOpaque_25", proof ] red = c ===> c = red

-- l = xs ===> l = xs
#testOptimize [ "ConstOpaque_26", proof ] l = xs ===> l = xs

-- List.length xs = 3 ===> 3 = List.length xs
#testOptimize [ "ConstOpaque_27", proof ] (norm-result: 1) List.length xs = 3 ===> 3 = List.length xs

-- s = str ===> s = str
#testOptimize [ "ConstOpaque_28", proof ] s = str ===> s = str

-- String.length str = 12 ===> 12 = String.length str
#testOptimize [ "ConstOpaque_29", proof ] (norm-result: 1) String.length str = 12 ===> 12 = String.length str


/-! Test cases to ensure that non-opaque variables are properly handled as free variables. -/

variable (z : Nat)
-- z ===> z
#testOptimize [ "ConstOpaqueUnchanged_1", proof ] z ===> z

variable (p : Int)
-- p ===> p
#testOptimize [ "ConstOpaqueUnchanged_2", proof ] p ===> p

variable (ys : List Int)
-- ys ===> ys
#testOptimize [ "ConstOpaqueUnchanged_3", proof ] ys ===> ys

variable (anyColor : Color)
-- anyColor ===> anyColor
#testOptimize [ "ConstOpaqueUnchanged_4", proof ] anyColor ===> anyColor

variable (t : String)
-- t ===> t
#testOptimize [ "ConstOpaqueUnchanged_5", proof ] t ===> t

-- z + n = 100 + z ===> 100 = n
#testOptimize [ "ConstOpaqueUnchanged_6", proof ] (norm-result: 1) z + n = 100 + z ===> 100 = n

-- p + m = -45 + p ===> -45 = m
def constOpaqueUnchanged_7 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
    (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 44))))
  (Lean.Expr.const `Test.NormOpaque.m [])
elab "constOpaqueUnchanged_7" : term => return constOpaqueUnchanged_7
#testOptimize [ "ConstOpaqueUnchanged_7", proof ] p + m = -45 + p ===> constOpaqueUnchanged_7

-- List.length ys + List.length xs = 3 + List.length ys ===> 3 = List.length xs
#testOptimize [ "ConstOpaqueUnchanged_8", proof ] (norm-result: 1)
  List.length ys + List.length xs = 3 + List.length ys ===> 3 = List.length xs

-- String.append str t = String.append "testOptimize" t ===> String.append str t = String.append "testOptimize" t
#testOptimize [ "ConstOpaqueUnchanged_9", proof ]
  String.append str t = String.append "testOptimize" t ===>
  String.append str t = String.append "testOptimize" t

end Test.NormOpaque

