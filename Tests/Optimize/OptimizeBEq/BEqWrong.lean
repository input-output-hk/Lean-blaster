import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.BEqWrong
/-! ## Test objectives to ensure that normalization and simplification rules for ``BEq.beq
       are only applied for known types satisfying predicate `isOpaqueBeq`.
-/

/-! Test cases for `reduceApp` rule on wrongly defined ``BEq.beq instance. -/

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Repr

def color_beq (x : Color) (y : Color) : Bool :=
  match x, y with
  | Color.transparent, Color.transparent => true
  | Color.red c1, Color.red c2 => color_beq c1 c2
  | _, _ => false

-- providing a BEq instance not satisfying refl, symm and trans properties
instance instBEqColor : BEq Color where
  beq a b := color_beq a b

-- Color.red Color.transparent == Color.red Color.transparent ===> false
#testOptimize [ "BEqWrongCst_1" ] Color.red Color.transparent == Color.red Color.transparent ===> true

-- Color.red Color.transparent == Color.blue Color.transparent ===> false
#testOptimize [ "BEqWrongCst_2" ] Color.red Color.transparent == Color.blue Color.transparent ===> false

-- Color.blue Color.transparent == Color.blue Color.transparent ===> false
#testOptimize [ "BEqWrongCst_3" ] Color.blue Color.transparent == Color.blue Color.transparent ===> false

-- Color.yellow Color.transparent == Color.yellow Color.transparent ===> false
#testOptimize [ "BEqWrongCst_4" ] Color.yellow Color.transparent == Color.yellow Color.transparent ===> false

-- Color.red Color.transparent == Color.yellow Color.transparent ===> false
#testOptimize [ "BEqWrongCst_5" ] Color.red Color.transparent == Color.yellow Color.transparent ===> false

-- Color.yellow Color.transparent == Color.blue Color.transparent ===> false
#testOptimize [ "BEqWrongCst_6" ] Color.yellow Color.transparent == Color.blue Color.transparent ===> false

-- Color.red (Color.blue Color.transparent) == Color.red Color.transparent ===> false
#testOptimize [ "BEqWrongCst_7" ] Color.red (Color.blue Color.transparent) == Color.red Color.transparent ===> false

-- Color.red (Color.yellow Color.transparent) == Color.red Color.transparent ===> false
#testOptimize [ "BEqWrongCst_8" ] Color.red (Color.yellow Color.transparent) == Color.red Color.transparent ===> false

-- Color.red (Color.yellow Color.transparent) == Color.red (Color.yellow Color.transparent) ===> false
#testOptimize [ "BEqWrongCst_9" ] Color.red (Color.yellow Color.transparent) == Color.red (Color.yellow Color.transparent) ===> false

-- Color.red (Color.blue Color.transparent) == Color.red (Color.yellow Color.transparent) ===> false
#testOptimize [ "BEqWrongCst_10" ] Color.red (Color.blue Color.transparent) == Color.red (Color.yellow Color.transparent) ===> false


/-! Test cases to ensure that the following simplification rules must not be applied on
    unknown `BEq.beq` instances.
     - `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`
     - `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`
-/

-- x == Color.red Color.transparent ===> color_beq x Color.red Color.transparent
#testOptimize [ "BEqWrongUnchanged_1" ] ∀ (x : Color), (x == (Color.red Color.transparent)) ===>
                                        ∀ (x : Color), true = (color_beq x (Color.red Color.transparent))

-- x == x ===> color_beq x x
#testOptimize [ "BEqWrongUnchanged_2" ] ∀ (x : Color), x == x ===>
                                        ∀ (x : Color), true = color_beq x x

-- x == y ===> color_beq x y
#testOptimize [ "BEqWrongUnchanged_3" ] ∀ (x y : Color), x == y ===>
                                        ∀ (x y : Color), true = color_beq x y

end Test.BEqWrong
