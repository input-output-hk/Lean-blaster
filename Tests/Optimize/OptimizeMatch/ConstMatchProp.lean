import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstMatchProp

/-! ## Test objectives to validate ite/match over match constant propagation. -/

/-! Test cases to validate when ite over match constant propagation must be applied. -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color
  deriving BEq

def beqColor : Color → Color → Bool
| .red x, .red y
| .blue x, .blue y => beqColor x y
| .transparent, .transparent
| .black, .black => true
| _, _ => false

-- ∀ (c : Bool) (x : Color), beqColor (if c then Color.red x else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)
#testOptimize [ "IteOverMatch_1" ]
  ∀ (c : Bool) (x : Color), beqColor (if c then Color.red x else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)

-- ∀ (b c : Bool) (x : Color),
--  beqColor (if c then (if b then Color.red x else Color.black) else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)
#testOptimize [ "IteOverMatch_2" ]
  ∀ (b c : Bool) (x : Color),
    beqColor (if c then (if b then Color.red x else Color.black) else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)

-- ∀ (b c : Bool) (x : Color),
--  beqColor (if c then Color.blue x else (if b then Color.red x else Color.black)) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color), true = (c && beqColor x x)
#testOptimize [ "IteOverMatch_3" ]
  ∀ (b c : Bool) (x : Color),
    beqColor (if c then Color.blue x else (if b then Color.red x else Color.black)) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color), true = (c && beqColor x x)

-- ∀ (b c d : Bool) (x : Color),
-- let op1 :=
--   if c
--   then if d then Color.transparent else Color.blue x
--   else if b then Color.red x else Color.black;
--  beqColor op1 (Color.blue x) ===>
-- ∀ (c d : Bool) (x : Color), true = (c && (!d && beqColor x x))
#testOptimize [ "IteOverMatch_4" ]
  ∀ (b c d: Bool) (x : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    beqColor op1 (Color.blue x) ===>
  ∀ (c d : Bool) (x : Color), true = (c && (!d && beqColor x x))

-- ∀ (b c d : Bool) (x : Color),
-- let op1 :=
--   if c
--   then if d then Color.transparent else Color.blue x
--   else if b then Color.red x else Color.black;
-- let op2 :=
--    if b then Color.blue x else Color.black
--  beqColor op1 op2 ===>
-- ∀ (b c d : Bool) (x : Color),
--  (false = c → false = b) ∧
--  (true = c → true = (!d && (b && beqColor x x)))
#testOptimize [ "IteOverMatch_5" ]
  ∀ (b c d: Bool) (x : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    let op2 := if b then Color.blue x else Color.black;
    beqColor op1 op2 ===>
  ∀ (b c d : Bool) (x : Color),
    (false = c → false = b) ∧
    (true = c → true = (!d && (b && beqColor x x)))

/-! Test cases to validate when ite over match constant propagation must NOT be applied. -/

-- ∀ (c : Bool) (x y : Color), beqColor (if c then Color.red x else y) (Color.blue x) ===>
-- ∀ (c : Bool) (x y : Color), true = beqColor (if true = c then Color.red x else y) (Color.blue x)
#testOptimize [ "IteOverMatchUnchanged_1" ]
  ∀ (c : Bool) (x y : Color), beqColor (if c then Color.red x else y) (Color.blue x) ===>
  ∀ (c : Bool) (x y : Color), true = beqColor (if true = c then Color.red x else y) (Color.blue x)

-- ∀ (b c : Bool) (x y : Color),
--  beqColor (if c then (if b then Color.red x else y) else Color.blue x) (Color.blue x) ===>
-- ∀ (b c : Bool) (x y : Color),
--  true = beqColor (if true = c then (if true = b then Color.red x else y) else Color.blue x) (Color.blue x)
#testOptimize [ "IteOverMatchUnchanged_2" ]
  ∀ (b c : Bool) (x y : Color),
    beqColor (if c then (if b then Color.red x else y) else Color.blue x) (Color.blue x) ===>
  ∀ (b c : Bool) (x y : Color),
    true = beqColor (if true = c then (if true = b then Color.red x else y) else Color.blue x) (Color.blue x)

-- ∀ (b c : Bool) (x y : Color),
--  beqColor (if c then Color.blue x else (if b then Color.red x else y)) (Color.blue x) ===>
-- ∀ (b c : Bool) (x y : Color),
--  true = beqColor (if true = c then Color.blue x else (if true = b then Color.red x else y)) (Color.blue x)
#testOptimize [ "IteOverMatchUnchanged_3" ]
  ∀ (b c : Bool) (x y : Color),
    beqColor (if c then Color.blue x else (if b then Color.red x else y)) (Color.blue x) ===>
  ∀ (b c : Bool) (x y : Color),
    true = beqColor (if true = c then Color.blue x else (if true = b then Color.red x else y)) (Color.blue x)

-- ∀ (b c d : Bool) (x y : Color),
-- let op1 :=
--   if c
--   then if d then Color.transparent else Color.blue x
--   else if b then Color.red x else y;
--  beqColor op1 (Color.blue x) ===>
-- ∀ (b c d : Bool) (x y : Color),
--  true =
--  beqColor
--    (if true = c then if true = d then Color.transparent else Color.blue x
--     else if true = b then Color.red x else y)
--    (Color.blue x)
#testOptimize [ "IteOverMatchUnchanged_4" ]
  ∀ (b c d: Bool) (x y : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else y;
    beqColor op1 (Color.blue x) ===>
  ∀ (b c d : Bool) (x y : Color),
    true =
      beqColor
        (if true = c then if true = d then Color.transparent else Color.blue x
         else if true = b then Color.red x else y)
      (Color.blue x)

-- ∀ (b c d : Bool) (x y : Color),
-- let op1 :=
--   if c
--   then if d then Color.transparent else Color.blue x
--   else if b then Color.red x else Color.black;
-- let op2 :=
--    if b then Color.blue x else y
--  beqColor op1 op2 ===>
-- ∀ (b c d : Bool) (x y : Color),
-- true =
--   beqColor
--    (if true = c then if true = d then Color.transparent else Color.blue x
--     else if true = b then Color.red x else Color.black)
--    (if true = b then Color.blue x else y)
#testOptimize [ "IteOverMatchUnchanged_5" ]
  ∀ (b c d: Bool) (x y : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    let op2 := if b then Color.blue x else y;
    beqColor op1 op2 ===>
  ∀ (b c d : Bool) (x y : Color),
       true =
         beqColor
          (if true = c then if true = d then Color.transparent else Color.blue x
           else if true = b then Color.red x else Color.black)
          (if true = b then Color.blue x else y)


/-! Test cases to validate when dite over match constant propagation must be applied. -/

-- ∀ (c : Bool) (x : Color) (f : c → Color → Color),
--   beqColor (if h : c then Color.red (f h x) else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)
#testOptimize [ "DIteOverMatch_1" ]
  ∀ (c : Bool) (x : Color) (f : c → Color → Color),
    beqColor (if h : c then Color.red (f h x) else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color), true = (!c && beqColor x x)

-- ∀ (b c : Bool) (x : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--   beqColor (if h1 : c
--             then (if h2 : b then Color.red (g h2 x) else Color.black)
--             else Color.blue (f h1 x)) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color) (f : false = c → Color → Color),
--   false = c ∧ (∀ (h1 : false = c), true = beqColor (f h1 x) x)
#testOptimize [ "DIteOverMatch_2" ]
  ∀ (b c : Bool) (x : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
    beqColor (if h1 : c
              then (if h2 : b then Color.red (g h2 x) else Color.black)
              else Color.blue (f h1 x)) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color) (f : false = c → Color → Color),
    false = c ∧ (∀ (h1 : false = c), true = beqColor (f h1 x) x)

-- ∀ (b c : Bool) (x : Color) (f : c → Color → Color) (g : b → Color → Color),
--   beqColor (if h1 : c
--             then Color.blue (f h1 x)
--             else (if h2 : b then Color.red (g h2 x) else Color.black)) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color) (f : true = c → Color → Color),
--   true = c ∧ (∀ (h1 : true = c), true = beqColor (f h1 x) x)
#testOptimize [ "DIteOverMatch_3" ]
  ∀ (b c : Bool) (x : Color) (f : c → Color → Color) (g : b → Color → Color),
    beqColor (if h1 : c
              then Color.blue (f h1 x)
              else (if h2 : b then Color.red (g h2 x) else Color.black)) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color) (f : true = c → Color → Color),
    true = c ∧ (∀ (h1 : true = c), true = beqColor (f h1 x) x)

-- ∀ (b c d: Bool) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   let op1 :=
--     if h1 : c
--     then if h2 : d then Color.transparent else Color.blue (g h2 x)
--     else if h3 : b then Color.red (t h3 x) else Color.red (f h1 y);
--   beqColor op1 (Color.blue x) ===>
-- ∀ (c d : Bool) (x : Color) (g : false = d → Color → Color),
--   (false = d ∧ ∀ (h2 : false = d), true = beqColor (g h2 x) x) ∧ true = c
#testOptimize [ "DIteOverMatch_4" ]
  ∀ (b c d: Bool) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    let op1 :=
      if h1 : c
      then if h2 : d then Color.transparent else Color.blue (g h2 x)
      else if h3 : b then Color.red (t h3 x) else Color.red (f h1 y);
    beqColor op1 (Color.blue x) ===>
  ∀ (c d : Bool) (x : Color) (g : false = d → Color → Color),
    (false = d ∧ ∀ (h2 : false = d), true = beqColor (g h2 x) x) ∧ true = c

-- ∀ (b c d: Bool) (x y : Color)
--   (f : c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   let op1 :=
--     if h1 : c
--     then if h2 : d then Color.red (f h1 y) else Color.blue (g h2 x)
--     else if h3 : b then Color.red (t h3 x) else Color.black;
--   let op2 := if h4 : b then Color.blue (t h4 x) else Color.black;
--   beqColor op1 op2 ===>
-- ∀ (b c d : Bool) (x : Color)
--   (g : false = d → Color → Color) (t : true = b → Color → Color),
--   (false = c → false = b) ∧
--   (true = c →
--     false = d ∧
--     (∀ (h2 : false = d),
--       true = b ∧ (∀ (h4 : true = b), true = beqColor (g h2 x) (t h4 x))))
#testOptimize [ "DIteOverMatch_5" ]
  ∀ (b c d: Bool) (x y : Color)
    (f : c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    let op1 :=
      if h1 : c
      then if h2 : d then Color.red (f h1 y) else Color.blue (g h2 x)
      else if h3 : b then Color.red (t h3 x) else Color.black;
    let op2 := if h4 : b then Color.blue (t h4 x) else Color.black;
    beqColor op1 op2 ===>
  ∀ (b c d : Bool) (x : Color)
    (g : false = d → Color → Color) (t : true = b → Color → Color),
    (false = c → false = b) ∧
    (true = c →
      false = d ∧
      (∀ (h2 : false = d),
        true = b ∧ (∀ (h4 : true = b), true = beqColor (g h2 x) (t h4 x))))

/-! Test cases to validate when dite over match constant propagation must NOT be applied. -/

-- ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
--   beqColor (if h : c then Color.red (f h x) else y) (Color.blue x) ===>
-- ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
--    true = beqColor (if h : c then Color.red (f h x) else y) (Color.blue x)
#testOptimize [ "DIteOverMatchUnchanged_1" ]
  ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
    beqColor (if h : c then Color.red (f h x) else y) (Color.blue x) ===>
  ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
     true = beqColor (if h : c then Color.red (f h x) else y) (Color.blue x)

-- ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--     beqColor (if h1 : c
--               then (if h2 : b then Color.red (g h2 x) else y)
--               else Color.blue (f h1 x)) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--   true = beqColor (if h1 : c
--                    then (if h2 : b then Color.red (g h2 x) else y)
--                    else Color.blue (f h1 x)) (Color.blue x)
#testOptimize [ "DIteOverMatchUnchanged_2" ]
  ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
      beqColor (if h1 : c
                then (if h2 : b then Color.red (g h2 x) else y)
                else Color.blue (f h1 x)) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
    true = beqColor (if h1 : c
                     then (if h2 : b then Color.red (g h2 x) else y)
                     else Color.blue (f h1 x)) (Color.blue x)

-- ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--     beqColor (if h1 : c
--               then Color.blue (f h1 x)
--               else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--     true = beqColor (if h1 : c
--                      then Color.blue (f h1 x)
--                      else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x)
#testOptimize [ "DIteOverMatchUnchanged_3" ]
  ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
      beqColor (if h1 : c
                then Color.blue (f h1 x)
                else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
      true = beqColor (if h1 : c
                       then Color.blue (f h1 x)
                       else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x)

-- ∀ (b c d: Prop) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c
--     then if h2 : d then Color.transparent else Color.blue (g h2 x)
--     else if h3 : b then Color.red (t h3 x) else (f h1 y);
--   beqColor op1 (Color.blue x) ===>
-- ∀ (b c d : Prop) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   true =
--     beqColor
--       (if h1 : c
--        then if h2 : d then Color.transparent else Color.blue (g h2 x)
--        else if h3 : b then Color.red (t h3 x) else (f h1 y))
--     (Color.blue x)
#testOptimize [ "DIteOverMatchUnchanged_4" ]
  ∀ (b c d: Prop) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    [Decidable b] → [Decidable c] → [Decidable d] →
    let op1 :=
      if h1 : c
      then if h2 : d then Color.transparent else Color.blue (g h2 x)
      else if h3 : b then Color.red (t h3 x) else (f h1 y);
    beqColor op1 (Color.blue x) ===>
  ∀ (b c d : Prop) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    [Decidable b] → [Decidable c] → [Decidable d] →
    true =
      beqColor
        (if h1 : c
         then if h2 : d then Color.transparent else Color.blue (g h2 x)
         else if h3 : b then Color.red (t h3 x) else (f h1 y))
      (Color.blue x)

-- ∀ (b c d: Prop) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c
--     then if h2 : d then Color.transparent else Color.blue (g h2 x)
--     else if h3 : b then Color.red (t h3 x) else (f h1 y);
--   let op2 := if h4 : b then Color.blue (t h4 x) else y;
--   beqColor op1 op2 ===>
-- ∀ (b c d : Prop) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--      true =
--        beqColor
--         (if h1 : c
--          then if h2 : d then Color.transparent else Color.blue (g h2 x)
--          else if h3 : b then Color.red (t h3 x) else (f h1 y))
--         (if h4 : b then Color.blue (t h4 x) else y)
#testOptimize [ "DIteOverMatchUnchanged_5" ]
  ∀ (b c d: Prop) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    [Decidable b] → [Decidable c] → [Decidable d] →
    let op1 :=
      if h1 : c
      then if h2 : d then Color.transparent else Color.blue (g h2 x)
      else if h3 : b then Color.red (t h3 x) else (f h1 y);
    let op2 := if h4 : b then Color.blue (t h4 x) else y;
    beqColor op1 op2 ===>
  ∀ (b c d : Prop) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    [Decidable b] → [Decidable c] → [Decidable d] →
       true =
         beqColor
          (if h1 : c
           then if h2 : d then Color.transparent else Color.blue (g h2 x)
           else if h3 : b then Color.red (t h3 x) else (f h1 y))
          (if h4 : b then Color.blue (t h4 x) else y)


/-! Test cases to validate when match over match constant propagation must be applied. -/

def toColorOne (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some _ => .blue .transparent

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) (Color.blue x) ===>
-- ∀ (n : Option Nat) (x : Color),
--    true = ( toColorOne.match_1 (fun (_ : Option Nat) => Bool) n
--             (fun (_ : PUnit) => false)
--             (fun (_ : PUnit) => false)
--             (fun (_ : PUnit) => false)
--             (fun (_ : PUnit) => beqColor Color.black x)
--             (fun (_ : Nat) => beqColor Color.transparent x) )
#testOptimize [ "MatchOverMatch_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) (Color.blue x) ===>
  ∀ (n : Option Nat) (x : Color),
       ( toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
         (fun (_ : PUnit) => False)
         (fun (_ : PUnit) => False)
         (fun (_ : PUnit) => False)
         (fun (_ : PUnit) => true = beqColor Color.black x)
         (fun (_ : Nat) => true = beqColor Color.transparent x) )

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (Color.blue x) ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
--   ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
--      (fun (_ : PUnit) => False)
--      (fun (_ : α) => true = beqColor Color.transparent x) )
--      true = ( toColorTwo.match_1 (fun (_ : Option α) => Bool) n
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverMatch_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (Color.blue x) ===>
  ∀ (α : Type) (n : Option α) (x : Color),
      ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
        (fun (_ : PUnit) => False)
        (fun (_ : α) => true = beqColor Color.transparent x) )


inductive ColorPrim (α : Type u) where
  | red : ColorPrim α → ColorPrim α
  | transparent : α -> ColorPrim α
  | blue : ColorPrim α → ColorPrim α
  | black : α -> ColorPrim α
  | white : ColorPrim α

def beqColorPrim [BEq α]: ColorPrim α → ColorPrim α → Bool
| .red x, .red y
| .blue x, .blue y => beqColorPrim x y
| .transparent t1, .transparent t2
| .black t1, .black t2 => t1 == t2
| .white, .white => true
| _, _ => false

def toColorThree (x : Option α) : ColorPrim α :=
 match x with
 | none => .white
 | some n => .blue (.transparent n)

-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) (ColorPrim.blue x) ===>
-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
--    ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
--      (fun (_ : PUnit) => False)
--      (fun (a : α) => true = beqColorPrim (ColorPrim.transparent a) x) )
-- NOTE: Test case to ensure that generic type are also properly handled
-- NOTE: Lean4 already applied structural equivalence between toColorThree.match_1 and toColorTwo.match_1
#testOptimize [ "MatchOverMatch_3" ]
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) (ColorPrim.blue x) ===>
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
    ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
      (fun (_ : PUnit) => False)
      (fun (a : α) => true = beqColorPrim (ColorPrim.transparent a) x) )

def boolToNat (n : Nat) (x : Bool) : Nat :=
  match x with
  | true => 1
  | false => n

-- ∀ (c : Bool) (x : Color),
--   boolToNat ((if c then Color.red x else Color.blue x) == (Color.blue x)) = 1 ===>
-- ∀ (n : Nat), 1 = n
#testOptimize [ "MatchOverMatch_4" ] (norm-result: 1)
  ∀ (c : Bool) (n : Nat) (x : Color),
    boolToNat n ((if c then Color.red x else Color.transparent) == (Color.blue x)) = 1 ===>
  ∀ (n : Nat), 1 = n


def toColorFour (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some n => if n < 10 then .blue .transparent
             else if n < 100 then .red .black
             else .red .transparent

-- ∀ (n : Option Nat) (x : Color),
--   beqColor (toColorFour n) (Color.blue x) ===>
-- ∀ (n : Option Nat) (x : Color),
--   ( toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
--      (fun (_ : PUnit) => False)
--      (fun (_ : PUnit) => False)
--      (fun (_ : PUnit) => False)
--      (fun (_ : PUnit) => true = beqColor Color.black x)
--      (fun (a : Nat) =>
--        true = beqColor Color.transparent x ∧ a < 10) )
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that simplification rule can transitively detect
-- that all path reduce to constant values
-- NOTE: Can be reduced further with additional simplification rules
#testOptimize [ "MatchOverMatch_5" ] (norm-result: 1)
  ∀ (n : Option Nat) (x : Color),
    beqColor (toColorFour n) (Color.blue x) ===>
  ∀ (n : Option Nat) (x : Color),
     ( toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => true = beqColor Color.black x)
      (fun (a : Nat) =>
          true = beqColor Color.transparent x ∧ a < 10) )

def beqColorDegree : Color → Color → (Nat → Bool)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then true else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => true
| _, _ => λ _n => false

-- ∀ (n : Option Nat) (y : Nat) (x : Color),
--    beqColorDegree (toColorFour n) (Color.blue x) y ===>
-- ∀ (n : Option Nat) (y : Nat) (x : Color),
-- toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
--   (fun (_ : PUnit) => False)
--   (fun (_ : PUnit) => False)
--   (fun (_ : PUnit) => False)
--   (fun (_ : PUnit) => ¬ 0 = y → true = beqColor Color.black x)
--   (fun (a : Nat) =>
--       a < 10 ∧
--       (¬ 0 = y → true = beqColor Color.transparent x) )
-- NOTE: Test case to ensure that functions as rhs of match patterns are properly handled.
#testOptimize [ "MatchOverMatch_6" ] (norm-result: 1)
  ∀ (n : Option Nat) (y : Nat) (x : Color),
    beqColorDegree (toColorFour n) (Color.blue x) y ===>
  ∀ (n : Option Nat) (y : Nat) (x : Color),
    toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => False)
      (fun (_ : PUnit) => ¬ 0 = y → true = beqColor Color.black x)
      (fun (a : Nat) =>
          a < 10 ∧
          (¬ 0 = y → true = beqColor Color.transparent x) )

/-! Test cases to validate when match over match constant propagation must NOT be applied. -/

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
-- ∀ (n : Option Nat) (x : Color),
--    true =
--      beqColor
--      ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--        (fun (_ : PUnit) => .black)
--        (fun (_ : PUnit) => .transparent)
--        (fun (_ : PUnit) =>  .red .transparent)
--        (fun (_ : PUnit) => .blue .black)
--        (fun (_ : Nat) => .blue .transparent) ) x
#testOptimize [ "MatchOverMatchUnchanged_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
  ∀ (n : Option Nat) (x : Color),
       true =
       beqColor
       ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
         (fun (_ : PUnit) => .black)
         (fun (_ : PUnit) => .transparent)
         (fun (_ : PUnit) =>  .red .transparent)
         (fun (_ : PUnit) => .blue .black)
         (fun (_ : Nat) => .blue .transparent) ) x

-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
-- true =
-- beqColor
-- ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
--   (fun (_ : PUnit) => .black)
--   (fun (_ : α) => .blue .transparent) ) x

#testOptimize [ "MatchOverMatchUnchanged_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
  ∀ (α : Type) (n : Option α) (x : Color),
    true =
    beqColor
    ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
      (fun (_ : PUnit) => .black)
      (fun (_ : α) => .blue .transparent) ) x

-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) x ===>
-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
--      true =
--      beqColorPrim
--      ( toColorTwo.match_1 (fun (_ : Option α) => ColorPrim α) n
--        (fun (_ : PUnit) => .white)
--        (fun (a : α) => .blue (.transparent a) ) ) x
-- NOTE: Lean4 already applied structural equivalence between toColorThree.match_1 and toColorTwo.match_1
#testOptimize [ "MatchOverMatchUnchanged_3" ]
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) x ===>
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
       true =
       beqColorPrim
       ( toColorTwo.match_1 (fun (_ : Option α) => ColorPrim α) n
         (fun (_ : PUnit) => .white)
         (fun (a : α) => .blue (.transparent a) ) ) x

-- ∀ (n : Option Nat) (x : Color),
--   beqColor (toColorFour n) x ===>
-- ∀ (n : Option Nat) (x : Color),
--   true =
--    beqColor
--     ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--       (fun (_ : PUnit) => .black)
--       (fun (_ : PUnit) => .transparent)
--       (fun (_ : PUnit) => .red .transparent)
--       (fun (_ : PUnit) => .blue .black)
--       (fun (a : Nat) =>
--         if a < 10 then .blue .transparent else
--         if a < 100 then .red .black
--         else .red .transparent ) ) x

-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
#testOptimize [ "MatchOverMatchUnchanged_4" ] (norm-result: 1)
  ∀ (n : Option Nat) (x : Color),
    beqColor (toColorFour n) x ===>
  ∀ (n : Option Nat) (x : Color),
    true =
     beqColor
      ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
        (fun (_ : PUnit) => .black)
        (fun (_ : PUnit) => .transparent)
        (fun (_ : PUnit) => .red .transparent)
        (fun (_ : PUnit) => .blue .black)
        (fun (a : Nat) =>
          if a < 10 then .blue .transparent else
          if a < 100 then .red .black
          else .red .transparent ) ) x

end Tests.ConstMatchProp



