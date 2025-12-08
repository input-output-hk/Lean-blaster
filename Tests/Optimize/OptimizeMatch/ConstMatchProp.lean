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

def beqColor : Color → Color → Prop
| .red x, .red y
| .blue x, .blue y => x = y
| .transparent, .transparent
| .black, .black => True
| _, _ => False

-- ∀ (c : Bool) (x : Color), beqColor (if c then Color.red x else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool), false = c
#testOptimize [ "IteOverMatch_1" ]
  ∀ (c : Bool) (x : Color), beqColor (if c then Color.red x else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool), false = c

-- ∀ (b c : Bool) (x : Color),
--   beqColor (if c then (if b then Color.red x else Color.black) else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool), false = c
#testOptimize [ "IteOverMatch_2" ]
  ∀ (b c : Bool) (x : Color),
    beqColor (if c then (if b then Color.red x else Color.black) else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool), false = c

-- ∀ (b c : Bool) (x : Color),
--   beqColor (if c then Color.blue x else (if b then Color.red x else Color.black)) (Color.blue x) ===>
-- ∀ (c : Bool), true = c
#testOptimize [ "IteOverMatch_3" ]
  ∀ (b c : Bool) (x : Color),
    beqColor (if c then Color.blue x else (if b then Color.red x else Color.black)) (Color.blue x) ===>
  ∀ (c : Bool), true = c

-- ∀ (b c d : Bool) (x : Color),
-- let op1 :=
--   if c
--   then if d then Color.transparent else Color.blue x
--   else if b then Color.red x else Color.black;
--  beqColor op1 (Color.blue x) ===>
-- ∀ (c d : Bool), true = (c && !d)
#testOptimize [ "IteOverMatch_4" ]
  ∀ (b c d: Bool) (x : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    beqColor op1 (Color.blue x) ===>
  ∀ (c d : Bool), true = (c && !d)

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
--  (true = c → true = (b && !d))
#testOptimize [ "IteOverMatch_5" ]
  ∀ (b c d: Bool) (x : Color),
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    let op2 := if b then Color.blue x else Color.black;
    beqColor op1 op2 ===>
  ∀ (b c d : Bool),
    (false = c → false = b) ∧
    (true = c → true = (b && !d))

/-! Test cases to validate when ite over match constant propagation must NOT be applied. -/

-- ∀ (c : Prop) (x y : Color), [Decidable c] →
--      beqColor (if c then Color.red x else y) (Color.blue x) ===>
-- ∀ (c : Prop) (x y : Color),
--  beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--  (Blaster.dite' c (fun _ : c => Color.red x) (fun _ : ¬ c => y)) (Color.blue x)
--  (fun (x : Color) (y : Color) => x = y)
--  (fun (x : Color) (y : Color) => x = y)
--  (fun (_ : Unit) => True)
--  (fun (_ : Unit) => True)
--  (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "IteOverMatchUnchanged_1" ]
  ∀ (c : Prop) (x y : Color), [Decidable c] →
       beqColor (if c then Color.red x else y) (Color.blue x) ===>
  ∀ (c : Prop) (x y : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
    (Blaster.dite' c (fun _ : c => Color.red x) (fun _ : ¬ c => y)) (Color.blue x)
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)

-- ∀ (b c : Prop) (x y : Color), [Decidable b] → [Decidable c] →
--   beqColor (if c then (if b then Color.red x else y) else Color.blue x) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--    (Blaster.dite' c
--       (fun _ : c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y))
--       (fun _ : ¬ c => Color.blue x))
--   (Color.blue x)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "IteOverMatchUnchanged_2" ]
  ∀ (b c : Prop) (x y : Color), [Decidable b] → [Decidable c] →
    beqColor (if c then (if b then Color.red x else y) else Color.blue x) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
     (Blaster.dite' c
        (fun _ : c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y))
        (fun _ : ¬ c => Color.blue x))
    (Color.blue x)
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)

-- ∀ (b c : Prop) (x y : Color), [Decidable b] → [Decidable c] →
--   beqColor (if c then Color.blue x else (if b then Color.red x else y)) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--   (Blaster.dite' c
--     (fun _ : c => Color.blue x)
--     (fun _ : ¬ c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y)))
--   (Color.blue x)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "IteOverMatchUnchanged_3" ]
  ∀ (b c : Prop) (x y : Color), [Decidable b] → [Decidable c] →
    beqColor (if c then Color.blue x else (if b then Color.red x else y)) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
    (Blaster.dite' c
      (fun _ : c => Color.blue x)
      (fun _ : ¬ c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y)))
    (Color.blue x)
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)


-- ∀ (b c d: Prop) (x y : Color), [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then Color.transparent else Color.blue x
--     else if b then Color.red x else y;
--   beqColor op1 (Color.blue x) ===>
-- ∀ (b c d : Prop) (x y : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--   (Blaster.dite' c
--     (fun _ : c =>
--       Blaster.dite' d (fun _ : d => Color.transparent) (fun _ : ¬ d => Color.blue x))
--     (fun _ : ¬ c =>
--       Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y)))
--    (Color.blue x)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "IteOverMatchUnchanged_4" ]
  ∀ (b c d: Prop) (x y : Color), [Decidable b] → [Decidable c] → [Decidable d] →
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else y;
    beqColor op1 (Color.blue x) ===>
  ∀ (b c d : Prop) (x y : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
    (Blaster.dite' c
      (fun _ : c =>
        Blaster.dite' d (fun _ : d => Color.transparent) (fun _ : ¬ d => Color.blue x))
      (fun _ : ¬ c =>
        Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => y)))
     (Color.blue x)
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)

-- ∀ (b c d: Prop) (x y : Color), [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then Color.transparent else Color.blue x
--     else if b then Color.red x else Color.black;
--   let op2 := if b then Color.blue x else y;
--   beqColor op1 op2 ===>
-- ∀ (b c d : Prop) (x y : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--    (Blaster.dite' c
--      (fun _ : c => Blaster.dite' d (fun _ : d => Color.transparent) (fun _ : ¬ d => Color.blue x))
--      (fun _ : ¬ c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => Color.black)))
--    (Blaster.dite' b (fun _ : b => Color.blue x) (fun _ : ¬ b => y))
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "IteOverMatchUnchanged_5" ]
  ∀ (b c d: Prop) (x y : Color), [Decidable b] → [Decidable c] → [Decidable d] →
    let op1 :=
      if c
      then if d then Color.transparent else Color.blue x
      else if b then Color.red x else Color.black;
    let op2 := if b then Color.blue x else y;
    beqColor op1 op2 ===>
  ∀ (b c d : Prop) (x y : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
     (Blaster.dite' c
       (fun _ : c => Blaster.dite' d (fun _ : d => Color.transparent) (fun _ : ¬ d => Color.blue x))
       (fun _ : ¬ c => Blaster.dite' b (fun _ : b => Color.red x) (fun _ : ¬ b => Color.black)))
     (Blaster.dite' b (fun _ : b => Color.blue x) (fun _ : ¬ b => y))
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)


/-! Test cases to validate when dite over match constant propagation must be applied. -/

-- ∀ (c : Bool) (x : Color) (f : c → Color → Color),
--   beqColor (if h : c then Color.red (f h x) else Color.blue x) (Color.blue x) ===>
-- ∀ (c : Bool), false = c
#testOptimize [ "DIteOverMatch_1" ]
  ∀ (c : Bool) (x : Color) (f : c → Color → Color),
    beqColor (if h : c then Color.red (f h x) else Color.blue x) (Color.blue x) ===>
  ∀ (c : Bool), false = c

-- ∀ (b c : Bool) (x : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--   beqColor (if h1 : c
--             then (if h2 : b then Color.red (g h2 x) else Color.black)
--             else Color.blue (f h1 x)) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color) (f : false = c → Color → Color),
--   false = c ∧ ∀ (h1 : false = c), x = f h1 x
#testOptimize [ "DIteOverMatch_2" ]
  ∀ (b c : Bool) (x : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
    beqColor (if h1 : c
              then (if h2 : b then Color.red (g h2 x) else Color.black)
              else Color.blue (f h1 x)) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color) (f : false = c → Color → Color),
    false = c ∧ ∀ (h1 : false = c), x = f h1 x

-- ∀ (b c : Bool) (x : Color) (f : c → Color → Color) (g : b → Color → Color),
--   beqColor (if h1 : c
--             then Color.blue (f h1 x)
--             else (if h2 : b then Color.red (g h2 x) else Color.black)) (Color.blue x) ===>
-- ∀ (c : Bool) (x : Color) (f : true = c → Color → Color),
--   true = c ∧ ∀ (h1 : true = c), x = f h1 x
#testOptimize [ "DIteOverMatch_3" ]
  ∀ (b c : Bool) (x : Color) (f : c → Color → Color) (g : b → Color → Color),
    beqColor (if h1 : c
              then Color.blue (f h1 x)
              else (if h2 : b then Color.red (g h2 x) else Color.black)) (Color.blue x) ===>
  ∀ (c : Bool) (x : Color) (f : true = c → Color → Color),
    true = c ∧ ∀ (h1 : true = c), x = f h1 x

-- ∀ (b c d: Bool) (x y : Color)
--   (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
--   let op1 :=
--     if h1 : c
--     then if h2 : d then Color.transparent else Color.blue (g h2 x)
--     else if h3 : b then Color.red (t h3 x) else Color.red (f h1 y);
--   beqColor op1 (Color.blue x) ===>
-- ∀ (c d : Bool) (x : Color) (g : false = d → Color → Color),
--   (false = d ∧ ∀ (h2 : false = d), x = g h2 x) ∧ true = c
#testOptimize [ "DIteOverMatch_4" ]
  ∀ (b c d: Bool) (x y : Color)
    (f : ¬ c → Color → Color) (g : ¬ d → Color → Color) (t : b → Color → Color),
    let op1 :=
      if h1 : c
      then if h2 : d then Color.transparent else Color.blue (g h2 x)
      else if h3 : b then Color.red (t h3 x) else Color.red (f h1 y);
    beqColor op1 (Color.blue x) ===>
  ∀ (c d : Bool) (x : Color) (g : false = d → Color → Color),
    (false = d ∧ ∀ (h2 : false = d), x = g h2 x) ∧ true = c

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
--       true = b ∧ (∀ (h4 : true = b), g h2 x = t h4 x)))
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
        true = b ∧ (∀ (h4 : true = b), g h2 x = t h4 x)))

/-! Test cases to validate when dite over match constant propagation must NOT be applied. -/

-- ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
--   beqColor (if h : c then Color.red (f h x) else y) (Color.blue x) ===>
-- ∀ (c : Prop) (x y : Color) (f : c → Color → Color),
--    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--    (Blaster.dite' c (fun h : c => Color.red (f h x)) (fun _ : ¬ c => y))
--    (Color.blue x)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (_ : Unit) => True)
--    (fun (_ : Unit) => True)
--    (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "DIteOverMatchUnchanged_1" ]
  ∀ (c : Prop) (x y : Color) (f : c → Color → Color), [Decidable c] →
    beqColor (if h : c then Color.red (f h x) else y) (Color.blue x) ===>
  ∀ (c : Prop) (x y : Color) (f : c → Color → Color),
     beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
     (Blaster.dite' c (fun h : c => Color.red (f h x)) (fun _ : ¬ c => y))
     (Color.blue x)
     (fun (x : Color) (y : Color) => x = y)
     (fun (x : Color) (y : Color) => x = y)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)

-- ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--     beqColor (if h1 : c
--               then (if h2 : b then Color.red (g h2 x) else y)
--               else Color.blue (f h1 x)) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
--     beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--     (Blaster.dite' c
--       (fun _ : c => Blaster.dite' b (fun h2 : b => Color.red (g h2 x)) (fun _ : ¬ b => y))
--       (fun h1 : ¬ c => Color.blue (f h1 x)))
--     (Color.blue x)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (_ : Unit) => True)
--    (fun (_ : Unit) => True)
--    (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "DIteOverMatchUnchanged_2" ]
  ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
      beqColor (if h1 : c
                then (if h2 : b then Color.red (g h2 x) else y)
                else Color.blue (f h1 x)) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color) (f : ¬ c → Color → Color) (g : b → Color → Color),
      beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
      (Blaster.dite' c
        (fun _ : c => Blaster.dite' b (fun h2 : b => Color.red (g h2 x)) (fun _ : ¬ b => y))
        (fun h1 : ¬ c => Color.blue (f h1 x)))
      (Color.blue x)
     (fun (x : Color) (y : Color) => x = y)
     (fun (x : Color) (y : Color) => x = y)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)

-- ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
--   [Decidable b] → [Decidable c] →
--     beqColor (if h1 : c
--               then Color.blue (f h1 x)
--               else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x) ===>
-- ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
--     beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--     (Blaster.dite' c
--       (fun h1 : c => Color.blue (f h1 x))
--       (fun _ : ¬ c => Blaster.dite' b (fun h2 : b => Color.red (g h2 x)) (fun _ : ¬ b => y)))
--     (Color.blue x)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (_ : Unit) => True)
--    (fun (_ : Unit) => True)
--    (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "DIteOverMatchUnchanged_3" ]
  ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
    [Decidable b] → [Decidable c] →
      beqColor (if h1 : c
                then Color.blue (f h1 x)
                else (if h2 : b then Color.red (g h2 x) else y)) (Color.blue x) ===>
  ∀ (b c : Prop) (x y : Color) (f : c → Color → Color) (g : b → Color → Color),
      beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
      (Blaster.dite' c
        (fun h1 : c => Color.blue (f h1 x))
        (fun _ : ¬ c => Blaster.dite' b (fun h2 : b => Color.red (g h2 x)) (fun _ : ¬ b => y)))
      (Color.blue x)
     (fun (x : Color) (y : Color) => x = y)
     (fun (x : Color) (y : Color) => x = y)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)


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
--     beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--     (Blaster.dite' c
--       (fun _ : c =>
--          Blaster.dite' d
--           (fun _ : d => Color.transparent)
--           (fun h2 : ¬ d => Color.blue (g h2 x)))
--       (fun h1 : ¬ c =>
--          Blaster.dite' b
--            (fun h3 : b => Color.red (t h3 x))
--            (fun _ : ¬ b => (f h1 y))))
--     (Color.blue x)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (_ : Unit) => True)
--    (fun (_ : Unit) => True)
--    (fun (_ : Color) (_ : Color) => False)
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
      beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
      (Blaster.dite' c
        (fun _ : c =>
           Blaster.dite' d
            (fun _ : d => Color.transparent)
            (fun h2 : ¬ d => Color.blue (g h2 x)))
        (fun h1 : ¬ c =>
           Blaster.dite' b
             (fun h3 : b => Color.red (t h3 x))
             (fun _ : ¬ b => (f h1 y))))
      (Color.blue x)
     (fun (x : Color) (y : Color) => x = y)
     (fun (x : Color) (y : Color) => x = y)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)


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
--     beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--     (Blaster.dite' c
--      (fun _ : c =>
--        Blaster.dite' d
--          (fun _ : d => Color.transparent)
--          (fun h2 : ¬ d => Color.blue (g h2 x)))
--      (fun h1 : ¬ c =>
--        Blaster.dite' b
--          (fun h3 : b => Color.red (t h3 x))
--          (fun _ : ¬ b => (f h1 y))))
--     (Blaster.dite' b (fun h4 : b => Color.blue (t h4 x)) (fun _ : ¬ b => y))
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (x : Color) (y : Color) => x = y)
--    (fun (_ : Unit) => True)
--    (fun (_ : Unit) => True)
--    (fun (_ : Color) (_ : Color) => False)
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
      beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
      (Blaster.dite' c
       (fun _ : c =>
         Blaster.dite' d
           (fun _ : d => Color.transparent)
           (fun h2 : ¬ d => Color.blue (g h2 x)))
       (fun h1 : ¬ c =>
         Blaster.dite' b
           (fun h3 : b => Color.red (t h3 x))
           (fun _ : ¬ b => (f h1 y))))
      (Blaster.dite' b (fun h4 : b => Color.blue (t h4 x)) (fun _ : ¬ b => y))
     (fun (x : Color) (y : Color) => x = y)
     (fun (x : Color) (y : Color) => x = y)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)


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
--             (fun (_ : Unit) => false)
--             (fun (_ : Unit) => false)
--             (fun (_ : Unit) => false)
--             (fun (_ : Unit) => Color.black = x)
--             (fun (_ : Nat) => Color.transparent = x) )
#testOptimize [ "MatchOverMatch_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) (Color.blue x) ===>
  ∀ (n : Option Nat) (x : Color),
       ( toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
         (fun (_ : Unit) => False)
         (fun (_ : Unit) => False)
         (fun (_ : Unit) => False)
         (fun (_ : Unit) => Color.black = x)
         (fun (_ : Nat) => Color.transparent = x) )

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (Color.blue x) ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
--   ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
--      (fun (_ : Unit) => False)
--      (fun (_ : α) => Color.transparent = x) )
--      true = ( toColorTwo.match_1 (fun (_ : Option α) => Bool) n
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverMatch_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (Color.blue x) ===>
  ∀ (α : Type) (n : Option α) (x : Color),
      ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
        (fun (_ : Unit) => False)
        (fun (_ : α) => Color.transparent = x) )


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
--      (fun (_ : Unit) => False)
--      (fun (a : α) => true = beqColorPrim (ColorPrim.transparent a) x) )
-- NOTE: Test case to ensure that generic type are also properly handled
-- NOTE: Lean4 already applied structural equivalence between toColorThree.match_1 and toColorTwo.match_1
#testOptimize [ "MatchOverMatch_3" ]
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) (ColorPrim.blue x) ===>
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
    ( toColorTwo.match_1 (fun (_ : Option α) => Prop) n
      (fun (_ : Unit) => False)
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
--      (fun (_ : Unit) => False)
--      (fun (_ : Unit) => False)
--      (fun (_ : Unit) => False)
--      (fun (_ : Unit) => Color.black = x)
--      (fun (a : Nat) => Color.transparent = x ∧ a < 10) )
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that simplification rule can transitively detect
-- that all path reduce to constant values
-- NOTE: Can be reduced further with additional simplification rules
#testOptimize [ "MatchOverMatch_5" ] (norm-result: 1)
  ∀ (n : Option Nat) (x : Color),
    beqColor (toColorFour n) (Color.blue x) ===>
  ∀ (n : Option Nat) (x : Color),
     ( toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
      (fun (_ : Unit) => False)
      (fun (_ : Unit) => False)
      (fun (_ : Unit) => False)
      (fun (_ : Unit) => Color.black = x)
      (fun (a : Nat) => Color.transparent = x ∧ a < 10) )

def beqColorDegree : Color → Color → (Nat → Prop)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then True else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => True
| _, _ => λ _n => False

-- ∀ (n : Option Nat) (y : Nat) (x : Color),
--    beqColorDegree (toColorFour n) (Color.blue x) y ===>
-- ∀ (n : Option Nat) (y : Nat) (x : Color),
--   toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
--     (fun (_ : Unit) => False)
--     (fun (_ : Unit) => False)
--     (fun (_ : Unit) => False)
--     (fun (_ : Unit) =>
--       ¬ 0 = y →
--           beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop) Color.black x
--           (fun (x : Color) (y : Color) => x = y)
--           (fun (x : Color) (y : Color) => x = y)
--           (fun (_ : Unit) => True)
--           (fun (_ : Unit) => True)
--           (fun (_ : Color) (_ : Color) => False))
--     (fun (a : Nat) =>
--         a < 10 ∧
--         (¬ 0 = y →
--             beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop) Color.transparent x
--             (fun (x : Color) (y : Color) => x = y)
--             (fun (x : Color) (y : Color) => x = y)
--             (fun (_ : Unit) => True)
--             (fun (_ : Unit) => True)
--             (fun (_ : Color) (_ : Color) => False)))
-- NOTE: Test case to ensure that functions as rhs of match patterns are properly handled.
#testOptimize [ "MatchOverMatch_6" ] (norm-result: 1)
  ∀ (n : Option Nat) (y : Nat) (x : Color),
    beqColorDegree (toColorFour n) (Color.blue x) y ===>
  ∀ (n : Option Nat) (y : Nat) (x : Color),
    toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
      (fun (_ : Unit) => False)
      (fun (_ : Unit) => False)
      (fun (_ : Unit) => False)
      (fun (_ : Unit) =>
        ¬ 0 = y →
            beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop) Color.black x
            (fun (x : Color) (y : Color) => x = y)
            (fun (x : Color) (y : Color) => x = y)
            (fun (_ : Unit) => True)
            (fun (_ : Unit) => True)
            (fun (_ : Color) (_ : Color) => False))
      (fun (a : Nat) =>
          a < 10 ∧
          (¬ 0 = y →
              beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop) Color.transparent x
              (fun (x : Color) (y : Color) => x = y)
              (fun (x : Color) (y : Color) => x = y)
              (fun (_ : Unit) => True)
              (fun (_ : Unit) => True)
              (fun (_ : Color) (_ : Color) => False)))

/-! Test cases to validate when match over match constant propagation must NOT be applied. -/

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
-- ∀ (n : Option Nat) (x : Color),
--  beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--  ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--    (fun (_ : Unit) => .black)
--    (fun (_ : Unit) => .transparent)
--    (fun (_ : Unit) =>  .red .transparent)
--    (fun (_ : Unit) => .blue .black)
--    (fun (_ : Nat) => .blue .transparent) ) x
--  (fun (x : Color) (y : Color) => x = y)
--  (fun (x : Color) (y : Color) => x = y)
--  (fun (_ : Unit) => True)
--  (fun (_ : Unit) => True)
--  (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "MatchOverMatchUnchanged_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
  ∀ (n : Option Nat) (x : Color),
       beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
       ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
         (fun (_ : Unit) => .black)
         (fun (_ : Unit) => .transparent)
         (fun (_ : Unit) =>  .red .transparent)
         (fun (_ : Unit) => .blue .black)
         (fun (_ : Nat) => .blue .transparent) ) x
       (fun (x : Color) (y : Color) => x = y)
       (fun (x : Color) (y : Color) => x = y)
       (fun (_ : Unit) => True)
       (fun (_ : Unit) => True)
       (fun (_ : Color) (_ : Color) => False)


-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--   ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
--     (fun (_ : Unit) => .black)
--     (fun (_ : α) => .blue .transparent) ) x
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
#testOptimize [ "MatchOverMatchUnchanged_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
  ∀ (α : Type) (n : Option α) (x : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
    ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
      (fun (_ : Unit) => .black)
      (fun (_ : α) => .blue .transparent) ) x
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)

-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) x ===>
-- ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
--      true =
--      beqColorPrim
--      ( toColorTwo.match_1 (fun (_ : Option α) => ColorPrim α) n
--        (fun (_ : Unit) => .white)
--        (fun (a : α) => .blue (.transparent a) ) ) x
-- NOTE: Lean4 already applied structural equivalence between toColorThree.match_1 and toColorTwo.match_1
#testOptimize [ "MatchOverMatchUnchanged_3" ]
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] → beqColorPrim (toColorThree n) x ===>
  ∀ (α : Type) (n : Option α) (x : ColorPrim α), [BEq α] →
       true =
       beqColorPrim
       ( toColorTwo.match_1 (fun (_ : Option α) => ColorPrim α) n
         (fun (_ : Unit) => .white)
         (fun (a : α) => .blue (.transparent a) ) ) x

-- ∀ (n : Option Nat) (x : Color),
--   beqColor (toColorFour n) x ===>
-- ∀ (n : Option Nat) (x : Color),
--   beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
--   ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--     (fun (_ : Unit) => .black)
--     (fun (_ : Unit) => .transparent)
--     (fun (_ : Unit) => .red .transparent)
--     (fun (_ : Unit) => .blue .black)
--     (fun (a : Nat) =>
--       Blaster.dite' (a < 10)
--        (fun _ : a < 10 => .blue .transparent)
--        (fun  _ : ¬ a < 10 =>
--          Blaster.dite' (a < 100)
--            (fun _ :  a < 100 => .red .black)
--            (fun _ : ¬ a < 100 => .red .transparent ) ))) x
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (x : Color) (y : Color) => x = y)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
#testOptimize [ "MatchOverMatchUnchanged_4" ] (norm-result: 1)
  ∀ (n : Option Nat) (x : Color),
    beqColor (toColorFour n) x ===>
  ∀ (n : Option Nat) (x : Color),
    beqColor.match_1 (fun ( _ : Color) (_ : Color) => Prop)
    ( toColorOne.match_1 (fun (_ : Option Nat) => Color) n
      (fun (_ : Unit) => .black)
      (fun (_ : Unit) => .transparent)
      (fun (_ : Unit) => .red .transparent)
      (fun (_ : Unit) => .blue .black)
      (fun (a : Nat) =>
        Blaster.dite' (a < 10)
         (fun _ : a < 10 => .blue .transparent)
         (fun  _ : ¬ a < 10 =>
           Blaster.dite' (a < 100)
             (fun _ :  a < 100 => .red .black)
             (fun _ : ¬ a < 100 => .red .transparent ) ))) x
    (fun (x : Color) (y : Color) => x = y)
    (fun (x : Color) (y : Color) => x = y)
    (fun (_ : Unit) => True)
    (fun (_ : Unit) => True)
    (fun (_ : Color) (_ : Color) => False)

end Tests.ConstMatchProp



