import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstIteProp

/-! ## Test objectives to validate ite over constant match/ite propagation (see `constDITEPropagation?`).
    The propagation rule pushes `sif h : c then e1 else e2` within the alternatives (resp. branches) of `c`
    when `c` is a match (resp. ite) whose alternatives (resp. branches) all end with `True` or `False`,
    possibly through nested constant match/ite expressions (see `isCstIteMatch`). -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def isColored : Color → Prop
| .red _ => True
| .blue _ => True
| _ => False

def isColoredB : Color → Bool
| .red _ => true
| .blue _ => true
| _ => false

def isPrim : Color → Prop
| .red _ => True
| .transparent => False
| .blue _ => True
| .black => False

def isDarkB : Color → Bool
| .black => true
| .red _ => true
| _ => false

def isPrimB : Color → Bool
| .red _ => true
| .transparent => false
| .blue _ => true
| .black => false

/-! Test cases to validate when ite over constant match propagation must be applied. -/

-- ∀ (x : Color) (a b : Prop), if isColoredB x then a else b ===>
-- ∀ (x : Color) (a b : Prop),
--   match x with
--   | .red _ => a
--   | .blue _ => a
--   | _ => b
#testOptimize [ "IteOverCstMatch_1" ]
  ∀ (x : Color) (a b : Prop), if isColoredB x then a else b ===>
  ∀ (x : Color) (a b : Prop),
    match x with
    | .red _ => a
    | .blue _ => a
    | _ => b

-- ∀ (x : Color) (a b : Prop), [Decidable (isPrim x)] → if isPrim x then a else b ===>
-- ∀ (x : Color) (a b : Prop),
--   match x with
--   | .red _ => a
--   | .transparent => b
--   | .blue _ => a
--   | .black => b
#testOptimize [ "IteOverCstMatch_2" ]
  ∀ (x : Color) (a b : Prop), [Decidable (isPrim x)] → if isPrim x then a else b ===>
  ∀ (x : Color) (a b : Prop),
    match x with
    | .red _ => a
    | .transparent => b
    | .blue _ => a
    | .black => b

-- ∀ (x : Color) (a b : Prop), if !(isColoredB x) then a else b ===>
-- ∀ (x : Color) (a b : Prop),
--   match x with
--   | .red _ => b
--   | .blue _ => b
--   | _ => a
-- NOTE: Test case to ensure that the negated condition is first pushed within the match alternatives.
#testOptimize [ "IteOverCstMatch_3" ]
  ∀ (x : Color) (a b : Prop), if !(isColoredB x) then a else b ===>
  ∀ (x : Color) (a b : Prop),
    match x with
    | .red _ => b
    | .blue _ => b
    | _ => a

-- ∀ (x : Color) (a b : Prop), (if isColoredB x then a else b) ∧ (if isColoredB x then b else a) ===>
-- ∀ (x : Color) (a b : Prop),
--   (match x with
--    | .red _ => a
--    | .blue _ => a
--    | _ => b) ∧
--   (match x with
--    | .red _ => b
--    | .blue _ => b
--    | _ => a)
#testOptimize [ "IteOverCstMatch_4" ]
  ∀ (x : Color) (a b : Prop), (if isColoredB x then a else b) ∧ (if isColoredB x then b else a) ===>
  ∀ (x : Color) (a b : Prop),
    (match x with
     | .red _ => a
     | .blue _ => a
     | _ => b) ∧
    (match x with
     | .red _ => b
     | .blue _ => b
     | _ => a)

-- ∀ (x : Color) (n m : Nat), (if isColoredB x then 1 else n) = m ===>
-- ∀ (x : Color) (n m : Nat),
--   m = match x with
--       | .red _ => 1
--       | .blue _ => 1
--       | _ => n
-- NOTE: Test case to ensure that the rule also applies when the ite is not of type Prop.
#testOptimize [ "IteOverCstMatch_5" ] (norm-result: 1)
  ∀ (x : Color) (n m : Nat), (if isColoredB x then 1 else n) = m ===>
  ∀ (x : Color) (n m : Nat),
    m = match x with
        | .red _ => 1
        | .blue _ => 1
        | _ => n

-- ∀ (x : Color) (n m : Nat) (f g : Nat → Nat), (if isColoredB x then f else g) n = m ===>
-- ∀ (x : Color) (n m : Nat) (f g : Nat → Nat),
--   m = match x with
--       | .red _ => f n
--       | .blue _ => f n
--       | _ => g n
-- NOTE: Test case to ensure that extra arguments applied to the ite are pushed within the match alternatives.
#testOptimize [ "IteOverCstMatch_6" ]
  ∀ (x : Color) (n m : Nat) (f g : Nat → Nat), (if isColoredB x then f else g) n = m ===>
  ∀ (x : Color) (n m : Nat) (f g : Nat → Nat),
    m = match x with
        | .red _ => f n
        | .blue _ => f n
        | _ => g n

/-! Test cases to validate when dite over constant match propagation must be applied. -/

-- ∀ (x : Color) (a b : Prop) (f : isColored x → Prop) (g : ¬ isColored x → Prop), [Decidable (isColored x)] →
--   if h : isColored x then (f h ∨ True) ∧ a else (g h ∧ False) ∨ b ===>
-- ∀ (x : Color) (a b : Prop),
--   match x with
--   | .red _ => a
--   | .blue _ => a
--   | _ => b
-- NOTE: `h` is replaced by `True.intro` (resp. `not_false`) in the then (resp. else) branch.
#testOptimize [ "DIteOverCstMatch_1" ]
  ∀ (x : Color) (a b : Prop) (f : isColored x → Prop) (g : ¬ isColored x → Prop), [Decidable (isColored x)] →
    if h : isColored x then (f h ∨ True) ∧ a else (g h ∧ False) ∨ b ===>
  ∀ (x : Color) (a b : Prop),
    match x with
    | .red _ => a
    | .blue _ => a
    | _ => b

/-! Test cases to validate when ite over nested constant match/ite propagation must be applied. -/

def optColored : Option Color → Prop
| none => True
| some c => isColored c

def optColoredB : Option Color → Bool
| none => true
| some c => isColoredB c

def optSelB (d : Bool) : Option Color → Bool
| none => true
| some c => if d then isColoredB c else isDarkB c

-- ∀ (x : Option Color) (a b : Prop), if optColoredB x then a else b ===>
-- ∀ (x : Option Color) (a b : Prop),
--   match x with
--   | none => a
--   | some c =>
--     match c with
--     | .red _ => a
--     | .blue _ => a
--     | _ => b
-- NOTE: Test case to ensure that the ite is pushed down to the alternatives of the nested match.
#testOptimize [ "IteOverNestedCstMatch_1" ]
  ∀ (x : Option Color) (a b : Prop), if optColoredB x then a else b ===>
  ∀ (x : Option Color) (a b : Prop),
    match x with
    | none => a
    | some c =>
      match c with
      | .red _ => a
      | .blue _ => a
      | _ => b

-- ∀ (x : Option Color) (a b : Prop), [Decidable (optColored x)] → if optColored x then a else b ===>
-- ∀ (x : Option Color) (a b : Prop),
--   match x with
--   | none => a
--   | some c =>
--     match c with
--     | .red _ => a
--     | .blue _ => a
--     | _ => b
#testOptimize [ "IteOverNestedCstMatch_2" ]
  ∀ (x : Option Color) (a b : Prop), [Decidable (optColored x)] → if optColored x then a else b ===>
  ∀ (x : Option Color) (a b : Prop),
    match x with
    | none => a
    | some c =>
      match c with
      | .red _ => a
      | .blue _ => a
      | _ => b

-- ∀ (d : Bool) (x : Option Color) (a b : Prop), if optSelB d x then a else b ===>
-- ∀ (d : Bool) (x : Option Color) (a b : Prop),
--   match x with
--   | none => a
--   | some c =>
--     Blaster.dite' (true = d)
--       (λ _ => match c with
--               | .red _ => a
--               | .blue _ => a
--               | _ => b)
--       (λ _ => match c with
--               | .black => a
--               | .red _ => a
--               | _ => b)
-- NOTE: Test case to ensure that the ite is pushed down through a nested ite whose branches are constant matches.
#testOptimize [ "IteOverNestedCstMatch_3" ]
  ∀ (d : Bool) (x : Option Color) (a b : Prop), if optSelB d x then a else b ===>
  ∀ (d : Bool) (x : Option Color) (a b : Prop),
    match x with
    | none => a
    | some c =>
      Blaster.dite' (true = d)
        (λ _ => match c with
                | .red _ => a
                | .blue _ => a
                | _ => b)
        (λ _ => match c with
                | .black => a
                | .red _ => a
                | _ => b)

-- ∀ (d : Bool) (x : Option Color) (n m : Nat), (if optSelB d x then 1 else n) = m ===>
-- ∀ (d : Bool) (x : Option Color) (n m : Nat),
--   m = match x with
--       | none => 1
--       | some c =>
--         Blaster.dite' (true = d)
--           (λ _ => match c with
--                   | .red _ => 1
--                   | .blue _ => 1
--                   | _ => n)
--           (λ _ => match c with
--                   | .black => 1
--                   | .red _ => 1
--                   | _ => n)
-- NOTE: Test case to ensure that the type of the nested match/ite is updated to the ite type.
#testOptimize [ "IteOverNestedCstMatch_4" ] (norm-result: 1)
  ∀ (d : Bool) (x : Option Color) (n m : Nat), (if optSelB d x then 1 else n) = m ===>
  ∀ (d : Bool) (x : Option Color) (n m : Nat),
    m = match x with
        | none => 1
        | some c =>
          Blaster.dite' (true = d)
            (λ _ => match c with
                    | .red _ => 1
                    | .blue _ => 1
                    | _ => n)
            (λ _ => match c with
                    | .black => 1
                    | .red _ => 1
                    | _ => n)

/-! Test cases to validate when ite over constant match propagation must NOT be applied. -/

def isColoredEq (y : Color) : Color → Prop
| .red c => c = y
| .blue _ => True
| _ => False

def isColoredSizeB (n : Nat) : Color → Bool
| .red _ => n == 0
| .blue _ => true
| _ => false

def optColoredSizeB (n : Nat) : Option Color → Bool
| none => true
| some c => isColoredSizeB n c

def optFlagB (d : Bool) : Option Color → Bool
| none => d
| some _ => false

def isZeroB : Nat → Bool
| 0 => true
| _ => false

def optZeroB : Option Nat → Bool
| none => true
| some n => isZeroB n

-- ∀ (x y : Color) (a b : Prop), [Decidable (isColoredEq y x)] → if isColoredEq y x then a else b ===>
-- ∀ (x y : Color) (a b : Prop),
--   Blaster.dite'
--     (match x with
--      | .red c => y = c
--      | .blue _ => True
--      | _ => False)
--     (λ _ => a) (λ _ => b)
-- NOTE: `c = y` is not a constant.
#testOptimize [ "IteOverCstMatchUnchanged_1" ]
  ∀ (x y : Color) (a b : Prop), [Decidable (isColoredEq y x)] → if isColoredEq y x then a else b ===>
  ∀ (x y : Color) (a b : Prop),
    Blaster.dite'
      (match x with
       | .red c => y = c
       | .blue _ => True
       | _ => False)
      (λ _ => a) (λ _ => b)

-- ∀ (n : Nat) (x : Color) (a b : Prop), if isColoredSizeB n x then a else b ===>
-- ∀ (n : Nat) (x : Color) (a b : Prop),
--   Blaster.dite'
--     (match x with
--      | .red _ => 0 = n
--      | .blue _ => True
--      | _ => False)
--     (λ _ => a) (λ _ => b)
-- NOTE: `0 = n` is not a constant.
#testOptimize [ "IteOverCstMatchUnchanged_2" ] (norm-result: 1)
  ∀ (n : Nat) (x : Color) (a b : Prop), if isColoredSizeB n x then a else b ===>
  ∀ (n : Nat) (x : Color) (a b : Prop),
    Blaster.dite'
      (match x with
       | .red _ => 0 = n
       | .blue _ => True
       | _ => False)
      (λ _ => a) (λ _ => b)

-- ∀ (d : Bool) (x : Option Color) (a b : Prop), if optFlagB d x then a else b ===>
-- ∀ (d : Bool) (x : Option Color) (a b : Prop),
--   Blaster.dite'
--     (match x with
--      | none => true = d
--      | some _ => False)
--     (λ _ => a) (λ _ => b)
-- NOTE: `true = d` is not a constant.
#testOptimize [ "IteOverCstMatchUnchanged_3" ]
  ∀ (d : Bool) (x : Option Color) (a b : Prop), if optFlagB d x then a else b ===>
  ∀ (d : Bool) (x : Option Color) (a b : Prop),
    Blaster.dite'
      (match x with
       | none => true = d
       | some _ => False)
      (λ _ => a) (λ _ => b)

-- ∀ (n : Nat) (x : Option Color) (a b : Prop), if optColoredSizeB n x then a else b ===>
-- ∀ (n : Nat) (x : Option Color) (a b : Prop),
--   Blaster.dite'
--     (match x with
--      | none => True
--      | some c =>
--        match c with
--        | .red _ => 0 = n
--        | .blue _ => True
--        | _ => False)
--     (λ _ => a) (λ _ => b)
-- NOTE: The nested match is not a constant match.
#testOptimize [ "IteOverCstMatchUnchanged_4" ] (norm-result: 1)
  ∀ (n : Nat) (x : Option Color) (a b : Prop), if optColoredSizeB n x then a else b ===>
  ∀ (n : Nat) (x : Option Color) (a b : Prop),
    Blaster.dite'
      (match x with
       | none => True
       | some c =>
         match c with
         | .red _ => 0 = n
         | .blue _ => True
         | _ => False)
      (λ _ => a) (λ _ => b)

-- ∀ (x : Option Nat) (a b : Prop), if optZeroB x then a else b ===>
-- ∀ (x : Option Nat) (a b : Prop),
--   Blaster.dite'
--     (match x with
--      | none => True
--      | some n => 0 = n)
--     (λ _ => a) (λ _ => b)
-- NOTE: The nested constant match `isZeroB n` is first eliminated into the equality `0 = n`,
-- which is not a constant.
#testOptimize [ "IteOverCstMatchUnchanged_5" ] (norm-result: 1)
  ∀ (x : Option Nat) (a b : Prop), if optZeroB x then a else b ===>
  ∀ (x : Option Nat) (a b : Prop),
    Blaster.dite'
      (match x with
       | none => True
       | some n => 0 = n)
      (λ _ => a) (λ _ => b)

/-! Test cases to validate when ite over constant ite propagation must be applied. -/

-- ∀ (d : Bool) (x : Color) (a b : Prop), if (if d then isColoredB x else isDarkB x) then a else b ===>
-- ∀ (d : Bool) (x : Color) (a b : Prop),
--   Blaster.dite' (true = d)
--     (λ _ => match x with
--             | .red _ => a
--             | .blue _ => a
--             | _ => b)
--     (λ _ => match x with
--             | .black => a
--             | .red _ => a
--             | _ => b)
#testOptimize [ "IteOverCstIte_1" ]
  ∀ (d : Bool) (x : Color) (a b : Prop), if (if d then isColoredB x else isDarkB x) then a else b ===>
  ∀ (d : Bool) (x : Color) (a b : Prop),
    Blaster.dite' (true = d)
      (λ _ => match x with
              | .red _ => a
              | .blue _ => a
              | _ => b)
      (λ _ => match x with
              | .black => a
              | .red _ => a
              | _ => b)

-- ∀ (d : Prop) (x : Color) (a b : Prop), [Decidable d] → [Decidable (isColored x)] → [Decidable (isPrim x)] →
--   if (if d then isColored x else isPrim x) then a else b ===>
-- ∀ (d : Prop) (x : Color) (a b : Prop),
--   Blaster.dite' d
--     (λ _ => match x with
--             | .red _ => a
--             | .blue _ => a
--             | _ => b)
--     (λ _ => match x with
--             | .red _ => a
--             | .transparent => b
--             | .blue _ => a
--             | .black => b)
#testOptimize [ "IteOverCstIte_2" ]
  ∀ (d : Prop) (x : Color) (a b : Prop), [Decidable d] → [Decidable (isColored x)] → [Decidable (isPrim x)] →
    if (if d then isColored x else isPrim x) then a else b ===>
  ∀ (d : Prop) (x : Color) (a b : Prop),
    Blaster.dite' d
      (λ _ => match x with
              | .red _ => a
              | .blue _ => a
              | _ => b)
      (λ _ => match x with
              | .red _ => a
              | .transparent => b
              | .blue _ => a
              | .black => b)

-- ∀ (d e : Bool) (x : Color) (a b : Prop),
--   if (if d then (if e then isColoredB x else isDarkB x) else isPrimB x) then a else b ===>
-- ∀ (d e : Bool) (x : Color) (a b : Prop),
--   Blaster.dite' (true = d)
--     (λ _ => Blaster.dite' (true = e)
--              (λ _ => match x with
--                      | .red _ => a
--                      | .blue _ => a
--                      | _ => b)
--              (λ _ => match x with
--                      | .black => a
--                      | .red _ => a
--                      | _ => b))
--     (λ _ => match x with
--             | .red _ => a
--             | .transparent => b
--             | .blue _ => a
--             | .black => b)
-- NOTE: Test case to ensure that the ite is pushed down through nested constant ites.
#testOptimize [ "IteOverCstIte_3" ]
  ∀ (d e : Bool) (x : Color) (a b : Prop),
    if (if d then (if e then isColoredB x else isDarkB x) else isPrimB x) then a else b ===>
  ∀ (d e : Bool) (x : Color) (a b : Prop),
    Blaster.dite' (true = d)
      (λ _ => Blaster.dite' (true = e)
               (λ _ => match x with
                       | .red _ => a
                       | .blue _ => a
                       | _ => b)
               (λ _ => match x with
                       | .black => a
                       | .red _ => a
                       | _ => b))
      (λ _ => match x with
              | .red _ => a
              | .transparent => b
              | .blue _ => a
              | .black => b)

-- ∀ (d : Bool) (x : Color) (n m : Nat), (if (if d then isColoredB x else isDarkB x) then 1 else n) = m ===>
-- ∀ (d : Bool) (x : Color) (n m : Nat),
--   m = Blaster.dite' (true = d)
--         (λ _ => match x with
--                 | .red _ => 1
--                 | .blue _ => 1
--                 | _ => n)
--         (λ _ => match x with
--                 | .black => 1
--                 | .red _ => 1
--                 | _ => n)
-- NOTE: Test case to ensure that the type of the pushed ite/match is updated to the ite type.
#testOptimize [ "IteOverCstIte_4" ] (norm-result: 1)
  ∀ (d : Bool) (x : Color) (n m : Nat), (if (if d then isColoredB x else isDarkB x) then 1 else n) = m ===>
  ∀ (d : Bool) (x : Color) (n m : Nat),
    m = Blaster.dite' (true = d)
          (λ _ => match x with
                  | .red _ => 1
                  | .blue _ => 1
                  | _ => n)
          (λ _ => match x with
                  | .black => 1
                  | .red _ => 1
                  | _ => n)

-- ∀ (d : Bool) (x : Color) (f g : Nat → Nat) (n m : Nat),
--   (if (if d then isColoredB x else isDarkB x) then f else g) n = m ===>
-- ∀ (d : Bool) (x : Color) (f g : Nat → Nat) (n m : Nat),
--   m = Blaster.dite' (true = d)
--         (λ _ => match x with
--                 | .red _ => f n
--                 | .blue _ => f n
--                 | _ => g n)
--         (λ _ => match x with
--                 | .black => f n
--                 | .red _ => f n
--                 | _ => g n)
-- NOTE: Test case to ensure that extra arguments applied to the ite are pushed within the ite/match branches.
#testOptimize [ "IteOverCstIte_5" ]
  ∀ (d : Bool) (x : Color) (f g : Nat → Nat) (n m : Nat),
    (if (if d then isColoredB x else isDarkB x) then f else g) n = m ===>
  ∀ (d : Bool) (x : Color) (f g : Nat → Nat) (n m : Nat),
    m = Blaster.dite' (true = d)
          (λ _ => match x with
                  | .red _ => f n
                  | .blue _ => f n
                  | _ => g n)
          (λ _ => match x with
                  | .black => f n
                  | .red _ => f n
                  | _ => g n)

-- ∀ (d : Bool) (x : Option Color) (a b : Prop), if (if d then optColoredB x else optSelB d x) then a else b ===>
-- ∀ (d : Bool) (x : Option Color) (a b : Prop),
--   Blaster.dite' (true = d)
--     (λ _ => match x with
--             | none => a
--             | some c =>
--               match c with
--               | .red _ => a
--               | .blue _ => a
--               | _ => b)
--     (λ _ => match x with
--             | none => a
--             | some c =>
--               match c with
--               | .black => a
--               | .red _ => a
--               | _ => b)
-- NOTE: Test case to ensure that the ite is pushed down to nested constant matches within the ite branches.
-- NOTE: In the else branch, the nested `if d` of `optSelB` is reduced with hypothesis `false = d`.
#testOptimize [ "IteOverCstIte_6" ]
  ∀ (d : Bool) (x : Option Color) (a b : Prop), if (if d then optColoredB x else optSelB d x) then a else b ===>
  ∀ (d : Bool) (x : Option Color) (a b : Prop),
    Blaster.dite' (true = d)
      (λ _ => match x with
              | none => a
              | some c =>
                match c with
                | .red _ => a
                | .blue _ => a
                | _ => b)
      (λ _ => match x with
              | none => a
              | some c =>
                match c with
                | .black => a
                | .red _ => a
                | _ => b)

/-! Test cases to validate when dite over constant ite propagation must be applied. -/

-- ∀ (d : Prop) (x : Color) (a b : Prop), [Decidable d] → [Decidable (isColored x)] → [Decidable (isPrim x)] →
--   ∀ (f : (if d then isColored x else isPrim x) → Prop) (g : ¬ (if d then isColored x else isPrim x) → Prop),
--     if h : (if d then isColored x else isPrim x) then (f h ∨ True) ∧ a else (g h ∧ False) ∨ b ===>
-- ∀ (d : Prop) (x : Color) (a b : Prop),
--   Blaster.dite' d
--     (λ _ => match x with
--             | .red _ => a
--             | .blue _ => a
--             | _ => b)
--     (λ _ => match x with
--             | .red _ => a
--             | .transparent => b
--             | .blue _ => a
--             | .black => b)
-- NOTE: `h` is replaced by `True.intro` (resp. `not_false`) in the then (resp. else) branch.
#testOptimize [ "DIteOverCstIte_1" ]
  ∀ (d : Prop) (x : Color) (a b : Prop), [Decidable d] → [Decidable (isColored x)] → [Decidable (isPrim x)] →
    ∀ (f : (if d then isColored x else isPrim x) → Prop) (g : ¬ (if d then isColored x else isPrim x) → Prop),
      if h : (if d then isColored x else isPrim x) then (f h ∨ True) ∧ a else (g h ∧ False) ∨ b ===>
  ∀ (d : Prop) (x : Color) (a b : Prop),
    Blaster.dite' d
      (λ _ => match x with
              | .red _ => a
              | .blue _ => a
              | _ => b)
      (λ _ => match x with
              | .red _ => a
              | .transparent => b
              | .blue _ => a
              | .black => b)

/-! Test cases to validate when ite over constant ite propagation must NOT be applied. -/

-- ∀ (c d : Bool) (x : Color) (a b : Prop), if (if d then isColoredB x else c) then a else b ===>
-- ∀ (c d : Bool) (x : Color) (a b : Prop),
--   Blaster.dite'
--     (Blaster.dite' (true = d)
--       (λ _ => match x with
--               | .red _ => True
--               | .blue _ => True
--               | _ => False)
--       (λ _ => true = c))
--     (λ _ => a) (λ _ => b)
-- NOTE: `true = c` is not a constant.
#testOptimize [ "IteOverCstIteUnchanged_1" ]
  ∀ (c d : Bool) (x : Color) (a b : Prop), if (if d then isColoredB x else c) then a else b ===>
  ∀ (c d : Bool) (x : Color) (a b : Prop),
    Blaster.dite'
      (Blaster.dite' (true = d)
        (λ _ => match x with
                | .red _ => True
                | .blue _ => True
                | _ => False)
        (λ _ => true = c))
      (λ _ => a) (λ _ => b)

-- ∀ (d : Bool) (x : Color) (a b : Prop), if (if d then true else isColoredB x) then a else b ===>
-- ∀ (d : Bool) (x : Color) (a b : Prop),
--   Blaster.dite'
--     (false = d → match x with
--                  | .red _ => True
--                  | .blue _ => True
--                  | _ => False)
--     (λ _ => a) (λ _ => b)
-- NOTE: The ite condition `if d then True else isColoredB x` is first simplified into an implication
-- (see `iteSimp?`), which is not a constant.
#testOptimize [ "IteOverCstIteUnchanged_2" ]
  ∀ (d : Bool) (x : Color) (a b : Prop), if (if d then true else isColoredB x) then a else b ===>
  ∀ (d : Bool) (x : Color) (a b : Prop),
    Blaster.dite'
      (false = d → match x with
                   | .red _ => True
                   | .blue _ => True
                   | _ => False)
      (λ _ => a) (λ _ => b)

end Tests.ConstIteProp
