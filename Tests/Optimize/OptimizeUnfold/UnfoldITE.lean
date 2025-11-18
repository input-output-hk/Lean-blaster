import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldITE

/-! ## Test objectives to validate unfolding `ite` expressions -/

/-! Test cases to validate unfolding of `ite` expressions only when reduced via rewriting. -/

-- ∀ (c : Bool) (p : Prop), if c then p else p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldIte_1" ] ∀ (c : Bool) (p : Prop), if c then p else p ===> ∀ (p : Prop), p

-- ∀ (c : Bool) (x y : Int), (if c then x else x) < y ===> ∀ (x y : Int), x < y
#testOptimize [ "UnfoldIte_2" ] ∀ (c : Bool) (x y : Int), (if c then x else x) < y ===>
                                ∀ (x y : Int), x < y

-- ∀ (p q : Prop), if True then p else q ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldIte_3" ] ∀ (p q : Prop), if True then p else q ===> ∀ (p : Prop), p

-- ∀ (x y z : Int), (if True then x else y) < z ===> ∀ (x z : Int), x < z
#testOptimize [ "UnfoldIte_4" ] ∀ (x y z : Int), (if True then x else y) < z ===>
                                ∀ (x z : Int), x < z

-- ∀ (p q : Prop), if False then p else q ===> ∀ (q : Prop), q
#testOptimize [ "UnfoldIte_5" ] ∀ (p q : Prop), if False then p else q ===> ∀ (q : Prop), q

-- ∀ (x y z : Int), (if False then x else y) < z ===> ∀ (y z : Int), y < z
#testOptimize [ "UnfoldIte_6" ] ∀ (x y z : Int), (if False then x else y) < z ===>
                                ∀ (y z : Int), y < z

-- ∀ (a b c : Bool), (if c then a else b) = true ===>
-- ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)
#testOptimize [ "UnfoldIte_7" ] ∀ (a b c : Bool), (if c then a else b) = true ===>
                                ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)

-- ∀ (c : Bool) (p q : Prop), if c then p else q ===> ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)
#testOptimize [ "UnfoldIte_8" ] ∀ (c : Bool) (p q : Prop), if c then p else q ===>
                                ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)


/-! Test cases to validate when `ite` expressions must not be unfolded -/

-- ∀ (c : Bool) (x y z : Int), (if c then x else y) < z ===>
-- ∀ (b c : Bool) (x y z : Int), (Solver.dite' (b = c) (fun _h : b = c => x) (fun _h : ¬ b = c => y)) < z
#testOptimize [ "IteNotUnfolded_1" ]
  ∀ (b c : Bool) (x y z : Int), (if b = c then x else y) < z ===>
  ∀ (b c : Bool) (x y z : Int), (Solver.dite' (b = c) (fun _h : b = c => x) (fun _h : ¬ b = c => y)) < z


-- ∀ (x y : Int), (if x = y then x else y) = y ===>
-- ∀ (x y : Int), y = Solver.dite' (x = y) (fun _h : x = y => x) (fun _h : ¬ x = y => y)
#testOptimize [ "IteNotUnfolded_2" ]
  ∀ (x y : Int), (if x = y then x else y) = y ===>
  ∀ (x y : Int), y = Solver.dite' (x = y) (fun _h : x = y => x) (fun _h : ¬ x = y => y)

-- ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < Solver.dite' (a = b) (fun _h : a = b => x) (fun _h : ¬ a = b => y)
#testOptimize [ "IteNotUnfolded_3" ]
  ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x ===>
  ∀ (a b : Bool) (x y : Int), x < Solver.dite' (a = b) (fun _h : a = b => x) (fun _h : ¬ a = b => y)

-- ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x ===>
-- ∀ (x y : Int) (c : Prop), x < Solver.dite' c (fun _h : c => x) (fun _h : ¬ c => y)
#testOptimize [ "IteNotUnfolded_4" ]
  ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x ===>
  ∀ (x y : Int) (c : Prop), x < Solver.dite' c (fun _h : c => x) (fun _h : ¬ c => y)


-- ∀ (α : Type) (x y : List α), [DecidableEq α] → (if x = y then x else y) = y ===>
-- ∀ (α : Type) (x y : List α), y = Solver.dite' (x = y) (fun _h : x = y => x) (fun _h : ¬ x = y => y)
#testOptimize [ "IteNotUnfolded_5" ]
  ∀ (α : Type) (x y : List α), [DecidableEq α] → (if x = y then x else y) = y ===>
  ∀ (α : Type) (x y : List α), y = Solver.dite' (x = y) (fun _h : x = y => x) (fun _h : ¬ x = y => y)

-- ∀ (p q r : Prop) (x y : Int), [Decidable p] → [Decidable q] → [Decidable r] →
--     (if p ∧ (q ∨ ¬ q) ∧ r then x else y) < x ===>
-- ∀ (p r : Prop) (x y : Int),
--   Solver.dite' (p ∧ r) (fun _h : p ∧ r => x) (fun _h : ¬ (p ∧ r) => y) < x
#testOptimize [ "IteNotUnfolded_6" ]
  ∀ (p q r : Prop) (x y : Int), [Decidable p] → [Decidable q] → [Decidable r] →
      (if p ∧ (q ∨ ¬ q) ∧ r then x else y) < x ===>
  ∀ (p r : Prop) (x y : Int),
    Solver.dite' (p ∧ r) (fun _h : p ∧ r => x) (fun _h : ¬ (p ∧ r) => y) < x

-- ∀ (p q r : Prop) (x y : Int), [Decidable p] → [Decidable q] → [Decidable r] →
--     (if p ∧ (q → r) ∧ r then x else y) < x ===>
-- ∀ (p r : Prop) (x y : Int),
--   Solver.dite' (p ∧ r) (fun _h : p ∧ r => x) (fun _h : ¬ (p ∧ r) => y) < x
#testOptimize [ "IteNotUnfolded_7" ]
  ∀ (p q r : Prop) (x y : Int), [Decidable p] → [Decidable q] → [Decidable r] →
      (if p ∧ (q → r) ∧ r then x else y) < x ===>
  ∀ (p r : Prop) (x y : Int),
      Solver.dite' (p ∧ r) (fun _h : p ∧ r => x) (fun _h : ¬ (p ∧ r) => y) < x

-- ∀ (p r : Prop) (x y : Int), [Decidable p] → [Decidable (∃ (q : Prop), q )] → [Decidable r] →
--     (if p ∧ (∃ (q : Prop), q ) ∧ r then x else y) < x ===>
-- ∀ (p r : Prop) (x y : Int),
--  Solver.dite'
--    (p ∧ r ∧ ∃ (q : Prop), q)
--    (fun _h : p ∧ r ∧ ∃ (q : Prop), q => x )
--    (fun _h : ¬ (p ∧ r ∧ ∃ (q : Prop), q) => y) < x
#testOptimize [ "IteNotUnfolded_8" ]
  ∀ (p r : Prop) (x y : Int), [Decidable p] → [Decidable (∃ (q : Prop), q )] → [Decidable r] →
      (if p ∧ (∃ (q : Prop), q ) ∧ r then x else y) < x ===>
  ∀ (p r : Prop) (x y : Int),
       Solver.dite'
         (p ∧ r ∧ ∃ (q : Prop), q)
         (fun _h : p ∧ r ∧ ∃ (q : Prop), q => x )
         (fun _h : ¬ (p ∧ r ∧ ∃ (q : Prop), q) => y) < x

-- ∀ (α : Type) (x y : List α), [LT α] → [DecidableLT (List α)] → (if x < y then x else y) = y ===>
-- ∀ (α : Type) (x y : List α), [LT α] →
--   y = Solver.dite'
--        (List.Lex (λ a b => LT.lt a b) x y)
--        (fun _h : (List.Lex (λ a b => LT.lt a b) x y) => x)
--        (fun _h : ¬ (List.Lex (λ a b => LT.lt a b) x y) => y)
#testOptimize [ "IteNotUnfolded_9" ]
 ∀ (α : Type) (x y : List α), [LT α] → [DecidableLT (List α)] → (if x < y then x else y) = y ===>
 ∀ (α : Type) (x y : List α), [LT α] →
   y = Solver.dite'
        (List.Lex (λ a b => LT.lt a b) x y)
        (fun _h : (List.Lex (λ a b => LT.lt a b) x y) => x)
        (fun _h : ¬ (List.Lex (λ a b => LT.lt a b) x y) => y)

-- ∀ (α : Type) (x y : α), [LT α] → [DecidableLT α] → (if x < y then x else y) = y ===>
-- ∀ (α : Type) (x y : α), [LT α] →
--   y = Solver.dite' (x < y) (fun _h : x < y => x) (fun _h : ¬ (x < y) => y)
#testOptimize [ "IteNotUnfolded_10" ]
 ∀ (α : Type) (x y : α), [LT α] → [DecidableLT α] → (if x < y then x else y) = y ===>
 ∀ (α : Type) (x y : α), [LT α] →
   y = Solver.dite' (x < y) (fun _h : x < y => x) (fun _h : ¬ (x < y) => y)


-- ∀ (α : Type) (x y : List α), [LT α] → [DecidableLT (List α)] → (if x < y then x else y) ≤ y ===>
-- ∀ (α : Type) (x y : List α), [LT α] →
--   ¬ List.Lex (λ a b => LT.lt a b) y
--     (Solver.dite'
--       (List.Lex (λ a b => LT.lt a b) x y)
--       (fun _h : List.Lex (λ a b => LT.lt a b) x y => x)
--       (fun _h : ¬ (List.Lex (λ a b => LT.lt a b) x y) => y))
#testOptimize [ "IteNotUnfolded_11" ]
 ∀ (α : Type) (x y : List α), [LT α] → [DecidableLT (List α)] → (if x < y then x else y) ≤ y ===>
 ∀ (α : Type) (x y : List α), [LT α] →
   ¬ List.Lex (λ a b => LT.lt a b) y
     (Solver.dite'
       (List.Lex (λ a b => LT.lt a b) x y)
       (fun _h : List.Lex (λ a b => LT.lt a b) x y => x)
       (fun _h : ¬ (List.Lex (λ a b => LT.lt a b) x y) => y))

end Tests.UnfoldITE
