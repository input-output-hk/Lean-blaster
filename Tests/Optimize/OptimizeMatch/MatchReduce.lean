import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.MatchReduce

/-! ## Test objectives to validate choice reduction on match expressions. -/

def discrAbstractOne (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [], _ => false
  | _, _ => true

/-! Test cases to validate when choice reduction must be applied on match expression. -/

-- ∀ (α : Type), discrAbstractOne ([] : List α) none = true ===> True
#testOptimize [ "MatchReduce_1" ] ∀ (α : Type), discrAbstractOne ([] : List α) none = true ===> True

-- ∀ (α : Type) (y : α), discrAbstractOne ([] : List α) (some y) = false ===> True
#testOptimize [ "MatchReduce_2" ] ∀ (α : Type) (y : α), discrAbstractOne ([] : List α) (some y) = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] none = false ===> True
#testOptimize [ "MatchReduce_3" ] ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] none = false ===> True

-- ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] (some z) = true ===> True
#testOptimize [ "MatchReduce_4" ] ∀ (α : Type) (x y z : α), discrAbstractOne [x, y , z] (some z) = true ===> True


def namedPatternNatOne (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | Nat.zero, _ => x
 | _, Nat.zero => y + 1
 | Nat.succ Nat.zero, _ => y + x
 | _, Nat.succ Nat.zero => x + y
 | r@(Nat.succ (Nat.succ n1)), Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ ((Nat.succ n2))))) => (r + n1) * n2 * p * q
 | r@(Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ n)))), z => n + p + q + r + z
 | q@(Nat.succ (Nat.succ n)), _ => q * n * 6

-- ∀ (n1 n2 : Nat),
--  namedPatternNatOne (Nat.succ (Nat.succ n1)) (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2)))))) =
--  (((n1 + 2) + n1) * n2) * (n2 + 3) * (n2 + 4) ===> True
#testOptimize [ "MatchReduce_5" ]
  ∀ (n1 n2 : Nat),
     namedPatternNatOne (Nat.succ (Nat.succ n1)) (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2)))))) =
     (((n1 + 2) + n1) * n2) * (n2 + 3) * (n2 + 4) ===> True

-- ∀ (n1 n2 : Nat),
--    namedPatternNatOne (n1 + 2) (n2 + 5) =
--    (((n1 + 2) + n1) * n2) * (n2 + 3) * (n2 + 4) ===> True
#testOptimize [ "MatchReduce_6" ]
  ∀ (n1 n2 : Nat),
     namedPatternNatOne (n1 + 2) (n2 + 5) =
     (((n1 + 2) + n1) * n2) * (n2 + 3) * (n2 + 4) ===> True

def namedPatternIntOne (x : Int) (y : Int) : Nat :=
 match x, y with
 | Int.ofNat p@Nat.zero, _ => p
 | _, Int.ofNat p@Nat.zero => p + 1
 | Int.ofNat p@(Nat.succ Nat.zero), _ => Int.toNat y + (p + Int.toNat x)
 | _, Int.ofNat (Nat.succ Nat.zero) => Int.toNat x + 3
 | r@(Int.ofNat (Nat.succ (Nat.succ n1))), Int.ofNat (Nat.succ (Nat.succ q@(Nat.succ p@(Nat.succ ((Nat.succ n2)))))) =>
     ((Int.toNat r) + n1) * n2 * p * q
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), z => n + Int.toNat z
 | Int.negSucc Nat.zero, _ => 4
 | _, Int.negSucc Nat.zero => 5
 | Int.negSucc p@(Nat.succ q@(Nat.succ Nat.zero)), _ => 6 * p * q * Int.toNat (Int.neg x)
 | _, q@(Int.negSucc p@(Nat.succ Nat.zero)) => 7 * p * Int.toNat (Int.neg q)
 | Int.negSucc q@(Nat.succ (Nat.succ p@(Nat.succ (Nat.succ n1)))), Int.ofNat (Nat.succ n2) => n1 + p + q + n2
 | _, Int.negSucc (Nat.succ q@(Nat.succ p@(Nat.succ r@(Nat.succ ((Nat.succ n)))))) => n + p + q + r + 2
 | p@(Int.ofNat (Nat.succ (Nat.succ n))), _ => Int.toNat p * n * 6
 | _, Int.negSucc (Nat.succ (Nat.succ n)) => n * 7
 | Int.negSucc (Nat.succ n), _ => n * 8

-- ∀ (n1 n2 : Nat),
--    namedPatternIntOne
--     (Int.ofNat (Nat.succ (Nat.succ n1)))
--     (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2))))))) =
--     ((n1 + 2) + n1) * n2 * (n2 + 2)  * (n2 + 3) ===> True
#testOptimize [ "MatchReduce_7" ]
  ∀ (n1 n2 : Nat),
     namedPatternIntOne
      (Int.ofNat (Nat.succ (Nat.succ n1)))
      (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2))))))) =
      ((n1 + 2) + n1) * n2 * (n2 + 2)  * (n2 + 3) ===> True

-- ∀ (n1 n2 : Nat),
--    namedPatternIntOne (Int.ofNat (n1 + 2)) (Int.ofNat (n2 + 5)) =
--     ((n1 + 2) + n1) * n2 * (n2 + 2)  * (n2 + 3) ===> True
#testOptimize [ "MatchReduce_8" ]
  ∀ (n1 n2 : Nat),
     namedPatternIntOne (Int.ofNat (n1 + 2)) (Int.ofNat (n2 + 5)) =
      ((n1 + 2) + n1) * n2 * (n2 + 2)  * (n2 + 3) ===> True

-- ∀ (n1 : Nat),
--    namedPatternIntOne
--      (Int.negSucc (Nat.succ (Nat.succ (Nat.succ (Nat.succ n1))))) 10 =
--    9 + ((n1 + (n1 + 2)) + (n1 + 4)) ===> True
#testOptimize [ "MatchReduce_9" ]
  ∀ (n1 : Nat),
     namedPatternIntOne
       (Int.negSucc (Nat.succ (Nat.succ (Nat.succ (Nat.succ n1))))) 10 =
     9 + ((n1 + (n1 + 2)) + (n1 + 4)) ===> True

-- ∀ (n1 : Nat),
--    namedPatternIntOne (- Int.ofNat (n1 + 5)) 6 =
--    5 + ((n1 + (n1 + 2)) + (n1 + 4)) ===> True
#testOptimize [ "MatchReduce_10" ]
  ∀ (n1 : Nat),
     namedPatternIntOne (- Int.ofNat (n1 + 5)) 6 =
     5 + ((n1 + (n1 + 2)) + (n1 + 4)) ===> True

def namedPatternList (x : List Int) (y : List Nat) : Nat :=
 match x, y with
 | [], [] => 0
 | [_], [_] => 1
 | _ :: q@(_ :: r@([_, _])), _ :: p@([_, n]) => (2 + List.length p + List.length q - List.length r) * n
 | [_], p@(_ :: q@([_, _])) => 1 + List.length p + List.length q
 | s, t => List.length s + List.length t + 8

-- ∀ (x1 x2 x3 : Int) (y1 y2 y3 : Nat), namedPatternList [x1, x2, x3] [y1, y2, y3] = 6 ===> True
#testOptimize [ "MatchReduce_11" ]
  ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 : Nat), namedPatternList [x1, x2, x3, x4] [y1, y2, y3] = y3 * 5 ===> True

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def beqColor : Color → Color → Bool
| .red x, .red y
| .blue x, .blue y => beqColor x y
| .transparent, .transparent
| .black, .black => true
| _, _ => false

def beqColorDegree : Color → Color → (Nat → Bool)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then true else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => true
| _, _ => λ _n => false


-- ∀ (x y : Color) (n : Nat),
--   beqColorDegree (Color.blue x) (Color.blue y) n =
--     if n == 0 then true else beqColor x y ===> True
-- NOTE: Test case considering match expression returning function and applied to extra arguments.
#testOptimize [ "MatchReduce_12" ]
  ∀ (x y : Color) (n : Nat),
    beqColorDegree (Color.blue x) (Color.blue y) n =
      if n == 0 then true else beqColor x y ===> True

def isSomeRed (x : Option Color) : Option Color :=
  match x with
  | some (Color.red y) => some y
  | _  => none

variable (x : Color)
-- isSomeRed (some (.red x)) ===> some x
#testOptimize [ "MatchReduce_13" ] isSomeRed (some (.red x)) ===> some x


def isBlue (x : Color) : Prop :=
  match x with
  | Color.blue _ => True
  | _  => False

-- isBlue (.red x) ===> False
#testOptimize [ "MatchReduce_14" ] isBlue (.red x) ===> False


def isRed (x : Color) : Prop :=
  match x with
  | .transparent
  | .blue _
  | .black => False
  | _  => True

-- isRed (.red x) ===> True
#testOptimize [ "MatchReduce_15" ] isRed (.red x) ===> True

def filterStringOne (s : String) : Nat :=
  match s with
  | "a" => 1
  | "bb" => 2
  | "ccc" => 3
  | "dddd" => 4
  | _ => 5

variable (c1 c2 c3 : Char)

variable (c4 c5 : Char)
-- filterString (String.mk [c1, c2, c3, c4, c5])  ===> 5
#testOptimize [ "MatchReduce_16" ] (norm-result: 1)
  filterStringOne (String.mk [c1, c2, c3, c4, c5])  ===> 5

def filterStringTwo (s : String) : Nat :=
  match s with
  | String.mk [s1, s2, s3] => s1.toNat + s2.toNat + s3.toNat
  | String.mk [s1, s2] => s1.toNat + s2.toNat
  | String.mk [s1, s2, s3, s4] => s1.toNat + s2.toNat + s3.toNat + s4.toNat
  | _ => 5

-- filterStringTwo "abc" ===> 294
#testOptimize [ "MatchReduce_17" ] (norm-result: 1)
  filterStringTwo "abc" ===> 294

-- filterStringTwo "abcd" ===> 394
#testOptimize [ "MatchReduce_18" ] (norm-result: 1)
  filterStringTwo "abcd" ===> 394

def filterStringThree (s : String) : Nat :=
  match s with
  | String.mk x =>
       match x with
       | [s1] => s1.toNat
       | [s1, s2, s3] => s1.toNat + s2.toNat + s3.toNat
       | _ => 200

-- filterStringThree "" ===> 200
#testOptimize [ "MatchReduce_19" ] (norm-result: 1)
  filterStringThree "" ===> 200

-- filterStringThree "a" ===> 97
#testOptimize [ "MatchReduce_20" ] (norm-result: 1)
  filterStringThree "a" ===> 97

-- filterStringThree "abc" ===> 294
#testOptimize [ "MatchReduce_21" ] (norm-result: 1)
  filterStringThree "abc" ===> 294

-- filterStringThree (String.mk [c1, c2, c3]) = Nat.add (Nat.add c1.toNat c2.toNat) c3.toNat ===> True
#testOptimize [ "MatchReduce_22" ] (norm-result: 1)
  filterStringThree (String.mk [c1, c2, c3]) = Nat.add (Nat.add c1.toNat c2.toNat) c3.toNat ===> True


def heqMatchOne (x : List Int) (y : List Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat) : Nat :=
 match heq1 : x, heq2 : y with
 | [], [] => 0
 | [_], [_] => 1
 | _ :: q@(_ :: r@([_, _])), _ :: p@([_, n]) => (2 + List.length p + f x (by simp [heq1]) + g y (by simp [heq2]) + List.length q - List.length r) * n
 | [_], p@(_ :: q@([_, _])) => 1 + List.length p + List.length q + f x (by simp [heq1]) + g y (by simp [heq2])
 | s, t => List.length s + List.length t + 8

-- ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 nb : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
--    heqMatchOne [x1, x2, x3, x4] [y1, y2, y3] f g > nb ===>
-- ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 nb : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
--    nb < Nat.mul y3
--         (Nat.add 1
--           (Nat.add (g [y1, y2, y3] (Tests.MatchReduce.heqMatchOne._proof_2 [y1, y2, y3] y1 y2 y3 (by rfl)))
--           (Nat.add 4 (f [x1, x2, x3, x4] (Tests.MatchReduce.heqMatchOne._proof_1 [x1, x2, x3, x4] x1 x2 x3 x4 (by rfl))))))
-- Test cases validating heq in match
#testOptimize [ "MatchReduce_23" ] (norm-result: 1)
  ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 nb : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
     heqMatchOne [x1, x2, x3, x4] [y1, y2, y3] f g > nb ===>
  ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 nb : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
     nb < Nat.mul y3
          (Nat.add 1
            (Nat.add (g [y1, y2, y3] (Tests.MatchReduce.heqMatchOne._proof_2 [y1, y2, y3] y1 y2 y3 (by rfl)))
            (Nat.add 4 (f [x1, x2, x3, x4] (Tests.MatchReduce.heqMatchOne._proof_1 [x1, x2, x3, x4] x1 x2 x3 x4 (by rfl))))))

-- ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
--    heqMatchOne [x1, x2, x3, x4] [y1, y2, y3] f g =
--    y3 * (1 + (g [y1, y2, y3] (Tests.MatchReduce.heqMatchOne._proof_2 [y1, y2, y3] y1 y2 y3 (by rfl)) +
--         (4 + f [x1, x2, x3, x4] (Tests.MatchReduce.heqMatchOne._proof_1 [x1, x2, x3, x4] x1 x2 x3 x4 (by rfl))))) ===> True
-- Test cases validating heq in match while checking for structural equality
#testOptimize [ "MatchReduce_24" ]
  ∀ (x1 x2 x3 x4 : Int) (y1 y2 y3 : Nat) (f : (x : List Int) → ¬ [] = x → Nat) (g : (y : List Nat) → ¬ [] = y → Nat),
     heqMatchOne [x1, x2, x3, x4] [y1, y2, y3] f g =
     y3 * (1 + (g [y1, y2, y3] (Tests.MatchReduce.heqMatchOne._proof_2 [y1, y2, y3] y1 y2 y3 (by rfl)) +
          (4 + f [x1, x2, x3, x4] (Tests.MatchReduce.heqMatchOne._proof_1 [x1, x2, x3, x4] x1 x2 x3 x4 (by rfl))))) ===> True

def heqMatchTwo (x : List Int) (y : Nat) (g : (y : Nat) → y = 0 → Nat) : Nat :=
 match x, heq : y with
 | [], _ => 0
 | [_], _ => 1
 | _ :: q@(_ :: [_, _]), Nat.zero => g y heq + List.length q
 | [_, _], Nat.succ (Nat.succ n) => n
 | s, t => List.length s + t + 8

-- ∀ (x1 x2 x3 x4 : Int) (nb : Nat) (g : (y : Nat) → y = 0 → Nat),
--    heqMatchTwo [x1, x2, x3, x4] 0 g > nb ===>
-- ∀ (nb : Nat) (g : (y : Nat) → 0 = y → Nat),
--    nb < Nat.add 3 (g 0 (by rfl))
#testOptimize [ "MatchReduce_25" ] (norm-result: 1)
  ∀ (x1 x2 x3 x4 : Int) (nb : Nat) (g : (y : Nat) → y = 0 → Nat),
     heqMatchTwo [x1, x2, x3, x4] 0 g > nb ===>
  ∀ (nb : Nat) (g : (y : Nat) → 0 = y → Nat),
     nb < Nat.add 3 (g 0 (by rfl))

/-! Test cases to validate when choice reduction must NOT be applied on match expression. -/

-- ∀ (α : Type) (x : List α), discrAbstractOne x none ===>
-- ∀ (α : Type) (x : List α), [] = x
-- NOTE: Match is normalized to ite since we are no more constrainted
-- with Decidable instance on Eq.
#testOptimize [ "MatchReduceUnchanged_1" ]
  ∀ (α : Type) (x : List α), discrAbstractOne x none ===>
  ∀ (α : Type) (x : List α), [] = x

-- ∀ (α : Type) (y : Option α), discrAbstractOne ([] : List α) y ===>
-- ∀ (α : Type) (y : Option α), none = y
-- NOTE: Match is normalized to ite since we are no more constrainted
-- with Decidable instance on Eq.
#testOptimize [ "MatchReduceUnchanged_2" ]
  ∀ (α : Type) (y : Option α), discrAbstractOne ([] : List α) y ===>
  ∀ (α : Type) (y : Option α), none = y


def discrAbstractTwo (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], some _ => true
  | _, none => false
  | _, _ => true

-- ∀ (α : Type) (x : List α), discrAbstractTwo x none ===>
-- ∀ (α : Type) (x : List α),
--  ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
--    (fun (_ : α) => True)
--    (fun (_ : List α) => False)
--    (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_3" ]
  ∀ (α : Type) (x : List α), discrAbstractTwo x none ===>
  ∀ (α : Type) (x : List α),
    ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) x none
      (fun (_ : α) => True)
      (fun (_ : List α) => False)
      (fun (_ : List α) (_ : Option α) => True) )

-- ∀ (α : Type) (y : Option α), discrAbstractTwo ([] : List α) y ===>
-- ∀ (α : Type) (y : Option α),
--  ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
--    (fun (_ : α) => True)
--    (fun (_ : List α) => False)
--    (fun (_ : List α) (_ : Option α) => True) )
#testOptimize [ "MatchReduceUnchanged_4" ]
  ∀ (α : Type) (y : Option α), discrAbstractTwo ([] : List α) y ===>
  ∀ (α : Type) (y : Option α),
    ( discrAbstractTwo.match_1 (fun (_ : List α) (_ : Option α) => Prop) ([] : List α) y
      (fun (_ : α) => True)
      (fun (_ : List α) => False)
      (fun (_ : List α) (_ : Option α) => True) )

def namedPatternNatTwo (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | Nat.zero, _ => x
 | _, Nat.zero => y + 1
 | Nat.succ Nat.zero, _ => y + x
 | _, Nat.succ Nat.zero => x + y
 | r@(Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ n)))), z => n + p + q + r + z
 | r@(Nat.succ (Nat.succ n1)), Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ ((Nat.succ n2))))) => (r + n1) * n2 * p * q
 | q@(Nat.succ (Nat.succ n)), _ => q * n * 6

variable (n : Nat)
-- namedPatternNatOne n (Nat.succ Nat.zero) ===>
-- Blaster.dite' (0 = n)
--   (fun _ => 0)
--   (fun _ =>
--     Blaster.dite' (1 = n) (fun _ => 2) (fun _ => Nat.add 1 n))
-- NOTE: normalization via match to ite rule
#testOptimize [ "MatchReduceUnchanged_5" ] (norm-result: 1)
  namedPatternNatOne n (Nat.succ Nat.zero) ===>
    Blaster.dite' (0 = n)
      (fun _ => 0)
      (fun _ =>
        Blaster.dite' (1 = n) (fun _ => 2) (fun _ => Nat.add 1 n))


variable (w : Int)
-- namedPatternIntOne w (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ Nat.zero))))))) ===>
-- Blaster.dite' (Int.ofNat 0 = w)
-- (fun _ => 0)
-- (fun _ =>
--     Blaster.dite' (Int.ofNat 1 = w)
--     (fun _ => 7)
--     (fun _ =>
--       Blaster.dite' (w < Int.ofNat 2)
--         (fun _ =>
--           Blaster.dite' (w < Int.ofNat 4)
--             (fun _ =>
--               Blaster.dite' (Int.negSucc 0 = w)
--               (fun _ => 4)
--               (fun _ =>
--                 Blaster.dite' (Int.negSucc 2 = w)
--                 (fun _ => 36)
--                 (fun _ =>
--                   Blaster.dite' (Int.negSucc 4 < w)
--                   (fun _ => Nat.mul 8 (w.neg.toNat.sub 2))
--                   (fun _ => Nat.add 4 (((w.neg.toNat.sub 3).add (w.neg.toNat.sub 5)).add (w.neg.toNat.sub 1)))
--                 )
--               )
--             )
--             (fun _ => Nat.add 5 (w.toNat.sub 4))
--          )
--         (fun _ => 0)
--      )
-- )
-- NOTE: normalization via match to ite rule
#testOptimize [ "MatchReduceUnchanged_6" ] (norm-result: 1)
  namedPatternIntOne w (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ Nat.zero))))))) ===>
  Blaster.dite' (Int.ofNat 0 = w)
  (fun _ => 0)
  (fun _ =>
      Blaster.dite' (Int.ofNat 1 = w)
      (fun _ => 7)
      (fun _ =>
        Blaster.dite' (w < Int.ofNat 2)
          (fun _ =>
            Blaster.dite' (w < Int.ofNat 4)
              (fun _ =>
                Blaster.dite' (Int.negSucc 0 = w)
                (fun _ => 4)
                (fun _ =>
                  Blaster.dite' (Int.negSucc 2 = w)
                  (fun _ => 36)
                  (fun _ =>
                    Blaster.dite' (Int.negSucc 4 < w)
                    (fun _ => Nat.mul 8 (w.neg.toNat.sub 2))
                    (fun _ => Nat.add 4 (((w.neg.toNat.sub 3).add (w.neg.toNat.sub 5)).add (w.neg.toNat.sub 1)))
                  )
                )
              )
              (fun _ => Nat.add 5 (w.toNat.sub 4))
           )
          (fun _ => 0)
       )
  )

variable (sx : Option Color)
-- isSomeRed sx ===>
--   match sx with
--   | some (.red y) => some y
--   | _ => none
#testOptimize [ "MatchReduceUnchanged_7" ]
  isSomeRed sx ===>
    match sx with
    | some (.red y) => some y
    | _ => none

-- isSomeRed (some x) ===>
--   match (some x) with
--   | some (.red y) => some y
--   | _ => none
#testOptimize [ "MatchReduceUnchanged_8" ]
  isSomeRed (some x) ===>
    match (some x) with
    | some (.red y) => some y
    | _ => none

def isSomeRedBlue (x : Option Color) (y : Color) : Prop :=
  match x, y with
  | some (.red _), .blue _ => True
  | _, _ => False

-- isSomeRedBlue (some x) (.blue x) ===>
--   match some x, (Color.blue x) with
--   | some (.red _), .blue _ => True
--   | _, _ => False
#testOptimize [ "MatchReduceUnchanged_9" ]
  isSomeRedBlue (some x) (.blue x) ===>
    match some x, (Color.blue x) with
    | some (.red _), .blue _ => True
    | _, _ => False


def isSomeColorAndBlue (x : Option Color) (y : Color) : Prop :=
  match x, y with
  | some (.red _), .blue _ => True
  | some (_), .blue _ => True
  | _, _ => False

-- isSomeColorAndBlue (some x) (.blue x) ===>
--   match some x, (Color.blue x) with
--   | some (.red _), .blue _ => True
--   | some (_), .blue _ => True
--   | _, _ => False
#testOptimize [ "MatchReduceUnchanged_10" ]
  isSomeColorAndBlue (some x) (.blue x) ===>
    match some x, (Color.blue x) with
    | some (.red _), .blue _ => True
    | some (_), .blue _ => True
    | _, _ => False

def filterNat (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | 2 => 3
  | 4 => 8
  | y => 3 * y

-- filterNat n ===>
--   Blaster.dite' (0 = n) (fun _ => 1)
--   (fun _ =>
--     Blaster.dite' (2 = n) (fun _ => 3)
--     (fun _ => Blaster.dite' (4 = n) (fun _ => 8) (fun _ => Nat.mul 3 n)))
-- NOTE: normalized via match to ite rule
#testOptimize [ "MatchReduceUnchanged_11" ] (norm-result: 1)
  filterNat n ===>
    Blaster.dite' (0 = n) (fun _ => 1)
    (fun _ =>
      Blaster.dite' (2 = n) (fun _ => 3)
      (fun _ => Blaster.dite' (4 = n) (fun _ => 8) (fun _ => Nat.mul 3 n)))

-- filterNat (Nat.succ (Nat.succ (Nat.succ n))) ===>
--   Blaster.dite' (1 = n) (fun _ => 8) (fun _ => Nat.mul 3 (Nat.add 3 n))
-- NOTE: Normalized and simplified via match to ite rule
#testOptimize [ "MatchReduceUnchanged_12" ] (norm-result: 1)
  filterNat (Nat.succ (Nat.succ (Nat.succ n))) ===>
    Blaster.dite' (1 = n) (fun _ => 8) (fun _ => Nat.mul 3 (Nat.add 3 n))

variable (s : String)
-- filterString s ===>
--  Blaster.dite' ("a" = s) (fun _ => 1)
--   (fun _ =>
--     Blaster.dite' ("bb" = s) (fun _ => 2)
--     (fun _ => Blaster.dite' ("ccc" = s)
--               (fun _ => 3)
--               (fun _ => Blaster.dite' ("dddd" = s ) (fun _ => 4) (fun _ => 5))))
#testOptimize [ "MatchReduceUnchanged_13" ] (norm-result: 1)
  filterStringOne s ===>
   Blaster.dite' ("a" = s) (fun _ => 1)
    (fun _ =>
      Blaster.dite' ("bb" = s) (fun _ => 2)
      (fun _ => Blaster.dite' ("ccc" = s)
                (fun _ => 3)
                (fun _ => Blaster.dite' ("dddd" = s ) (fun _ => 4) (fun _ => 5))))

-- filterStringOne (String.mk [c1, c2, c3])  ===>
--  Blaster.dite' ("a" = String.mk [c1, c2, c3]) (fun _ => 1) fun _ =>
--     Blaster.dite' ("bb" = String.mk [c1, c2, c3]) (fun _ => 2) fun _ =>
--       Blaster.dite' ("ccc" = String.mk [c1, c2, c3]) (fun _ => 3) fun _ =>
--         Blaster.dite' ("dddd" = String.mk [c1, c2, c3]) (fun _ => 4) fun _ => 5
-- NOTE: Normalized and simplified via match to ite rule
-- NOTE: Can be reduced to
--     Blaster.dite' ("ccc" = String.mk [c1, c2, c3]) (fun _ => 3) (fun _ => 5)
-- with const equality rule.
#testOptimize [ "MatchReduceUnchanged_14" ] (norm-result: 1)
  filterStringOne (String.mk [c1, c2, c3])  ===>
   Blaster.dite' ("a" = String.mk [c1, c2, c3]) (fun _ => 1) fun _ =>
      Blaster.dite' ("bb" = String.mk [c1, c2, c3]) (fun _ => 2) fun _ =>
        Blaster.dite' ("ccc" = String.mk [c1, c2, c3]) (fun _ => 3) fun _ =>
          Blaster.dite' ("dddd" = String.mk [c1, c2, c3]) (fun _ => 4) fun _ => 5


variable (n1 : Nat)
variable (n2 : Nat)
-- namedPatternNatTwo (Nat.succ (Nat.succ n1)) (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2)))))) ===>
--  Blaster.dite' (n1 < 2)
--  (fun _ => (Nat.add 4 n2).mul ((Nat.add 3 n2).mul (n2.mul (n1.add (Nat.add 2 n1)))))
--  (fun _ => (((n1.add (n1.sub 2)).add (Nat.add 1 n1)).add (Nat.add 2 n1)).add (Nat.add 5 n2))
-- NOTE: Normalized and simplified via match to ite rule
#testOptimize [ "MatchReduceUnchanged_15" ] (norm-result: 1)
 namedPatternNatTwo (Nat.succ (Nat.succ n1)) (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2)))))) ===>
   Blaster.dite' (n1 < 2)
   (fun _ => (Nat.add 4 n2).mul ((Nat.add 3 n2).mul (n2.mul (n1.add (Nat.add 2 n1)))))
   (fun _ => (((n1.add (n1.sub 2)).add (Nat.add 1 n1)).add (Nat.add 2 n1)).add (Nat.add 5 n2))

-- namedPatternNatTwo (n1 + 2) (n2 + 5) ===>
--  Blaster.dite' (n1 < 2)
--  (fun _ => (Nat.add 4 n2).mul ((Nat.add 3 n2).mul (n2.mul (n1.add (Nat.add 2 n1)))))
--  (fun _ => (((n1.add (n1.sub 2)).add (Nat.add 1 n1)).add (Nat.add 2 n1)).add (Nat.add 5 n2))
#testOptimize [ "MatchReduceUnchanged_16" ] (norm-result: 1)
  namedPatternNatTwo (n1 + 2) (n2 + 5) ===>
   Blaster.dite' (n1 < 2)
   (fun _ => (Nat.add 4 n2).mul ((Nat.add 3 n2).mul (n2.mul (n1.add (Nat.add 2 n1)))))
   (fun _ => (((n1.add (n1.sub 2)).add (Nat.add 1 n1)).add (Nat.add 2 n1)).add (Nat.add 5 n2))

def namedPatternIntTwo (x : Int) (y : Int) : Nat :=
 match x, y with
 | Int.ofNat p@Nat.zero, _ => p
 | _, Int.ofNat p@Nat.zero => p + 1
 | Int.ofNat p@(Nat.succ Nat.zero), _ => Int.toNat y + (p + Int.toNat x)
 | _, Int.ofNat (Nat.succ Nat.zero) => Int.toNat x + 3
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), z => n + Int.toNat z
 | Int.ofNat (Nat.succ (Nat.succ _)), Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ _)))))) => Int.toNat x
 | _, _ => Int.toNat x

-- ∀ (n1 n2 : Nat),
--    namedPatternIntTwo
--     (Int.ofNat (Nat.succ (Nat.succ n1)))
--     (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2))))))) ===>
--  Blaster.dite' (n1 < 2) (fun _ => Nat.add 2 n1) (fun _ => (Nat.add 5 n2).add ((Nat.add 2 n1).sub 4))
-- NOTE: Normalized and simplified via match to ite, eq and relational rules
#testOptimize [ "MatchReduceUnchanged_17" ] (norm-result: 1)
  namedPatternIntTwo
   (Int.ofNat (Nat.succ (Nat.succ n1)))
   (Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2))))))) ===>
     Blaster.dite' (n1 < 2) (fun _ => Nat.add 2 n1) (fun _ => (Nat.add 5 n2).add ((Nat.add 2 n1).sub 4))

end Tests.MatchReduce
