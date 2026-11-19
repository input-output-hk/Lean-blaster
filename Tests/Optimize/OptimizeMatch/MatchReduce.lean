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

/-! ## Test cases on Nat/Int literal discriminators.
     - literal patterns, offset patterns (`k + c`, `Int.ofNat (k + c)`, `Int.negSucc (k + c)`),
       variable patterns and named patterns.
     - `MatchReduce_26` .. `MatchReduce_73`: choice reduction must be applied.
     - `MatchReduceUnchanged_18` .. `MatchReduceUnchanged_25`: choice reduction must NOT be applied,
       but some discriminators unify with their pattern (equality map update). -/

def natLit (x : Nat) : Nat :=
  match x with
  | 0 => 100
  | 1 => 101
  | 5 => 105
  | k + 2 => k

-- literal pattern hit
#testOptimize [ "MatchReduce_26" ] natLit 0 = 100 ===> True
#testOptimize [ "MatchReduce_27" ] natLit 1 = 101 ===> True
#testOptimize [ "MatchReduce_28" ] natLit 5 = 105 ===> True
-- offset pattern `k + 2`: literal ≥ offset binds `k := lit - 2`
#testOptimize [ "MatchReduce_29" ] natLit 2 = 0 ===> True
#testOptimize [ "MatchReduce_30" ] natLit 7 = 5 ===> True
-- `Nat.succ` / `Nat.zero` spelled discriminators normalize to literals
#testOptimize [ "MatchReduce_31" ] natLit (Nat.succ (Nat.succ (Nat.succ Nat.zero))) = 1 ===> True
#testOptimize [ "MatchReduce_32" ] natLit Nat.zero = 100 ===> True
-- off-by-one must be refuted
#testOptimize [ "MatchReduce_33" ] natLit 7 = 6 ===> False
#testOptimize [ "MatchReduce_34" ] natLit 5 = 3 ===> False

-- named patterns on Nat: the alias must be bound to the normalized (literal) value
def natNamed (x : Nat) : Nat :=
  match x with
  | m@0 => m + 50
  | m@(k + 3) => m * k
  | m@(k + 1) => m + k

#testOptimize [ "MatchReduce_35" ] natNamed 0 = 50 ===> True
#testOptimize [ "MatchReduce_36" ] natNamed 7 = 28 ===> True
#testOptimize [ "MatchReduce_37" ] natNamed 3 = 0 ===> True
#testOptimize [ "MatchReduce_38" ] natNamed 2 = 3 ===> True
#testOptimize [ "MatchReduce_39" ] natNamed 1 = 1 ===> True
#testOptimize [ "MatchReduce_40" ] natNamed 7 = 21 ===> False

def intLit (x : Int) : Nat :=
  match x with
  | .ofNat 0 => 200
  | .ofNat 3 => 203
  | .negSucc 0 => 300
  | .negSucc 4 => 304
  | .ofNat (k + 1) => k
  | .negSucc (k + 1) => 2 * k

-- `Int.ofNat` literal patterns
#testOptimize [ "MatchReduce_41" ] intLit 0 = 200 ===> True
#testOptimize [ "MatchReduce_42" ] intLit 3 = 203 ===> True
#testOptimize [ "MatchReduce_43" ] intLit (Int.ofNat 3) = 203 ===> True
-- `Int.ofNat (k + 1)` offset pattern
#testOptimize [ "MatchReduce_44" ] intLit 1 = 0 ===> True
#testOptimize [ "MatchReduce_45" ] intLit 7 = 6 ===> True
#testOptimize [ "MatchReduce_46" ] intLit (Int.ofNat 7) = 6 ===> True
-- `Int.negSucc` literal patterns: `-1 = Int.negSucc 0`, `-5 = Int.negSucc 4`
#testOptimize [ "MatchReduce_47" ] intLit (-1) = 300 ===> True
#testOptimize [ "MatchReduce_48" ] intLit (-5) = 304 ===> True
#testOptimize [ "MatchReduce_49" ] intLit (Int.negSucc 0) = 300 ===> True
#testOptimize [ "MatchReduce_50" ] intLit (Int.negSucc 4) = 304 ===> True
-- `Int.negSucc (k + 1)` offset pattern: `-7 = Int.negSucc 6`, so `k := 5`
#testOptimize [ "MatchReduce_51" ] intLit (-2) = 0 ===> True
#testOptimize [ "MatchReduce_52" ] intLit (-7) = 10 ===> True
#testOptimize [ "MatchReduce_53" ] intLit (Int.negSucc 6) = 10 ===> True
-- negative literal obtained through constant folding
#testOptimize [ "MatchReduce_54" ] intLit (0 - 7) = 10 ===> True
#testOptimize [ "MatchReduce_55" ] intLit (-0) = 200 ===> True
-- off-by-one must be refuted
#testOptimize [ "MatchReduce_56" ] intLit (-7) = 8 ===> False
#testOptimize [ "MatchReduce_57" ] intLit (-5) = 6 ===> False
#testOptimize [ "MatchReduce_58" ] intLit 7 = 7 ===> False

-- named patterns on Int, on the whole discriminator and on the constructor argument
def intNamed (x : Int) : Nat :=
  match x with
  | p@(.ofNat 2) => p.toNat + 10
  | .ofNat m@(k + 3) => m * k
  | p@(.ofNat m) => p.toNat + m
  | p@(.negSucc 2) => p.natAbs + 20
  | .negSucc m@(k + 2) => m * k
  | p@(.negSucc m) => p.natAbs + m

#testOptimize [ "MatchReduce_59" ] intNamed 2 = 12 ===> True
#testOptimize [ "MatchReduce_60" ] intNamed 7 = 28 ===> True
#testOptimize [ "MatchReduce_61" ] intNamed 3 = 0 ===> True
#testOptimize [ "MatchReduce_62" ] intNamed 1 = 2 ===> True
#testOptimize [ "MatchReduce_63" ] intNamed 0 = 0 ===> True
#testOptimize [ "MatchReduce_64" ] intNamed (-3) = 23 ===> True
#testOptimize [ "MatchReduce_65" ] intNamed (-7) = 24 ===> True
#testOptimize [ "MatchReduce_66" ] intNamed (-4) = 3 ===> True
#testOptimize [ "MatchReduce_67" ] intNamed (-2) = 3 ===> True
#testOptimize [ "MatchReduce_68" ] intNamed (-1) = 1 ===> True
#testOptimize [ "MatchReduce_69" ] intNamed (-7) = 30 ===> False
#testOptimize [ "MatchReduce_70" ] intNamed (-2) = 2 ===> False

-- several Nat/Int literal discriminators
def mixedLit (x : Nat) (y : Int) : Nat :=
  match x, y with
  | 0, .negSucc 0 => 1
  | k + 1, .negSucc m => k + m
  | 2, .ofNat m => m
  | k, .ofNat (m + 3) => k * m
  | _, _ => 0

#testOptimize [ "MatchReduce_71" ] mixedLit 0 (-1) = 1 ===> True
#testOptimize [ "MatchReduce_72" ] mixedLit 3 (-7) = 8 ===> True
#testOptimize [ "MatchReduce_73" ] mixedLit 2 5 = 5 ===> True
#testOptimize [ "MatchReduce_74" ] mixedLit 4 10 = 28 ===> True
-- `Int.ofNat 2` does not unify with `Int.ofNat (m + 3)` (literal < offset)
#testOptimize [ "MatchReduce_75" ] mixedLit 1 2 = 0 ===> True
-- `Int.negSucc 2` does not unify with `Int.negSucc 0` nor with `Int.ofNat _`
#testOptimize [ "MatchReduce_76" ] mixedLit 0 (-3) = 0 ===> True
#testOptimize [ "MatchReduce_77" ] mixedLit 3 (-7) = 9 ===> False

-- named pattern `m@(k + 3)` unifies with the symbolic `Int.ofNat (3 + m)` (`m := 3 + m`, `k := m`)
variable (m : Nat)
#testOptimize [ "MatchReduce_78" ] (norm-result: 1)
  intNamed (Int.ofNat (m + 3)) ===> Nat.mul m (Nat.add 3 m)

/-! Choice reduction must NOT be applied, but discriminators unify with their pattern. -/

-- intLit (Int.negSucc m) ===>
--   Blaster.dite' (0 = m) (fun _ => 300) fun _ =>
--     Blaster.dite' (4 = m) (fun _ => 304) fun _ =>
--       Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 1)
--         (fun _ => Nat.mul 2 (Nat.sub (Nat.add 1 m) 2)) fun _ => 0
-- NOTE: `Int.negSucc m` is normalized to `Int.neg (Int.ofNat (1 + m))`; each `Int.negSucc` literal
--       pattern potentially matches and binds `m` in its alternative (300 and 304), `Int.negSucc (k + 1)`
--       binds `k := (1 + m) - 2`. The `Int.ofNat` literal alternatives are eliminated by the
--       `Int.ofNat N = Int.neg (Int.ofNat (N' + e)) ==> False` equality rule and the `Int.negSucc`
--       literal conditions are normalized by `Int.negSucc N = Int.neg (Int.ofNat e) ==> N + 1 = e`.
#testOptimize [ "MatchReduceUnchanged_18" ] (norm-result: 1)
  intLit (Int.negSucc m) ===>
  Blaster.dite' (0 = m) (fun _ => 300) fun _ =>
    Blaster.dite' (4 = m) (fun _ => 304) fun _ =>
      Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 1)
        (fun _ => Nat.mul 2 (Nat.sub (Nat.add 1 m) 2)) fun _ => 0

-- natLit (m + 2) ===> Blaster.dite' (3 = m) (fun _ => 105) fun _ => m
-- NOTE: `5` potentially matches `2 + m` (binding `m := 3`), `k + 2` unifies with `k := m`
#testOptimize [ "MatchReduceUnchanged_19" ] (norm-result: 1)
  natLit (m + 2) ===> Blaster.dite' (3 = m) (fun _ => 105) fun _ => m

-- natNamed (m + 1) ===>
--   Blaster.dite' (m < 2) (fun _ => Nat.add m (Nat.add 1 m)) fun _ => Nat.mul (Nat.add 1 m) (Nat.sub (Nat.add 1 m) 3)
-- NOTE: named pattern aliases are bound through the equality map: `m@(k + 3)` gives `m := 1 + m`,
--       `k := (1 + m) - 3` and `m@(k + 1)` gives `m := 1 + m`, `k := m`
#testOptimize [ "MatchReduceUnchanged_20" ] (norm-result: 1)
  natNamed (m + 1) ===>
  Blaster.dite' (m < 2) (fun _ => Nat.add m (Nat.add 1 m)) fun _ => Nat.mul (Nat.add 1 m) (Nat.sub (Nat.add 1 m) 3)

-- intNamed (Int.negSucc m) ===>
--   Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 3)
--     (fun _ =>
--       Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 0)
--         (fun _ =>
--           Blaster.dite' (2 = m) (fun _ => 23) fun _ =>
--             Blaster.dite' (Int.negSucc 2 < Int.neg (Int.ofNat (Nat.add 1 m)))
--               (fun _ => Nat.add m (Nat.add 1 m)) fun _ => Nat.mul m (Nat.sub m 2))
--         fun _ => 0)
--     fun _ => 0
-- NOTE: `p@(.negSucc 2)` binds `p := Int.negSucc 2` (23), `.negSucc m@(k + 2)` binds `m := m`,
--       `k := m - 2` and `p@(.negSucc m)` binds `p := Int.neg (Int.ofNat (1 + m))`.
--       The `p@(.ofNat 2)` alternative is eliminated by the `Int.ofNat N = Int.neg (Int.ofNat (N' + e)) ==> False` rule.
#testOptimize [ "MatchReduceUnchanged_21" ] (norm-result: 1)
  intNamed (Int.negSucc m) ===>
  Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 3)
    (fun _ =>
      Blaster.dite' (Int.neg (Int.ofNat (Nat.add 1 m)) < Int.ofNat 0)
        (fun _ =>
          Blaster.dite' (2 = m) (fun _ => 23) fun _ =>
            Blaster.dite' (Int.negSucc 2 < Int.neg (Int.ofNat (Nat.add 1 m)))
              (fun _ => Nat.add m (Nat.add 1 m)) fun _ => Nat.mul m (Nat.sub m 2))
        fun _ => 0)
    fun _ => 0

-- mixedLit 3 w ===>
--   Blaster.dite' (Int.negSucc 0 < w)
--     (fun _ => Blaster.dite' (w < Int.ofNat 3) (fun _ => 0) fun _ => Nat.mul 3 (Nat.sub (Int.toNat w) 3))
--     fun _ => Nat.add 2 (Nat.sub (Int.toNat (Int.neg w)) 1)
-- NOTE: the Nat literal discriminator unifies with `k + 1` (`k := 2`) and `k` (`k := 3`)
#testOptimize [ "MatchReduceUnchanged_22" ] (norm-result: 1)
  mixedLit 3 w ===>
  Blaster.dite' (Int.negSucc 0 < w)
    (fun _ => Blaster.dite' (w < Int.ofNat 3) (fun _ => 0) fun _ => Nat.mul 3 (Nat.sub (Int.toNat w) 3))
    fun _ => Nat.add 2 (Nat.sub (Int.toNat (Int.neg w)) 1)

-- mixedLit n (-7) ===> Blaster.dite' (0 = n) (fun _ => 0) fun _ => Nat.add 6 (Nat.sub n 1)
-- NOTE: `-7 = Int.negSucc 6` unifies with `.negSucc m` (`m := 6`) and refutes `.negSucc 0` and `.ofNat _`
#testOptimize [ "MatchReduceUnchanged_23" ] (norm-result: 1)
  mixedLit n (-7) ===> Blaster.dite' (0 = n) (fun _ => 0) fun _ => Nat.add 6 (Nat.sub n 1)

-- mixedLit n 10 ===> Blaster.dite' (2 = n) (fun _ => 10) fun _ => Nat.mul 7 n
-- NOTE: `10` unifies with `.ofNat m` (`m := 10`) and `.ofNat (m + 3)` (`m := 7`)
#testOptimize [ "MatchReduceUnchanged_24" ] (norm-result: 1)
  mixedLit n 10 ===> Blaster.dite' (2 = n) (fun _ => 10) fun _ => Nat.mul 7 n

end Tests.MatchReduce
