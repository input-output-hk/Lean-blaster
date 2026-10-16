import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ElimMatch

/-! ## Test objectives to validate match elimination rules. -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def colorRank (x : Color) : Nat :=
 match x with
 | .black => 0
 | .transparent => 1
 | .blue _ => 2
 | .red _ => 3

def toColorDegreeOne (x : Color) : Nat :=
  match x with
  | .red _ => 2 * colorRank x
  | .blue _ => 4 * colorRank x
  | .black => colorRank x
  | .transparent => colorRank x

variable (x : Color)

-- toColorDegreeOne x ===>
--  match x with
--  | .red _ => 6
--  | .blue _ => 8
--  | .black => 0
--  | .transparent => 1
#testOptimize [ "ElimMatch_1" ] (norm-result: 1)
  toColorDegreeOne x ===>
    match x with
    | .red _ => 6
    | .blue _ => 8
    | .black => 0
    | .transparent => 1

def toColorDegreeTwo (x : Color) : Nat :=
  match x with
  | .red .black => 1 + 2 * colorRank x
  | .red .transparent => 2 + 2 * colorRank x
  | .red p@(.blue _) => 3 + 2 * colorRank p
  | .red p@(.red _) => 4 + 2 * colorRank p
  | .blue .black => 1 + 4 * colorRank x
  | .blue (.red p@(.blue _)) => 100 * colorRank p
  | .black => colorRank x
  | .transparent => colorRank x
  | y => colorRank y

-- toColorDegreeTwo x ===>
--  match x with
--  | .red .black => 7
--  | .red .transparent => 8
--  | .red _p@(.blue _) => 7
--  | .red _p@(.red _) => 10
--  | .blue .black  => 9
--  | .blue (.red _p@(.blue _)) => 200
--  | .black => 0
--  | .transparent => 1
--  | _ =>
--    match x with
--    | .black => 0
--    | .transparent => 1
--    | .blue _ => 2
--    | .red _ => 3
-- NOTE: The default case can be simplified to 2 as the only case left for x to be `.blue _`
-- However, this will require more sophisticated rules
#testOptimize [ "ElimMatch_2" ] (norm-result: 1)
  toColorDegreeTwo x ===>
    match x with
    | .red .black => 7
    | .red .transparent => 8
    | .red _p@(.blue _) => 7
    | .red _p@(.red _) => 10
    | .blue .black  => 9
    | .blue (.red _p@(.blue _)) => 200
    | .black => 0
    | .transparent => 1
    | _ =>
      match x with
      | .black => 0
      | .transparent => 1
      | .blue _ => 2
      | .red _ => 3


def toColorDegreeThree (x : Color) : Nat :=
  match x with
  | .red _ => 10
  | .blue _ => 20
  | .transparent => 1
  | _ => match x with
         | .blue _ => 20
         | .transparent => 1
         | .red _=> 10
         | _ => colorRank x

-- toColorDegreeThree x ===>
--     match x with
--     | .red _ => 10
--     | .blue _ => 20
--     | .transparent => 1
--     | _ => match x with
--            | .black => 0
--            | .transparent => 1
--            | .blue _ => 2
--            | .red _ => 3
-- NOTE: Test case covering non eq pattern in context
-- NOTE: The default case can be reduced to 0 with advanced simplification rules.
#testOptimize [ "ElimMatch_3" ] (norm-result: 1)
  toColorDegreeThree x ===>
      match x with
      | .red _ => 10
      | .blue _ => 20
      | .transparent => 1
      | _ => match x with
             | .black => 0
             | .transparent => 1
             | .blue _ => 2
             | .red _ => 3


def toColorDegreeFour (x : Color) (n : Nat) : Nat :=
  match x, n with
  | .red _, Nat.succ p@(Nat.succ (Nat.succ y)) => y + p * colorRank x
  | .blue _, Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ ((Nat.succ n2))))) => p * q * n2 * colorRank x
  | .transparent, Nat.succ Nat.zero => n + colorRank x
  | y, n' => n' * colorRank y

variable (n : Nat)

-- toColorDegreeFour x n ===>
--  match x, n with
--  | .red _, Nat.succ p@(Nat.succ (Nat.succ y)) => Nat.add y (Nat.mul 3 (Nat.add 2 y))
--  | .blue _, Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ ((Nat.succ n2))))) =>
--       Nat.mul 2 (Nat.mul n2 (Nat.mul (Nat.add 3 n2) (Nat.add 4 n2)))
--  | .transparent, Nat.succ Nat.zero => 2
--  | _, _ => Nat.mul n (match x with
--                       | .black => 0
--                       | .transparent => 1
--                       | .blue _ => 2
--                       | .red _ => 3)
-- NOTE: The default case can be simplified to 0 as the only case left for x to be `.black`
-- However, this will require more sophisticated rules
#testOptimize [ "ElimMatch_4" ] (norm-result: 1)
  toColorDegreeFour x n ===>
    match x, n with
    | .red _, Nat.succ _p@(Nat.succ (Nat.succ y)) => Nat.add y (Nat.mul 3 (Nat.add 2 y))
    | .blue _, Nat.succ _q@(Nat.succ _p@(Nat.succ (Nat.succ ((Nat.succ n2))))) =>
          Nat.mul 2 (Nat.mul n2 (Nat.mul (Nat.add 3 n2) (Nat.add 4 n2)))
    | .transparent, Nat.succ Nat.zero => 2
    | _, _ => Nat.mul n (match x with
                         | .black => 0
                         | .transparent => 1
                         | .blue _ => 2
                         | .red _ => 3)

def toColorDegreeFive (x : Color) (n : Int) : Nat :=
  match x, n with
  | .red _, Int.ofNat p@(Nat.succ Nat.zero) => n.toNat + p * colorRank x
  | .blue _, Int.negSucc p@(Nat.succ q@(Nat.succ Nat.zero)) => p * q * colorRank x
  | .transparent,  Int.negSucc q@(Nat.succ (Nat.succ p@(Nat.succ (Nat.succ n1)))) => n1 + p + q + colorRank x
  | y, n' => n'.toNat * colorRank y



variable (m : Int)

-- toColorDegreeFive x m ===>
--  match x, m with
--  | .red _, Int.ofNat _p@(Nat.succ Nat.zero) => 4
--  | .blue _, Int.negSucc _p@(Nat.succ _q@(Nat.succ Nat.zero)) => 4
--  | .transparent,  Int.negSucc q@(Nat.succ (Nat.succ p@(Nat.succ (Nat.succ n1)))) =>
--        Nat.add 1 (Nat.add (Nat.add n1 (Nat.add 2 n1)) (Nat.add 4 n1))
--  | _, _ => Nat.mul m.toNat (match x with
--                             | .black => 0
--                             | .transparent => 1
--                             | .blue _ => 2
--                             | .red _ => 3)
#testOptimize [ "ElimMatch_5" ] (norm-result: 1)
  toColorDegreeFive x m ===>
    match x, m with
    | .red _, Int.ofNat _p@(Nat.succ Nat.zero) => 4
    | .blue _, Int.negSucc _p@(Nat.succ _q@(Nat.succ Nat.zero)) => 4
    | .transparent,  Int.negSucc _q@(Nat.succ (Nat.succ _p@(Nat.succ (Nat.succ n1)))) =>
           Nat.add 1 (Nat.add (Nat.add n1 (Nat.add 2 n1)) (Nat.add 4 n1))
    | _, _ => Nat.mul m.toNat (match x with
                                | .black => 0
                                | .transparent => 1
                                | .blue _ => 2
                                | .red _ => 3)

-- toColorDegreeTwo (.red x) ===>
--   match (Color.red x) with
--   | .red .black => 7
--   | .red .transparent => 8
--   | .red _p@(.blue _) => 7
--   | .red _p@(.red _) => 10
--   | .blue .black  => 13
--   | .blue (.red _p@(.blue _)) => 200
--   | .black => 3
--   | .transparent => 3
--   | _ => 3
#testOptimize [ "ElimMatch_6" ] (norm-result: 1)
  toColorDegreeTwo (.red x) ===>
    match (Color.red x) with
    | .red .black => 7
    | .red .transparent => 8
    | .red _p@(.blue _) => 7
    | .red _p@(.red _) => 10
    | .blue .black  => 13
    | .blue (.red _p@(.blue _)) => 200
    | .black => 3
    | .transparent => 3
    | _ => 3


def toColorDegreeSix (x : Color) (n : Nat) : Nat :=
  match x, n with
  | .red .black, Nat.succ Nat.zero => 1 + 2 * colorRank x
  | .red .transparent, Nat.succ y => 2 + y * colorRank x
  | .red p@(.blue (.blue b)), Nat.succ (Nat.succ y) => y + colorRank b + 2 * colorRank p
  | .red p@(.blue (.red r)), Nat.succ (Nat.succ (Nat.succ y))  => y + colorRank r * colorRank p
  | .red p@(.blue b), Nat.zero => 3 + colorRank b + 2 * colorRank p
  | y, z => z + colorRank y

-- toColorDegreeSix (.red (.blue (.blue (.red x)))) n ===>
--  match (Color.red (Color.blue (Color.blue (Color.red x)))), n with
--  | .red .black, Nat.succ Nat.zero => 7
--  | .red .transparent, Nat.succ y => Nat.add 2 (Nat.mul 3 y)
--  | .red _p@(.blue (.blue _)), Nat.succ (Nat.succ y) => Nat.add 7 y
--  | .red _p@(.blue (.red r)), Nat.succ (Nat.succ (Nat.succ y))  =>
--     Nat.add y ( Tests.ElimMatch.colorRank.match_1 (fun _ : Color => Nat) r
--                 (fun _ => 0)
--                 (fun _ => 2)
--                 (fun _ => 4)
--                 (fun _ => 6) )
--  | .red _p@(.blue _), Nat.zero => 9
--  | _, _ => Nat.add 3 n
#testOptimize [ "ElimMatch_7" ] (norm-result: 1)
  toColorDegreeSix (.red (.blue (.blue (.red x)))) n ===>
    match (Color.red (Color.blue (Color.blue (Color.red x)))), n with
    | .red .black, Nat.succ Nat.zero => 7
    | .red .transparent, Nat.succ y => Nat.add 2 (Nat.mul 3 y)
    | .red _p@(.blue (.blue _)), Nat.succ (Nat.succ y) => Nat.add 7 y
    | .red _p@(.blue (.red r)), Nat.succ (Nat.succ (Nat.succ y))  =>
       Nat.add y ( Tests.ElimMatch.colorRank.match_1 (fun _ : Color => Nat) r
                   (fun _ => 0)
                   (fun _ => 2)
                   (fun _ => 4)
                   (fun _ => 6) )
    | .red _p@(.blue _), Nat.zero => 9
    | _, _ => Nat.add 3 n


def toColorDegreeSeven (x : Color) : Nat :=
  match (Color.red x) with
  | .red .black => 1 + 2 * colorRank x
  | .red .transparent => 2 * colorRank x
  | .red (.blue p@(.blue _)) => colorRank x + 2 * colorRank p
  | .red (.blue p@(.red _)) => colorRank p * colorRank x
  | .red (.red (.blue p@(.red _))) => colorRank x * 3 + colorRank p
  | y' => colorRank y'


-- toColorDegreeSeven x ===>
--   match (Color.red x) with
--   | .red .black => 1
--   | .red .transparent => 2
--   | .red (.blue _p@(.blue _)) => 6
--   | .red (.blue _p@(.red _)) => 6
--   | .red (.red (.blue _p@(.red _))) => 12
--   | _ => 3
#testOptimize [ "ElimMatch_8" ] (norm-result: 1)
  toColorDegreeSeven x ===>
    match (Color.red x) with
    | .red .black => 1
    | .red .transparent => 2
    | .red (.blue _p@(.blue _)) => 6
    | .red (.blue _p@(.red _)) => 6
    | .red (.red (.blue _p@(.red _))) => 12
    | _ => 3

def toColorDegreeOneSwap (x : Color) : Nat :=
  match x with
  | .blue _ => 4 * colorRank x
  | .red _ => 2 * colorRank x
  | .transparent => colorRank x
  | .black => colorRank x

variable (c : Bool)

-- if c then toColorDegreeOne x else toColorDegreeOneSwap x ===>
-- Blaster.dite' (true = c)
--   (fun _ => match x with
--             | .red _ => 6
--             | .blue _ => 8
--             | .black => 0
--             | .transparent => 1 )
--   (fun _ =>  match x with
--              | .blue _ => 8
--              | .red _ => 6
--              | .transparent => 1
--              | .black => 0 )
-- NOTE: Test case to validate context reuse are handled properly
#testOptimize [ "ElimMatch_9" ] (norm-result: 1)
  if c then toColorDegreeOne x else toColorDegreeOneSwap x ===>
  Blaster.dite' (true = c)
    (fun _ => match x with
              | .red _ => 6
              | .blue _ => 8
              | .black => 0
              | .transparent => 1 )
    (fun _ =>  match x with
               | .blue _ => 8
               | .red _ => 6
               | .transparent => 1
               | .black => 0 )

-- toColorDegreeOne x = toColorDegreeOneSwap x ===> True
-- NOTE: Test case to validate context reuse are handled properly
#testOptimize [ "ElimMatch_10" ] (norm-result: 1)
  toColorDegreeOne x = toColorDegreeOneSwap x ===> True


variable (n : Nat)
-- n = toColorDegreeOne x ∧ (n = toColorDegreeOneSwap x) ===>
-- (n =
--    match x with
--    | .red _ => 6
--    | .blue _ => 8
--    | .black => 0
--    | .transparent => 1) ∧
-- (n =
--   match x with
--   | .blue _ => 8
--   | .red _ => 6
--   | .transparent => 1
--   | .black => 0 )
-- NOTE: Test case to validate context reuse are handled properly
#testOptimize [ "ElimMatch_11" ] (norm-result: 1)
  n = toColorDegreeOne x ∧ (n = toColorDegreeOneSwap x) ===>
  (n =
     match x with
     | .red _ => 6
     | .blue _ => 8
     | .black => 0
     | .transparent => 1) ∧
  (n =
    match x with
    | .blue _ => 8
    | .red _ => 6
    | .transparent => 1
    | .black => 0 )

def toColorDegreeSwap (x : Color) : Nat :=
  match x with
  | .blue _ => 2 * colorRank x
  | .red _ => 2 * colorRank x
  | .transparent => colorRank x
  | .black => colorRank x


inductive Taint where
  | dark : Color → Taint
  | pale : Color → Taint
  | gray : Taint
  | NoTaint : Taint

def toColorTaintDegree (n : Taint) (x : Color) : Nat :=
  match n with
  | .dark _ => 2 * colorRank x
  | .pale _ => 2 * colorRank x
  | .gray => colorRank x
  | .NoTaint => colorRank x


variable (t : Taint)
-- NOTE: Test case to validate context reuse are handled properly
#testOptimize [ "ElimMatch_11" ] (norm-result: 1)
  ((match x with
   | .blue _ => 2 * colorRank x
   | .red _ => 2 * colorRank x
   | .transparent => colorRank x
   | .black => colorRank x) + n)
  * ((match t with
     | .dark _ => 2 * colorRank x
     | .pale _ => 2 * colorRank x
     | .gray => colorRank x
     | .NoTaint => colorRank x) + n) ===>
    Nat.mul
      (Nat.add n
        (match x with
         | .blue _ => 4
         | .red _ => 6
         | .transparent => 1
         | .black => 0))
      (Nat.add n
        (match t with
        | .dark _ =>
          match x with
          | .black => 0
          | .transparent => 2
          | .blue _ => 4
          | .red _ => 6
        | .pale _ =>
          match x with
          | .black => 0
          | .transparent => 2
          | .blue _ => 4
          | .red _ => 6
        | .gray =>
          match x with
          | .black => 0
          | .transparent => 1
          | .blue _ => 2
          | .red _ => 3
        | .NoTaint =>
          match x with
          | .black => 0
          | .transparent => 1
          | .blue _ => 2
          | .red _ => 3))


end Tests.ElimMatch
