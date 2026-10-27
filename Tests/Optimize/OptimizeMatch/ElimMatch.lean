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
#testOptimize [ "ElimMatch_12" ] (norm-result: 1)
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



/-! ## Test cases covering the match elimination rules of `elimMatch?`:
     - `commonRhs?`: all alternatives have the same rhs (without loose bound variables).
     - `lastPatternReduction?`: every alternative but the last one has a constructor pattern
       recorded as a `NotEqPattern` for its discriminator in `matchInContext`, and the last
       alternative unifies with the discriminators. `matchInContext` is populated:
         - by `addNotEqPatternToContext` when optimizing an alternative of an outer match: the
           patterns of the previous alternatives having exactly one non-variable pattern are
           recorded for their discriminator;
         - by `propagateNotEqPatternContext` through the `equalityMap`: when a discriminator `e`
           is unified with a constructor pattern `p` (`e := p` in `equalityMap`), the
           `NotEqPattern` recorded for `e` are also recorded for `p` (as `e` is rewritten to `p`
           in the alternative's rhs). -/

axiom colorOf : Nat → Color

/-! `commonRhs?` -/

-- ∀ (x : Color) (n r : Nat), r = match x with | .red _ => n | .blue _ => n | .black => n | .transparent => n ===>
-- ∀ (n r : Nat), n = r
-- NOTE: the binder `x` is removed by forall reduction once the match is eliminated.
#testOptimize [ "ElimMatch_13" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat), r = match x with | .red _ => n | .blue _ => n | .black => n | .transparent => n ===>
  ∀ (n r : Nat), n = r

-- ∀ (x : Color) (n r : Nat), r = match x with | .red _ => n + 0 | .blue _ => 0 + n | .black => n * 1 | .transparent => n ===>
-- ∀ (n r : Nat), n = r
-- NOTE: the rhs are equal once optimized (`elimMatch?` is applied after the alternatives are optimized).
#testOptimize [ "ElimMatch_14" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat), r = match x with | .red _ => n + 0 | .blue _ => 0 + n | .black => n * 1 | .transparent => n ===>
  ∀ (n r : Nat), n = r

-- ∀ (x : Color) (r : Nat), r = match x with | .red y => colorRank y | .blue y => colorRank y | .black => 0 | .transparent => 0 ===>
-- ∀ (x : Color) (r : Nat),
--   r = match x with
--       | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | .blue y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | .black => 0
--       | .transparent => 0
-- NOTE: no common rhs as the rhs of the first alternative depends on the pattern variable `y`.
#testOptimize [ "ElimMatch_15" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red y => colorRank y | .blue y => colorRank y | .black => 0 | .transparent => 0 ===>
  ∀ (x : Color) (r : Nat),
    r = match x with
        | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | .blue y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | .black => 0
        | .transparent => 0

/-! `lastPatternReduction?` with `matchInContext` populated by `addNotEqPatternToContext` -/

-- ∀ (n r : Nat), r = match colorOf n with | .red _ => 1 | .blue _ => 2 | _ => match colorOf n with | .red _ => 3 | .blue _ => 4 | _ => 5 ===>
-- ∀ (n r : Nat), r = match colorOf n with | .red _ => 1 | .blue _ => 2 | _ => 5
-- NOTE: the discriminator is an opaque application (see `ElimMatch_3` for a variable discriminator).
#testOptimize [ "ElimMatch_16" ] (norm-result: 1)
  ∀ (n r : Nat), r = match colorOf n with | .red _ => 1 | .blue _ => 2 | _ => match colorOf n with | .red _ => 3 | .blue _ => 4 | _ => 5 ===>
  ∀ (n r : Nat), r = match colorOf n with | .red _ => 1 | .blue _ => 2 | _ => 5

-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red (.blue _) => 2 | _ => 3 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => 3
-- NOTE: nested constructor pattern.
#testOptimize [ "ElimMatch_17" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red (.blue _) => 2 | _ => 3 ===>
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => 3

-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red _ => 2 | _ => 3 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red _ => 2 | _ => 3
-- NOTE: no elimination as the inner pattern `.red _` is more general than the recorded `.red (.blue _)`.
#testOptimize [ "ElimMatch_18" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red _ => 2 | _ => 3 ===>
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | _ => match x with | .red _ => 2 | _ => 3

-- ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => match x with | .red _ => 2 | .blue _ => 3 | _ => 4 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => match x with | .red _ => 2 | .blue _ => 3 | _ => 4
-- NOTE: no elimination as `.blue _` is not recorded for `x`.
#testOptimize [ "ElimMatch_19" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => match x with | .red _ => 2 | .blue _ => 3 | _ => 4 ===>
  ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => match x with | .red _ => 2 | .blue _ => 3 | _ => 4

-- ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | .blue _ => 2 | _ => match x with | .red _ => 3 | .blue _ => 4 | .black => 5 | .transparent => 6 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | .blue _ => 2 | _ => match x with | .red _ => 3 | .blue _ => 4 | .black => 5 | .transparent => 6
-- NOTE: no elimination as the last alternative of the inner match does not unify with `x`
-- (`.transparent` is only a potential match for the variable `x`).
#testOptimize [ "ElimMatch_20" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | .blue _ => 2 | _ => match x with | .red _ => 3 | .blue _ => 4 | .black => 5 | .transparent => 6 ===>
  ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | .blue _ => 2 | _ => match x with | .red _ => 3 | .blue _ => 4 | .black => 5 | .transparent => 6

-- ∀ (x : Color) (n r : Nat),
--   r = match x, n with | .red _, _ => 1 | _, 0 => 2 | _, _ => (match x with | .red _ => 3 | _ => 4) + (match n with | 0 => 5 | _ => 6) ===>
-- ∀ (x : Color) (n r : Nat),
--   r = match x, n with | .red _, _ => 1 | _, 0 => 2 | _, _ => Blaster.dite' (0 = n) (fun _ => 9) (fun _ => 10)
-- NOTE: alternatives with exactly one constructor pattern record it for the corresponding discriminator:
-- `.red _` for `x` and `0` for `n`. The inner match on `x` is eliminated, while the inner match on `n`
-- is normalized to an ite (literal pattern) before `elimMatch?` is applied, hence the recorded pattern
-- `0` for `n` is not exploited. It can be simplified further with additional simplification rules
-- (e.g., exploiting the recorded patterns when normalizing a match to an ite) to:
-- ∀ (x : Color) (n r : Nat), r = match x, n with | .red _, _ => 1 | _, 0 => 2 | _, _ => 10
#testOptimize [ "ElimMatch_21" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat),
    r = match x, n with | .red _, _ => 1 | _, 0 => 2 | _, _ => (match x with | .red _ => 3 | _ => 4) + (match n with | 0 => 5 | _ => 6) ===>
  ∀ (x : Color) (n r : Nat),
    r = match x, n with | .red _, _ => 1 | _, 0 => 2 | _, _ => Blaster.dite' (0 = n) (fun _ => 9) (fun _ => 10)

-- ∀ (x : Color) (n r : Nat), r = match x, n with | .red _, 0 => 1 | _, _ => match x with | .red _ => 2 | _ => 3 ===>
-- ∀ (x : Color) (n r : Nat), r = match x, n with | .red _, 0 => 1 | _, _ => match x with | .red _ => 2 | _ => 3
-- NOTE: no elimination as the first alternative has two constructor patterns (`x` may still be `.red _`).
#testOptimize [ "ElimMatch_22" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat), r = match x, n with | .red _, 0 => 1 | _, _ => match x with | .red _ => 2 | _ => 3 ===>
  ∀ (x : Color) (n r : Nat), r = match x, n with | .red _, 0 => 1 | _, _ => match x with | .red _ => 2 | _ => 3

-- ∀ (x : Color) (n r : Nat),
--   r = match x, colorOf n with | _, .red _ => 1 | .blue _, _ => 2 | _, _ => (match colorOf n with | .red _ => 3 | _ => 4) + (match x with | .blue _ => 5 | _ => 6) ===>
-- ∀ (x : Color) (n r : Nat), r = match x, colorOf n with | _, .red _ => 1 | .blue _, _ => 2 | _, _ => 10
-- NOTE: patterns are recorded for each discriminator independently.
#testOptimize [ "ElimMatch_23" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat),
    r = match x, colorOf n with | _, .red _ => 1 | .blue _, _ => 2 | _, _ => (match colorOf n with | .red _ => 3 | _ => 4) + (match x with | .blue _ => 5 | _ => 6) ===>
  ∀ (x : Color) (n r : Nat), r = match x, colorOf n with | _, .red _ => 1 | .blue _, _ => 2 | _, _ => 10

-- ∀ (x : Color) (n r : Nat), r = match x with | .red _ => 1 | _ => match x, n with | .red _, 0 => 2 | _, _ => 3 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => 3
-- NOTE: a single discriminator with a recorded pattern suffices to discard an inner alternative
-- (the binder `n` is then removed by forall reduction).
#testOptimize [ "ElimMatch_24" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat), r = match x with | .red _ => 1 | _ => match x, n with | .red _, 0 => 2 | _, _ => 3 ===>
  ∀ (x : Color) (r : Nat), r = match x with | .red _ => 1 | _ => 3

-- ∀ (x : Color) (r : Nat), r = match x with | p@(.red _) => colorRank p | _ => match x with | q@(.red _) => colorRank q | _ => 2 ===>
-- ∀ (x : Color) (r : Nat), r = match x with | _q@(.red _) => 3 | _ => 2
-- NOTE: named patterns are ignored when recording and looking up the `NotEqPattern`.
#testOptimize [ "ElimMatch_25" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | p@(.red _) => colorRank p | _ => match x with | q@(.red _) => colorRank q | _ => 2 ===>
  ∀ (x : Color) (r : Nat), r = match x with | _q@(.red _) => 3 | _ => 2

-- ∀ (c : Char) (r : Nat), r = match c with | 'a' => 1 | _ => match c with | 'a' => 2 | _ => 3 ===>
-- ∀ (c : Char) (r : Nat), r = match c with | 'a' => 1 | _ => 3
-- NOTE: literal pattern (Char literals are not normalized to ite).
#testOptimize [ "ElimMatch_26" ] (norm-result: 1)
  ∀ (c : Char) (r : Nat), r = match c with | 'a' => 1 | _ => match c with | 'a' => 2 | _ => 3 ===>
  ∀ (c : Char) (r : Nat), r = match c with | 'a' => 1 | _ => 3

-- ∀ (x : Color) (n r : Nat),
--   r = match x with | .red _ => 1 | _ => match colorOf n with | .blue _ => 2 | _ => (match x with | .red _ => 3 | _ => 4) + (match colorOf n with | .blue _ => 5 | _ => 6) ===>
-- ∀ (x : Color) (n r : Nat), r = match x with | .red _ => 1 | _ => match colorOf n with | .blue _ => 2 | _ => 10
-- NOTE: the patterns recorded by the enclosing matches are all visible (active contexts).
#testOptimize [ "ElimMatch_27" ] (norm-result: 1)
  ∀ (x : Color) (n r : Nat),
    r = match x with | .red _ => 1 | _ => match colorOf n with | .blue _ => 2 | _ => (match x with | .red _ => 3 | _ => 4) + (match colorOf n with | .blue _ => 5 | _ => 6) ===>
  ∀ (x : Color) (n r : Nat), r = match x with | .red _ => 1 | _ => match colorOf n with | .blue _ => 2 | _ => 10

/-! `lastPatternReduction?` with `matchInContext` populated by `propagateNotEqPatternContext` (`equalityMap`) -/

-- ∀ (o : Option (Option Nat)) (r : Nat), r = match o with | some (some _) => 1 | some _ => (match o with | some (some _) => 2 | _ => 3) | none => 4 ===>
-- ∀ (o : Option (Option Nat)) (r : Nat), r = match o with | some (some _) => 1 | some _ => 3 | none => 4
-- NOTE: in the second alternative, `o := some k` is added to the equality map and the pattern
-- `some (some _)` recorded for `o` is propagated to `some k`. The inner match discriminator is rewritten
-- to `some k`, for which `some (some _)` is only a potential match: the inner match is eliminated thanks to
-- the propagated pattern.
#testOptimize [ "ElimMatch_28" ] (norm-result: 1)
  ∀ (o : Option (Option Nat)) (r : Nat), r = match o with | some (some _) => 1 | some _ => (match o with | some (some _) => 2 | _ => 3) | none => 4 ===>
  ∀ (o : Option (Option Nat)) (r : Nat), r = match o with | some (some _) => 1 | some _ => 3 | none => 4

-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match x with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
-- ∀ (x : Color) (r : Nat),
--   r = match x with
--       | .red (.blue _) => 1
--       | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | _ => 3
#testOptimize [ "ElimMatch_29" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match x with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
  ∀ (x : Color) (r : Nat),
    r = match x with
        | .red (.blue _) => 1
        | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | _ => 3

-- ∀ (n r : Nat), r = match colorOf n with | .red (.blue _) => 1 | .red y => (match colorOf n with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
-- ∀ (n r : Nat),
--   r = match colorOf n with
--       | .red (.blue _) => 1
--       | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | _ => 3
-- NOTE: same as `ElimMatch_29` with an opaque application as discriminator (`colorOf n := .red y`).
#testOptimize [ "ElimMatch_30" ] (norm-result: 1)
  ∀ (n r : Nat), r = match colorOf n with | .red (.blue _) => 1 | .red y => (match colorOf n with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
  ∀ (n r : Nat),
    r = match colorOf n with
        | .red (.blue _) => 1
        | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | _ => 3

-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match Color.red y with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
-- ∀ (x : Color) (r : Nat),
--   r = match x with
--       | .red (.blue _) => 1
--       | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | _ => 3
-- NOTE: the inner discriminator is directly the pattern `Color.red y` (the propagated pattern is recorded for it).
#testOptimize [ "ElimMatch_31" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match Color.red y with | .red (.blue _) => 2 | _ => colorRank y) | _ => 3 ===>
  ∀ (x : Color) (r : Nat),
    r = match x with
        | .red (.blue _) => 1
        | .red y => (match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | _ => 3

-- ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match x with | .red (.red _) => 2 | _ => colorRank y) | _ => 3 ===>
-- ∀ (x : Color) (r : Nat),
--   r = match x with
--       | .red (.blue _) => 1
--       | .red y => (match Color.red y with
--                    | .red (.red _) => 2
--                    | _ => match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
--       | _ => 3
-- NOTE: no elimination as `.red (.red _)` is not recorded for `x` (nor propagated to `Color.red y`);
-- the inner discriminator `x` is rewritten to `Color.red y` through the equality map.
#testOptimize [ "ElimMatch_32" ] (norm-result: 1)
  ∀ (x : Color) (r : Nat), r = match x with | .red (.blue _) => 1 | .red y => (match x with | .red (.red _) => 2 | _ => colorRank y) | _ => 3 ===>
  ∀ (x : Color) (r : Nat),
    r = match x with
        | .red (.blue _) => 1
        | .red y => (match Color.red y with
                     | .red (.red _) => 2
                     | _ => match y with | .black => 0 | .transparent => 1 | .blue _ => 2 | .red _ => 3)
        | _ => 3

/-! Literal patterns: the inner match is normalized to an ite before `elimMatch?` is applied. -/

axiom optOf : Nat → Option Nat

-- ∀ (n r : Nat), r = match optOf n with | some 0 => 1 | some k => (match optOf n with | some 0 => 2 | _ => k) | none => 3 ===>
-- ∀ (n r : Nat), r = match optOf n with | some 0 => 1 | some k => Blaster.dite' (some k = some 0) (fun _ => 2) (fun _ => k) | none => 3
-- NOTE: `optOf n := some k` is added to the equality map and the pattern `some 0` recorded for `optOf n` is
-- propagated to `some k`. However, the inner match (rewritten to `match some k with ...`) is normalized to
-- an ite before `elimMatch?` is applied, hence the propagated pattern is not exploited. It can be simplified
-- further with additional simplification rules (e.g., constructor injectivity `some k = some 0 ==> k = 0`
-- together with the recorded patterns) to:
-- ∀ (n r : Nat), r = match optOf n with | some 0 => 1 | some k => k | none => 3
#testOptimize [ "ElimMatch_33" ] (norm-result: 1)
  ∀ (n r : Nat), r = match optOf n with | some 0 => 1 | some k => (match optOf n with | some 0 => 2 | _ => k) | none => 3 ===>
  ∀ (n r : Nat), r = match optOf n with | some 0 => 1 | some k => Blaster.dite' (some k = some 0) (fun _ => 2) (fun _ => k) | none => 3

-- ∀ (o : Option Nat) (r : Nat), r = match o with | some 0 => 1 | some k => (match o with | some 0 => 2 | _ => k) | none => 3 ===>
-- ∀ (o : Option Nat) (r : Nat), r = match o with | some 0 => 1 | some k => Blaster.dite' (some k = some 0) (fun _ => 2) (fun _ => k) | none => 3
-- NOTE: same as `ElimMatch_33` with a variable discriminator (`o := some k`). It can be simplified further
-- with additional simplification rules to:
-- ∀ (o : Option Nat) (r : Nat), r = match o with | some 0 => 1 | some k => k | none => 3
#testOptimize [ "ElimMatch_34" ] (norm-result: 1)
  ∀ (o : Option Nat) (r : Nat), r = match o with | some 0 => 1 | some k => (match o with | some 0 => 2 | _ => k) | none => 3 ===>
  ∀ (o : Option Nat) (r : Nat), r = match o with | some 0 => 1 | some k => Blaster.dite' (some k = some 0) (fun _ => 2) (fun _ => k) | none => 3

-- ∀ (n r : Nat), r = match n with | 0 => 1 | 1 => 2 | _ => match n with | 0 => 3 | 1 => 4 | _ => 5 ===>
-- ∀ (n r : Nat), r = Blaster.dite' (0 = n) (fun _ => 1) (fun _ => Blaster.dite' (1 = n) (fun _ => 2) (fun _ => 5))
-- NOTE: both matches are normalized to ite (Nat literal patterns): the inner one is simplified through the
-- ite hypotheses `¬ 0 = n` and `¬ 1 = n` rather than by `elimMatch?`.
#testOptimize [ "ElimMatch_35" ] (norm-result: 1)
  ∀ (n r : Nat), r = match n with | 0 => 1 | 1 => 2 | _ => match n with | 0 => 3 | 1 => 4 | _ => 5 ===>
  ∀ (n r : Nat), r = Blaster.dite' (0 = n) (fun _ => 1) (fun _ => Blaster.dite' (1 = n) (fun _ => 2) (fun _ => 5))

-- ∀ (s : String) (r : Nat), r = match s with | "a" => 1 | _ => match s with | "a" => 2 | _ => 3 ===>
-- ∀ (s : String) (r : Nat), r = Blaster.dite' ("a" = s) (fun _ => 1) (fun _ => 3)
-- NOTE: same as `ElimMatch_35` with String literal patterns (see `ElimMatch_26` for Char literal patterns,
-- which are not normalized to ite).
#testOptimize [ "ElimMatch_36" ] (norm-result: 1)
  ∀ (s : String) (r : Nat), r = match s with | "a" => 1 | _ => match s with | "a" => 2 | _ => 3 ===>
  ∀ (s : String) (r : Nat), r = Blaster.dite' ("a" = s) (fun _ => 1) (fun _ => 3)

end Tests.ElimMatch
