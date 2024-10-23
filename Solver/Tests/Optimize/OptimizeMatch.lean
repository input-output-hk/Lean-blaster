import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.UnfoldMatch

/-! ## Test objectives to validate the normalization of "match" expressions to "ite" -/


/-! Test cases to validate when match expression must be normalized. -/

-- ∀ (a b c : Bool), cond c a b = true ===> ∀ (a b c : Bool), true = ((a || !c) && (b || c))
#testOptimize ["MatchToITE_1"] ∀ (a b c : Bool), cond c a b = true ===>
                               ∀ (a b c : Bool), true = ((a || !c) && (b || c))

-- ∀ (a b c : Bool), cond c a b ===>
-- ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)
#testOptimize ["MatchToITE_2"] ∀ (a b c : Bool), cond c a b ===>
                               ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)


def isNilOne (x : List Nat) : Bool :=
  match x with
  | [] => true
  | _ => false

-- ∀ (x : List Nat), isNilOne x = true ===>
-- ∀ (x : List Nat), [] = x
#testOptimize ["MatchToITE_3"] ∀ (x : List Nat), isNilOne x = true ===>
                               ∀ (x : List Nat), [] = x

def isNilTwo (x : List Nat) : Bool := if let [] := x then true else false
-- NOTE: `if let [] := x ...` is a syntactic suger for a match

-- ∀ (x : List Nat), isNilTwo x = true ===>
-- ∀ (x : List Nat), [] = x
#testOptimize ["MatchToITE_4"] ∀ (x : List Nat), isNilTwo x = true ===>
                               ∀ (x : List Nat), [] = x


def ite_sign (x : Int) : Int :=
  if 1 ≤ x then 1
  else if 0 = x then 0 else -1

-- ∀ (x : Int), Int.sign x = ite_sign ===> True
#testOptimize ["MatchToITE_5"] ∀ (x : Int), Int.sign x = ite_sign x ===> True

def ite_abs (x : Int) : Nat :=
  if 0 ≤ x then Int.toNat x else (Int.toNat (- x) - 1) + 1

-- ∀ (x : Int), Int.natAbs x = ite_abs ===> True
#testOptimize ["MatchToITE_6"] ∀ (x : Int), Int.natAbs x = ite_abs x ===> True

def ite_negNat (x : Nat) : Int :=
  if 0 = x then 0 else -(Int.ofNat ((x - 1) + 1))

-- ∀ (x : Nat), Int.negOfNat x = ite_negNat x ===> True
#testOptimize ["MatchToITE_7"] ∀ (x : Nat), Int.negOfNat x = ite_negNat x ===> True

def matchDiscrNat (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | Nat.zero, _ => 0
 | _, Nat.zero => 1
 | Nat.succ Nat.zero, _ => y + 2
 | _, Nat.succ Nat.zero => x + 3
 | Nat.succ (Nat.succ (Nat.succ (Nat.succ n))), z => n + z
 | Nat.succ n1, Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n2))))) => n1 * n2
 | Nat.succ (Nat.succ n), _ => n * 6

def iteDiscrNat (x : Nat) (y : Nat) : Nat :=
  if x = 0 then 0
  else if y = 0 then 1
  else if x = 1 then y + 2
  else if y = 1 then x + 3
  else if x ≥ 4 then (x - 4) + y
  else if x ≥ 1 ∧ y ≥ 5 then (y - 5) * (x - 1)
  else (x - 2) * 6

-- ∀ (x y : Nat), matchDiscrNat x y = iteDiscrNat x y ===> True
#testOptimize ["MatchToITE_8"] ∀ (x y : Nat), matchDiscrNat x y = iteDiscrNat x y ===> True


def matchDiscrInt (x : Int) (y : Int) : Nat :=
 match x, y with
 | Int.ofNat Nat.zero, _ => 0
 | _, Int.ofNat Nat.zero => 1
 | Int.ofNat (Nat.succ Nat.zero), _ => Int.toNat y + 2
 | _, Int.ofNat (Nat.succ Nat.zero) => Int.toNat x + 3
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), z => n + Int.toNat z
 | z, Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n)))))) => n * Int.toNat z
 | Int.negSucc Nat.zero, _ => 4
 | _, Int.negSucc Nat.zero => 5
 | Int.negSucc (Nat.succ (Nat.succ Nat.zero)), _ => 6
 | _, Int.negSucc (Nat.succ Nat.zero) => 7
 | Int.negSucc (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), _ => n + 1
 | _, Int.negSucc (Nat.succ (Nat.succ (Nat.succ (Nat.succ ((Nat.succ n)))))) => n + 2
 | Int.ofNat (Nat.succ (Nat.succ n)), _ => n * 6
 | _, Int.negSucc (Nat.succ (Nat.succ n)) => n * 7
 | Int.negSucc (Nat.succ n), _ => n * 8


def iteDiscrInt (x : Int) (y : Int) : Nat :=
  if x = 0 then 0
  else if y = 0 then 1
  else if x = 1 then Int.toNat y + 2
  else if y = 1 then Int.toNat x + 3
  else if x ≥ 4 then (Int.toNat x - 4) + Int.toNat y
  else if y ≥ 5 then (Int.toNat y - 5) * Int.toNat x
  else if x = -1 then 4
  else if y = -1 then 5
  else if x = -3 then 6
  else if y = -2 then 7
  else if x ≤ -5 then ((Int.toNat (-x)) - 5) + 1
  else if y ≤ -6 then ((Int.toNat (-y)) - 6) + 2
  else if x ≥ 2 then (Int.toNat x - 2) * 6
  else if y ≤ -3 then (Int.toNat (-y) - 3) * 7
  else (Int.toNat (-x) - 2) * 8

-- ∀ (x y : Int), matchDiscrInt x y = iteDiscrInt x y ===> True
#testOptimize ["MatchToITE_9"] ∀ (x y : Int), matchDiscrInt x y = iteDiscrInt x y ===> True

def matchMultiEq (x : Int) (y : Nat) (z : Option Nat) : Nat :=
 match x, y, z with
 | Int.ofNat Nat.zero, Nat.zero, _ => 0
 | 0, _, some Nat.zero => 1
 | _, Nat.succ n, some 1 => n
 | Int.ofNat (Nat.succ Nat.zero), _, none => y + 1
 | _, Nat.succ n, none => n + Int.toNat x
 | Int.negSucc 0, _, some 2 => y * 2
 | 3, (Nat.succ (Nat.succ n)), some 3 => n * 3
 | Int.negSucc (Nat.succ (Nat.succ n1)), (Nat.succ (Nat.succ (Nat.succ n2))), some 4 => (n1 + n2) * 4
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ n1))), (Nat.succ (Nat.succ n2)), some 4 => n1 * n2 * 4
 | Int.ofNat n, _, some 5 => (n + y) * 5
 | _, _, _ => 10

def iteMultiEq (x : Int) (y : Nat) (z : Option Nat) : Nat :=
 if x = 0 ∧ y = 0 then 0
 else if x = 0 ∧ z = some 0 then 1
 else if y ≥ 1 ∧ z = some 1 then y - 1
 else if x = 1 ∧ z = none then y + 1
 else if y ≥ 1 ∧ z = none then (y - 1) + Int.toNat x
 else if x = - 1 ∧ z = some 2 then y * 2
 else if (x = 3 ∧ y ≥ 2) ∧ z = some 3 then (y - 2) * 3
 else if (x ≤ -3 ∧ y ≥ 3) ∧ z = some 4 then ((Int.toNat (-x) - 3) + (y - 3)) * 4
 else if (x ≥ 3 ∧ y ≥ 2) ∧ z = some 4 then (Int.toNat x - 3) * (y - 2) * 4
 else if x ≥ 0 ∧ z = some 5 then (Int.toNat x + y) * 5
 else 10

-- ∀ (x : Int) (y : Nat) (z : Option Nat), matchMultiEq x y z = iteMultiEq x y z ===> True
-- NOTE: we need to check how to order list of ∧ to guarantee structural equivalence, i.e.,
-- `x ≤ -3 ∧ y ≥ 3 ∧ z = some 4` is internally represented as `x ≤ -3 ∧ (y ≥ 3 ∧ z = some 4)`
-- Hence, we need to explicitly place the parentheses here for the test to be successful.
#testOptimize ["MatchToITE_10"] ∀ (x : Int) (y : Nat) (z : Option Nat), matchMultiEq x y z = iteMultiEq x y z ===> True

def matchDiscrList (x : List Int) (y : List Nat) : Nat :=
 match x, y with
 | [], [] => 0
 | [1], [1] => 1
 | [1, 2, 3], [1, 2, 3] => 2
 | [-2, -1, 0], [2, 1, 0] => 3
 | _, [4, 5, 6] => List.length x + 4
 | [-4, -6, 3], z => List.length z + 7
 | s, t => List.length s + List.length t + 8

def iteDiscrList (x : List Int) (y : List Nat) : Nat :=
 if x = [] ∧ y = [] then 0
 else if x = [1] ∧ y = [1] then 1
 else if x = [1, 2, 3] ∧ y = [1, 2, 3] then 2
 else if x = [-2, -1, 0] ∧ y = [2, 1, 0] then 3
 else if y = [4, 5, 6] then List.length x + 4
 else if x = [-4, -6, 3] then List.length y + 7
 else List.length x + List.length y + 8

-- ∀ (x : List Int) (y : List Nat), matchDiscrList x y = iteDiscrList x y ===> True
#testOptimize ["MatchToITE_11"] ∀ (x : List Int) (y : List Nat), matchDiscrList x y = iteDiscrList x y ===> True


def matchDiscrAbstract (x : Option α) (y : Option α) : Nat :=
 match x, y with
 | none, none => 0
 | _, none => 1
 | none, _ => 2
 | _, _ => 3

def iteDiscrAbstract [DecidableEq α] (x : Option α) (y : Option α) : Nat :=
 if x = none ∧ y = none then 0
 else if y = none then 1
 else if x = none then 2
 else 3

-- ∀ (α : Type) (x y : Option α), [DecidableEq α] → matchDiscrAbstract x y = iteDiscrAbstract x y ===> True
-- Test case to check if Decidable instance can be synthesized properly on generic sort.
#testOptimize ["MatchToITE_12"] ∀ (α : Type) (x y : Option α),
                                  [DecidableEq α] → matchDiscrAbstract x y = iteDiscrAbstract x y ===> True


def embeddedMatch (x : Option Nat) (y : Option Nat) : Nat :=
  match x, y with
  | none, none => 0
  | some Nat.zero, some 0 => 1
  | _, some 0 => 2
  | some 0, _ => 3
  | some 1, some 1 => 4
  | some 2, some 2 => 5
  | _, some 3 =>
     match x with -- match expected not to be normalized
     | none => 6
     | some (Nat.succ n) => n + 5
     | some n => n + 6
  | some 4, _ =>
     match y with
     | none => 7
     | some 0 => 8
     | _ => 9
  | _, _ => 10

def embeddedIte (x : Option Nat) (y : Option Nat) : Nat :=
 if x = none ∧ y = none then 0
 else if x = some 0 ∧ y = some 0 then 1
 else if y = some 0 then 2
 else if x = some 0 then 3
 else if x = some 1 ∧ y = some 1 then 4
 else if x = some 2 ∧ y = some 2 then 5
 else if y = some 3 then match x with
                         | none => 6
                         | some (Nat.succ n) => n + 5
                         | some n => n + 6
 else if x = some 4 then if y = none then 7 else if y = some 0 then 8 else 9
 else 10

-- ∀ (x y : Option Nat), embeddedMatch x y = embeddedIte x y ===> true
#testOptimize ["MatchToITE_13"] ∀ (x y : Option Nat), embeddedMatch x y = embeddedIte x y ===> True


def namedPatternNat (x : Nat) (y : Nat) : Nat :=
 match x, y with
 | Nat.zero, _ => 0
 | _, Nat.zero => 1
 | Nat.succ Nat.zero, _ => y + 2
 | _, Nat.succ Nat.zero => x + 3
 | r@(Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ n)))), z => n + p + q + r + z
 | r@(Nat.succ (Nat.succ n1)), Nat.succ q@(Nat.succ p@(Nat.succ (Nat.succ ((Nat.succ n2))))) => (r + n1) * n2 * p * q
 | q@(Nat.succ (Nat.succ n)), _ => q * n * 6

def iteNamedPatternNat (x : Nat) (y : Nat) : Nat :=
  if x = 0 then 0
  else if y = 0 then 1
  else if x = 1 then y + 2
  else if y = 1 then x + 3
  else if x ≥ 4 then y + (x + (((x - 2) + (x - 4)) + (x - 1)))
  else if x ≥ 2 ∧ y ≥ 5 then (((x + (x - 2)) * (y - 5)) * (y - 2)) * (y - 1)
  else (x * (x - 2)) * 6

-- ∀ (x y : Option Nat), namedPatternNat x y = iteNamedPatternNat x y ===> true
#testOptimize ["MatchToITE_14"] ∀ (x y : Nat), namedPatternNat x y = iteNamedPatternNat x y ===> True

def namedPatternInt (x : Int) (y : Int) : Nat :=
 match x, y with
 | Int.ofNat Nat.zero, _ => 0
 | _, Int.ofNat Nat.zero => 1
 | Int.ofNat (Nat.succ Nat.zero), _ => Int.toNat y + 2
 | _, Int.ofNat (Nat.succ Nat.zero) => Int.toNat x + 3
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), z => n + Int.toNat z
 | r@(Int.ofNat (Nat.succ (Nat.succ n1))), Int.ofNat (Nat.succ (Nat.succ q@(Nat.succ p@(Nat.succ ((Nat.succ n2)))))) =>
     ((Int.toNat r) + n1) * n2 * p * q
 | Int.negSucc Nat.zero, _ => 4
 | _, Int.negSucc Nat.zero => 5
 | Int.negSucc p@(Nat.succ q@(Nat.succ Nat.zero)), _ => 6 * p * q
 | _, Int.negSucc (Nat.succ Nat.zero) => 7
 | Int.negSucc q@(Nat.succ (Nat.succ p@(Nat.succ (Nat.succ n)))), _ => n + p + q + 1
 | _, Int.negSucc (Nat.succ q@(Nat.succ p@(Nat.succ r@(Nat.succ ((Nat.succ n)))))) => n + p + q + r + 2
 | p@(Int.ofNat (Nat.succ (Nat.succ n))), _ => Int.toNat p * n * 6
 | _, Int.negSucc (Nat.succ (Nat.succ n)) => n * 7
 | Int.negSucc (Nat.succ n), _ => n * 8


def iteNamedPatternInt (x : Int) (y : Int) : Nat :=
  if x = 0 then 0
  else if y = 0 then 1
  else if x = 1 then Int.toNat y + 2
  else if y = 1 then Int.toNat x + 3
  else if x ≥ 4 then (Int.toNat x - 4) + Int.toNat y
  else if x ≥ 2 ∧ y ≥ 5 then ((Int.toNat x) + (Int.toNat x - 2)) * (Int.toNat y - 5) * (Int.toNat y - 3) * (Int.toNat y - 2)
  else if x = -1 then 4
  else if y = -1 then 5
  else if x = -3 then 12 -- 6 * p * q must reduced to 12
  else if y = -2 then 7
  else if x ≤ -5 then ((Int.toNat (-x)) - 5) + ((Int.toNat (-x)) - 3) + (Int.toNat (-x) - 1) + 1
  else if y ≤ -6 then ((Int.toNat (-y)) - 6) + ((Int.toNat (-y)) - 3) + ((Int.toNat (-y)) - 2) + ((Int.toNat (-y)) - 4) + 2
  else if x ≥ 2 then (Int.toNat x) * (Int.toNat x - 2) * 6
  else if y ≤ -3 then (Int.toNat (-y) - 3) * 7
  else (Int.toNat (-x) - 2) * 8

-- ∀ (x y : Int), namedPatternInt x y = iteNamedPatternInt x y ===> True
#testOptimize ["MatchToITE_15"] ∀ (x y : Int), namedPatternInt x y = iteNamedPatternInt x y ===> True


def namedPatternList (x : List Int) (y : List Nat) : Nat :=
 match x, y with
 | [], [] => 0
 | [1], [1] => 1
 | 1 :: q@([4, 5]), 1 :: p@([2, 3]) => 2 + List.length p + List.length q
 | q@([-2, -1, 0]), 2 :: p@([1, 0]) => 3 + List.length q - List.length p
 | _, p@(4 :: q@([5, 6])) => List.length x + List.length p + List.length q
 | [-4, -6, 3], z => List.length z + 7
 | s, t => List.length s + List.length t + 8

def iteNamedPatternList (x : List Int) (y : List Nat) : Nat :=
 if x = [] ∧ y = [] then 0
 else if x = [1] ∧ y = [1] then 1
 else if x = [1, 4, 5] ∧ y = [1, 2, 3] then 6
 else if x = [-2, -1, 0] ∧ y = [2, 1, 0] then 4
 else if y = [4, 5, 6] then List.length x + 5
 else if x = [-4, -6, 3] then List.length y + 7
 else List.length x + List.length y + 8

-- ∀ (x : List Int) (y : List Nat), matchDiscrList x y = iteDiscrList x y ===> True
#testOptimize ["MatchToITE_16"] ∀ (x : List Int) (y : List Nat), namedPatternList x y = iteNamedPatternList x y ===> True


def iteReducedMatchNil (x : List Int) (y : List Nat) : Nat :=
 if x = [] ∧ y = [] then 0
 else if y = [4, 5, 6] then List.length x + 5
 else List.length x + List.length y + 8

-- ∀ (y : List Nat), namedPatternList List.nil y = iteReducedMatchNil List.nil y ===> True
#testOptimize ["MatchToITE_17"] ∀ (y : List Nat), namedPatternList List.nil y = iteReducedMatchNil List.nil y ===> True


def iteReducedMatchCons (x : List Int) (y : List Nat) : Nat :=
 if y = [4, 5, 6] then List.length x + 5
 else List.length x + List.length y + 8

-- ∀ (m n : Nat) (y : List Nat), namedPatternList [m, n] y = iteReducedMatchCons [m, n] y ===> True
#testOptimize ["MatchToITE_18"] ∀ (m n : Nat) (y : List Nat), namedPatternList [m, n] y = iteReducedMatchCons [m, n] y ===> True


/-! Test cases to validate when match expression must NOT be normalized. -/


def condUnchanged (a : Option Bool) (b : Bool) (c : Bool) : Bool :=
 match a with
 | none => false
 | some d => if d then b else c

-- ∀ (a : Option Bool) (b c : Bool), condUnchanged a b c ===>
-- ∀ (a : Option Bool) (b c : Bool),
-- true = (match a with
--         | none => false
--         | some d => (b || !d) && (c || d)
#testOptimize ["MatchToITEUnchanged_1"] ∀ (a : Option Bool) ( b c : Bool), condUnchanged a b c ===>
                                        ∀ (a : Option Bool) ( b c : Bool),
                                            true = (match a with
                                                    | none => false
                                                    | some d => (b || !d) && (c || d))

def isNilUnchanged (x : List Nat) : Bool :=
  match x with
  | _head :: _tail => false
  | [] => true

-- ∀ (x : List Nat), isNilUnchanged x ===>
-- ∀ (x : List Nat), true = (match x with
--                           | _head :: _tail => false
--                           | [] => true )
#testOptimize ["MatchToITEUnchanged_2"] ∀ (x : List Nat), isNilUnchanged x ===>
                                        ∀ (x : List Nat), true = (match x with
                                                                  | _head :: _tail => false
                                                                  | [] => true )


def multiEqUnchanged (x : Int) (y : Nat) (z : Option Nat) : Nat :=
 match x, y, z with
 | Int.ofNat n, _, _ => n
 | _, Nat.succ n, none => n + Int.toNat x
 | Int.negSucc 0, _, some n => y * n
 | Int.negSucc (Nat.succ (Nat.succ n1)), (Nat.succ (Nat.succ (Nat.succ n2))), some (Nat.succ n3) => (n1 + n2) * n3
 | t, _, some n => (Int.toNat t + y) * n
 | _, _, _ => y

-- ∀ (x : Int) (y : Nat) (z: Option Nat), multiEqUnchanged x y z > y ===>
-- ∀ (x : Int) (y : Nat) (z: Option Nat),
-- y < (match x, y, z with
--      | Int.ofNat n, _, _ => n
--      | _, Nat.succ n, none => Nat.add n (Int.toNat x)
--      | Int.negSucc 0, _, some n => Nat.mul y n
--      | Int.negSucc (Nat.succ (Nat.succ n1)), (Nat.succ (Nat.succ (Nat.succ n2))), some (Nat.succ n3) => Nat.mul n3 (Nat.add n1 n2)
--      | t, _, some n => Nat.mul n (Nat.add y (Nat.toNat t))
--      | _, _, _ => y )
#testOptimize ["MatchToITEUnchanged_3"] ∀ (x : Int) (y : Nat) (z: Option Nat), multiEqUnchanged x y z > y ===>
                                        ∀ (x : Int) (y : Nat) (z: Option Nat),
                                          y < (match x, y, z with
                                               | Int.ofNat n, _, _ => n
                                               | _, Nat.succ n, none => Nat.add n (Int.toNat x)
                                               | Int.negSucc 0, _, some n => Nat.mul y n
                                               | Int.negSucc (Nat.succ (Nat.succ n1)),
                                                 (Nat.succ (Nat.succ (Nat.succ n2))),
                                                 some (Nat.succ n3) => Nat.mul n3 (Nat.add n1 n2)
                                               | t, _, some n => Nat.mul n (Nat.add y (Int.toNat t))
                                               | _, _, _ => y )


def discrListUnchanged (x : List Int) (y : List Nat) : Bool :=
 match x, y with
 | [], [] => true
 | [], _ => false
 | _, [] => false
 | 1 :: _, 1 :: _ => true
 | -2 :: xs, 2 :: ys => List.length xs == List.length ys
 | _ :: xs, _ :: ys => List.length xs == List.length ys

-- ∀ (x : List Int) (y : List Nat), discrListUnchanged x y ===>
-- ∀ (x : List Int) (y : List Nat),
--  true = ( match x, y with
--           | [], [] => true
--           | [], _ => false
--           | _, [] => false
--           | 1 :: _, 1 :: _ => true
--           | -2 :: xs, 2 :: ys => List.length xs == List.length ys
--           | _ :: xs, _ :: ys => List.length xs == List.length ys
#testOptimize ["MatchToITEUnchanged_4"] ∀ (x : List Int) (y : List Nat), discrListUnchanged x y ===>
                                        ∀ (x : List Int) (y : List Nat),
                                             true = ( match x, y with
                                                      | [], [] => true
                                                      | [], _ => false
                                                      | _, [] => false
                                                      | 1 :: _, 1 :: _ => true
                                                      | -2 :: xs, 2 :: ys => List.length xs == List.length ys
                                                      | _ :: xs, _ :: ys => List.length xs == List.length ys)


def discrAbstractUnchanged (x : List α) (y : Option α) : Bool :=
  match x, y with
  | [], none => true
  | _, none => false
  | [],_ => false
  | _, _ => true


-- ∀ (α : Type) (x : List α) (y : Option α), (discrAbstractUnchanged x y) ===>
-- ∀ (α : Type) (x : List α) (y : Option α),
--    true = ( match x, y with
--             | [], none => true
--             | _, none => false
--             | [],_ => false
--             | _, _ => true )
-- Test case to check that match expression is not normalized when DecidableEq instance cannot be synthesized.
-- We here used auxiliary function `discrAbstractUnchanged.match_1` created by Lean to check the result.
#testOptimize ["MatchToITEUnchanged_5"] ∀ (α : Type) (x : List α) (y : Option α), (discrAbstractUnchanged x y) ===>
                                        ∀ (α : Type) (x : List α) (y : Option α),
                                            true = ( discrAbstractUnchanged.match_1 (fun (_ : List α) (_ : Option α) => Bool) x y
                                                     (fun (_ : Unit) => true)
                                                     (fun (_ : List α) => false)
                                                     (fun (_ : Option α) => false)
                                                     (fun (_ : List α) (_ : Option α) => true) )


end Tests.UnfoldMatch
