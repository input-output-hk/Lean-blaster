import Lean
import Solver.Command.Syntax
import Solver.Tests.Utils


namespace Tests.SmtMatch

/-! ## Test objectives to validate "match/recursor" to smt ite translation -/

/-! Test cases to validate match to smt ite translation -/

def namedPatternInt (x : Int) (y : Option Int) : Nat :=
 match x, y with
 | _ , none => 1
 | Int.ofNat p@Nat.zero, _ => p + 2
 | _, some (Int.ofNat Nat.zero) => 3
 | Int.ofNat (Nat.succ Nat.zero), some t => Int.toNat t + 2
 | _, some (Int.ofNat (Nat.succ Nat.zero)) => Int.toNat x + 3
 | Int.ofNat (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))), some z => n + Int.toNat z
 | r@(Int.ofNat (Nat.succ (Nat.succ n1))),
   some (Int.ofNat t@(Nat.succ (Nat.succ q@(Nat.succ p@(Nat.succ ((Nat.succ n2))))))) =>
     ((Int.toNat r) + n1 + n2) * p * q * t
 | Int.negSucc Nat.zero, _ => 4
 | _, some (Int.negSucc Nat.zero) => 5
 | Int.negSucc p@(Nat.succ q@(Nat.succ Nat.zero)), _ => 6 + p + q
 | _, some (Int.negSucc (Nat.succ Nat.zero)) => 7
 | Int.negSucc q@(Nat.succ (Nat.succ p@(Nat.succ (Nat.succ n)))), _ => n + p + q + 1
 | _, some (Int.negSucc (Nat.succ q@(Nat.succ p@(Nat.succ r@(Nat.succ ((Nat.succ n))))))) => n + p + q + r + 2
 | p@(Int.ofNat (Nat.succ (Nat.succ n))), _ => (Int.toNat p + n) * 6
 | _, some (Int.negSucc (Nat.succ (Nat.succ n))) => n + 7
 | Int.negSucc (Nat.succ n), _ => n + 8


#solve [∀ (x : Int) (y : Option Int), y.isNone → namedPatternInt x y = 1]

#solve [∀ (x : Int) (y : Option Int), x = 0 → ¬ y.isNone → namedPatternInt x y = 2]

#solve [∀ (x : Int) (y : Option Int), x ≠ 0 → y = some 0 → namedPatternInt x y = 3]

#solve [∀ (x t : Int) (y : Option Int),
          x = 1 → y = some t → t ≠ 0 → namedPatternInt x y = Int.toNat t + 2]

#solve [∀ (x t : Int) (y : Option Int),
          x ≠ 1 → x ≠ 0 → y = some t → t = 1 → namedPatternInt x y = Int.toNat x + 3]

#solve [∀ (x t : Int) (y : Option Int),
        x ≥ 4 → y = some t → t > 1 → namedPatternInt x y = Int.toNat x - 4 + Int.toNat t]

#solve [∀ (x t : Int) (y : Option Int),
          x ≥ 2 → x < 4 → y = some t → t ≥ 5 →
           let r := Int.toNat x;
           let n1 := Int.toNat x - 2;
           let n2 := Int.toNat t - 5;
           let p := n2 + 2;
           let q := n2 + 3;
            namedPatternInt x y = (r + n1 + n2) * p * q * (Int.toNat t)]

#solve [∀ (x t : Int) (y : Option Int),
          x = -1 → y = some t → t > 1 → namedPatternInt x y = 4]

#solve [∀ (x t : Int) (y : Option Int),
          (x < -1 ∨ x = 3) → y = some t → t = -1 → namedPatternInt x y = 5]

#solve [∀ (x t : Int) (y : Option Int),
          x = -3 → y = some t → (t > 1 ∨ t < -1) →
          let p := Int.toNat (Int.neg x) - 1;
          let q := p - 1;
          namedPatternInt x y = 6 + p + q]

#solve [∀ (x t : Int) (y : Option Int),
          (x = -2 ∨ x < -3 ∨ x = 3) → y = some t → t = -2 → namedPatternInt x y = 7]

#solve [∀ (x t : Int) (y : Option Int),
          x ≤ -5 → y = some t → t < -2 →
          let n := Int.neg x - 5;
          let p := n + 2
          let q := n + 4
          namedPatternInt x y = n + p + q + 1]

#solve [∀ (x t : Int) (y : Option Int),
          x < -1 → (x = -2 ∨ x = -4) → y = some t → t ≤ -6 →
          let n := Int.neg t - 6;
          let r := n + 2;
          let p := n + 3
          let q := n + 4
          namedPatternInt x y = n + p + q + r + 2]


#solve [∀ (x t : Int) (y : Option Int),
          x ≥ 2 →
          x < 4 →
          y = some t →
          ((t < 5 ∧ t > 1) ∨ (t > -6 ∧ t < -2)) →
          let p := Int.toNat x;
          let n := p - 2
          namedPatternInt x y = (p + n) * 6]


#solve [∀ (x t : Int) (y : Option Int),
          y = some t →
          (x = -2 ∨ x = -4) →
          t > -6 →
          t ≤ -3 →
          let n := Int.neg t - 3
          namedPatternInt x y = n + 7]

#solve [∀ (x t : Int) (y : Option Int),
          y = some t →
          (x = -2 ∨ x = -4) →
          t > -3 →
          t < -2 →
          let n := Int.neg t - 3
          namedPatternInt x y = n + 8]


def isNil (x : List Nat) : Bool :=
  match x with
  | _head :: _tail => false
  | [] => true

#solve [∀ (xs : List Nat), isNil xs → List.length xs = 0]


/-! Test cases to validate casesOn recursor application to smt ite translation -/

structure POSIXTime where
    time : Nat
deriving BEq

structure VerificationKeyHash where
    hash : Nat
deriving BEq

-- NOTE deriving BEq uses recursor to derive the == instance
inductive Purpose
 | Minting
 | Spending
 | Rewarding
deriving BEq

structure ValidityRange where
    upper_bound : Nat
    lower_bound : Nat
deriving BEq

structure Tx (α : Type) where
    values : Option α
    signatories : Option VerificationKeyHash
    validity_range : ValidityRange
deriving BEq

structure ScriptContext where
    purpose : Purpose
    transaction : Tx Nat
deriving BEq

#solve [∀ (x y : POSIXTime), x == y → y == x]

#solve [∀ (x y : Purpose), x == y → y == x]

#solve [∀ (x y : ValidityRange), x == y → y == x]

#solve [∀ (x y : Tx Nat), x == y → y == x]

#solve [∀ (x y : ScriptContext), x == y → y == x]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose != Purpose.Minting]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose != Purpose.Rewarding]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose != Purpose.Spending]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose != Purpose.Rewarding]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose != Purpose.Spending]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose != Purpose.Minting]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose == Purpose.Spending]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose == Purpose.Minting]

#solve [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose == Purpose.Rewarding]


inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | yellow : Color → Color
  | black : Color
  | green : Color → Color
  | white : Color
  deriving BEq

def isRed (c : Color) : Bool :=
 match c with
 | Color.red _ => true
 | _ => false

def isBlue (c : Color) : Bool :=
 match c with
 | Color.red _ => true
 | _ => false

def isYellow (c : Color) : Bool :=
 match c with
 | Color.yellow _ => true
 | _ => false

def isGreen (c : Color) : Bool :=
 match c with
 | Color.green _ => true
 | _ => false

#solve [∀ (x y : Color), x == y → x == Color.transparent → y == Color.transparent ]

#solve [∀ (x y z : Color), x == y → x == Color.transparent → y != Color.red z ]

#solve [∀ (x y z : Color), x == y → x == Color.transparent → y != Color.blue z ]

#solve [∀ (x y z : Color), x == y → x == Color.transparent → y != Color.yellow z ]

#solve [∀ (x y z : Color), x == y → x == Color.transparent → y != Color.green z ]

#solve [∀ (x y : Color), x == y → x == Color.transparent → y != Color.black ]

#solve [∀ (x y : Color), x == y → x == Color.transparent → y != Color.white ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.transparent ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.blue z ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.yellow z ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.green z ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.black ]

#solve [∀ (x y z : Color), x == y → x == Color.red z → y != Color.white ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.transparent ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.red z ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.yellow z ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.green z ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.black ]

#solve [∀ (x y z : Color), x == y → x == Color.blue z → y != Color.white ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.transparent ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.red z ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.blue z ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.green z ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.black ]

#solve [∀ (x y z : Color), x == y → x == Color.yellow z → y != Color.white ]


#solve [∀ (x y : Color), x == y → x == Color.white → y == Color.white ]

#solve [∀ (x y z : Color), x == y → x == Color.white → y != Color.red z ]

#solve [∀ (x y z : Color), x == y → x == Color.white → y != Color.blue z ]

#solve [∀ (x y z : Color), x == y → x == Color.white → y != Color.yellow z ]

#solve [∀ (x y z : Color), x == y → x == Color.white → y != Color.green z ]

#solve [∀ (x y : Color), x == y → x == Color.white → y != Color.black ]

#solve [∀ (x y : Color), x == y → x == Color.white → y != Color.transparent ]

#solve [∀ (x y : Color), x == y → x == Color.black → y == Color.black ]

#solve [∀ (x y z : Color), x == y → x == Color.black → y != Color.red z ]

#solve [∀ (x y z : Color), x == y → x == Color.black → y != Color.blue z ]

#solve [∀ (x y z : Color), x == y → x == Color.black → y != Color.yellow z ]

#solve [∀ (x y z : Color), x == y → x == Color.black → y != Color.green z ]

#solve [∀ (x y : Color), x == y → x == Color.black → y != Color.white ]

#solve [∀ (x y : Color), x == y → x == Color.black → y != Color.transparent ]

#solve [∀ (x y : Color), x == y → isRed x → isRed y]

#solve [∀ (x y : Color), x == y → isBlue x → isBlue y]

#solve [∀ (x y : Color), x == y → isYellow x → isYellow y]

#solve [∀ (x y : Color), x == y → isGreen x → isGreen y]


/-! # Test cases to ensure that counterexample are properly detected -/


#solve (gen-cex: 0) (falsified-result: 1) [∀ (x : Int) (y : Option Int), y.isNone → namedPatternInt x y ≠ 1]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x : Int) (y : Option Int), x = 0 → ¬ y.isNone → namedPatternInt x y ≠ 2]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x : Int) (y : Option Int), x ≠ 0 → y = some 0 → namedPatternInt x y ≠ 3]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x t : Int) (y : Option Int), x ≠ 1 ∨ y.isNone ∨ (y = some t ∧ t = 0) → namedPatternInt x y = Int.toNat t + 2]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x t : Int) (y : Option Int), x = 1 ∨ x = 0 ∨ y.isNone ∨ (y = some t ∧ t ≠ 1) → namedPatternInt x y = Int.toNat x + 3]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (xs : List Nat), ¬ isNil xs → List.length xs = 0]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : POSIXTime), x == y → y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Purpose), x == y → y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : ValidityRange), x == y → y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Tx Nat), x == y → y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : ScriptContext), x == y → y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose == Purpose.Minting]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose == Purpose.Rewarding]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose == Purpose.Spending]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose == Purpose.Rewarding]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose == Purpose.Spending]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose == Purpose.Minting]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Spending → y.purpose != Purpose.Spending]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Minting → y.purpose != Purpose.Minting]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : ScriptContext), x == y → x.purpose == Purpose.Rewarding → y.purpose != Purpose.Rewarding]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → x == Color.transparent → y != Color.transparent ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.transparent → y == Color.red z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.transparent → y == Color.blue z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.transparent → y == Color.yellow z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.red z → y == Color.transparent ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.red z → y == Color.black ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.red z → y == Color.white ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.red z → y == Color.blue z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.red z → y == Color.yellow z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.blue z → y == Color.transparent ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.blue z → y == Color.black ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.blue z → y == Color.white ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.blue z → y == Color.red z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.blue z → y == Color.yellow z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.yellow z → y == Color.transparent ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.yellow z → y == Color.black ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.yellow z → y == Color.white ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.yellow z → y == Color.red z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y z : Color), x == y → x == Color.yellow z → y == Color.blue z ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → isRed x → ¬ isRed y]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → isBlue x → ¬ isBlue y]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → isYellow x → ¬ isYellow y]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → x != Color.black ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → x != Color.white ]

#solve (gen-cex: 0) (falsified-result: 1)
  [∀ (x y : Color), x == y → x != Color.transparent ]

end Tests.SmtMatch
