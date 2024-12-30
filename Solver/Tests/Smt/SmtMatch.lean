import Lean
import Solver.Command.Syntax
import Solver.Tests.Utils


/-! ## Test objectives to validate "match" to smt ite translation -/

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

