import Lean
import Blaster

namespace Test.SmtPartialUnsafe

mutual
  partial def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n

  partial def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end

/--
error: normConst: partial function not supported Test.SmtPartialUnsafe.isEven !!!
-/
#guard_msgs in
#blaster (only-optimize: 1) [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

unsafe def powerN (a : Int) (n : Nat) : Int :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => a * powerN a n'

/--
error: normConst: unsafe definition not supported Test.SmtPartialUnsafe.powerN !!!
-/
#guard_msgs in
#blaster (only-optimize: 1) [∀ (x : Int) (n : Nat), powerN x n = Int.pow x n]

partial def powerN' (a : Int) (n : Nat) : Int :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => a * powerN' a n'

/--
error: normConst: partial function not supported Test.SmtPartialUnsafe.powerN' !!!
-/
#guard_msgs in
#blaster (only-optimize: 1) [∀ (x : Int) (n : Nat), powerN' x n = Int.pow x n]

end Test.SmtPartialUnsafe
