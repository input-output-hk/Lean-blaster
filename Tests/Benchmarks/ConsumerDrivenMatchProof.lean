import Blaster

namespace ConsumerDrivenMatchProof

set_option maxHeartbeats 0

inductive Data where
  | leaf : Nat → Data
  | pair : Data → Data → Data

def encode : Option Nat → Data
  | none => .leaf 0
  | some n => .leaf (n + 1)

def pack : List (Option Nat) → Data
  | [] => .leaf 99
  | x :: xs => .pair (encode x) (pack xs)

def first : Data → Data
  | .pair x _ => x
  | x => x

#blaster (preserve-constructor-choices: 1)
  [∀ a b c d : Option Nat, first (pack [a, b, c, d]) = encode a]

def firstLeaf : Data → Nat
  | .pair (.leaf n) _ => n
  | _ => 999

def encodedNat : Option Nat → Nat
  | none => 0
  | some n => n + 1

theorem firstLeaf_correct (a b c d : Option Nat) :
    firstLeaf (pack [a, b, c, d]) = encodedNat a := by
  cases a <;> rfl

end ConsumerDrivenMatchProof
