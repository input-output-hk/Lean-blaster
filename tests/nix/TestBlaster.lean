import Blaster

-- Propositional logic
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by blaster

-- Linear arithmetic
example (x y : Nat) (h1 : x + y > 0) (h2 : y > 0) : x + y > 0 := by blaster

-- De Morgan
example (p q : Prop) (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by blaster
