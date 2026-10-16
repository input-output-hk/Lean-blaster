import Blaster

/-! ## Goal binders stay aligned when `blaster` prepends a local Prop axiom of the module.
    The axiom holds for the whole module, hence this separate file. -/

axiom localAx : ∀ k : Int, k + 0 = k

example : ∀ (m n : Int), m + n = n + m := by blaster
example : ∀ (m n : Nat), m + n = n + m := by blaster
example : ∀ (a b : Bool), (a && b) = (b && a) := by blaster
example : ∀ (a b : Prop), (a ∧ b) = (b ∧ a) := by blaster
example : ∀ (a b : Prop), a → b → a ∧ b := by blaster
example : (2 : Int) + 3 = 5 := by blaster
example : let x := (2 : Int); ∀ (y : Int), x + y = y + 2 := by blaster
example : (∀ (m n : Int), m + n = n + m) = True := by blaster
example : (∀ (a b : Prop), (a ∧ b) = (b ∧ a)) = (∀ (a b : Prop), (b ∧ a) = (a ∧ b)) := by blaster
