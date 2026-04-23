import Blaster

/-- Commutativity of addition -/
theorem addComm : ∀ (n m : Nat), n + m = m + n := by blaster

/-- Zero is the additive identity -/
theorem zeroAdd : ∀ (n : Nat), 0 + n = n := by blaster

-- A falsified case: wrong on purpose
#blaster (solve-result: 1) [∀ (x : Nat), x + 1 = x]

-- An undetermined case (timeout)
#blaster (timeout: 2) (solve-result: 2) [∀ (x : Nat), 0 < 2^x]
