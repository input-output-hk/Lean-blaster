import Lean

namespace Blaster.FiniteField

/-- Bounded repeated squaring. The caller supplies enough binary digits; the
correctness theorem, rather than the executable result, licenses its use in proofs. -/
def powMod (fuel a e n : Nat) : Nat :=
  match fuel with
  | 0 => 1 % n
  | fuel + 1 =>
    if e = 0 then 1 % n else
      let r := powMod fuel a (e / 2) n
      if e % 2 = 0 then r * r % n else r * r % n * a % n

/-- Repeated squaring computes the mathematical power residue when the exponent
fits in the supplied number of binary digits. No native evaluation is trusted. -/
theorem powMod_eq (fuel a e n : Nat) (h : e < 2 ^ fuel) :
    powMod fuel a e n = a ^ e % n := by
  induction fuel generalizing e with
  | zero =>
    have : e = 0 := by simpa using h
    subst e
    rfl
  | succ fuel ih =>
    have he : e / 2 < 2 ^ fuel := by
      rw [Nat.pow_succ] at h
      omega
    rw [powMod]
    split
    next hz => simp [hz]
    next hz =>
      rw [ih _ he]
      split
      next even =>
        have heq : e = e / 2 + e / 2 := by omega
        conv => rhs; rw [heq, Nat.pow_add, Nat.mul_mod]
      next odd =>
        have heq : e = (e / 2 + e / 2) + 1 := by omega
        conv => rhs; rw [heq, Nat.pow_succ, Nat.pow_add]
        simp only [Nat.mul_mod, Nat.mod_mod]

end Blaster.FiniteField
