import Blaster.FiniteField.Basic
import Blaster.FiniteField.PrimeOrder
import Blaster.FiniteField.PrimePower
import Init.Grind.Ring.Field

/-!
# Total operations on prime residue fields

The inverse uses the locally proved natural-number Fermat theorem, not a field
assumption or a solver. Repeated squaring computes the nonzero inverse; the
explicit zero branch is essential in characteristic two. All ring operations
and natural powers remain those of the nominal carrier in `Basic`.
-/

namespace Blaster.FiniteField.Residue

open Lean.Grind

variable {p : Nat}

/-- Natural powers on the nominal carrier agree with modular natural powers. -/
theorem rep_pow [NeZero p] (a : Residue p) (n : Nat) :
    (a ^ n).rep.val = a.rep.val ^ n % p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Semiring.pow_succ]
    change ((a ^ n).rep.val * a.rep.val) % p = _
    rw [ih, Nat.pow_succ, Nat.mod_mul_mod]

variable [PrimeModulus p]

/-- Total inverse, computed by bounded repeated squaring. Fuel `p` is more than
sufficient; the computation stops when the halved exponent reaches zero. -/
instance instInv : Inv (Residue p) := ⟨fun a =>
  if a = 0 then 0 else
    ⟨Fin.ofNat p (powMod p a.rep.val (p - 2) p)⟩⟩

/-- Division never inherits `Fin.div`: it multiplies by the total inverse. -/
instance instDiv : Div (Residue p) := ⟨fun a b => a * b⁻¹⟩

/-- Nonnegative integer powers reuse natural powers; negative powers invert
those same natural powers. In particular the zeroth power is always one. -/
instance instZPow : HPow (Residue p) Int (Residue p) := ⟨fun a n =>
  match n with
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹⟩

/-- Zero has inverse zero, including at modulus two. -/
theorem inv_zero : (0 : Residue p)⁻¹ = 0 := by
  change (if (0 : Residue p) = 0 then 0 else _) = 0
  rw [if_pos rfl]

/-- The executable inverse agrees with the mathematical Fermat power off zero. -/
theorem inv_eq_pow {a : Residue p} (ha : a ≠ 0) : a⁻¹ = a ^ (p - 2) := by
  change (if a = 0 then 0 else _) = _
  rw [if_neg ha]
  apply ext
  apply Fin.ext
  change powMod p a.rep.val (p - 2) p % p = _
  rw [powMod_eq p a.rep.val (p - 2) p
    (Nat.lt_of_le_of_lt (Nat.sub_le p 2) Nat.lt_two_pow_self), Nat.mod_mod, rep_pow]

/-- A nonzero representative below a prime is coprime to that prime. -/
theorem coprime_rep {a : Residue p} (ha : a ≠ 0) : Nat.Coprime a.rep.val p := by
  apply Nat.Coprime.symm
  apply Prime.coprime_of_not_dvd (PrimeModulus.prime (p := p))
  intro hd
  have hz : a.rep.val = 0 := Nat.eq_zero_of_dvd_of_lt hd a.rep.isLt
  apply ha
  apply ext
  exact Fin.ext hz

/-- Nontriviality follows from the lower bound in the primality evidence. -/
theorem zero_ne_one : (0 : Residue p) ≠ 1 := by
  intro h
  have hv := congrArg (fun a : Residue p => a.rep.val) h
  change 0 = 1 % p at hv
  rw [Nat.mod_eq_of_lt (PrimeModulus.prime (p := p)).one_lt] at hv
  contradiction

/-- Fermat's theorem supplies the inverse law without assuming a field. -/
theorem mul_inv_cancel {a : Residue p} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_eq_pow ha, CommSemiring.mul_comm, ← Semiring.pow_succ]
  have he : p - 2 + 1 = p - 1 := by have := PrimeModulus.two_le p; omega
  rw [he]
  apply ext
  apply Fin.ext
  rw [rep_pow]
  exact pow_pred_mod (PrimeModulus.prime (p := p)) (coprime_rep ha)

/-- Division is definitionally multiplication by the denominator's inverse. -/
theorem div_eq_mul_inv (a b : Residue p) : a / b = a * b⁻¹ := rfl

/-- A right inverse is unique, using only the ring and the proved inverse law. -/
theorem eq_inv_of_mul_eq_one {a b : Residue p} (h : a * b = 1) : a = b⁻¹ := by
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, Semiring.mul_zero] at h
    exact zero_ne_one h
  have hm := congrArg (fun x => x * b⁻¹) h
  simpa only [Semiring.mul_assoc, mul_inv_cancel hb, Semiring.mul_one,
    Semiring.one_mul] using hm

/-- Inversion fixes one; established before constructing the Field instance. -/
theorem inv_one : (1 : Residue p)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (Semiring.mul_one 1)).symm

/-- Inversion is involutive even at zero, without a circular Field assumption. -/
theorem inv_inv (a : Residue p) : a⁻¹⁻¹ = a := by
  by_cases ha : a = 0
  · rw [ha, inv_zero, inv_zero]
  · exact (eq_inv_of_mul_eq_one (mul_inv_cancel ha)).symm

/-- Integer natural casts preserve the existing natural powers definitionally. -/
theorem zpow_natCast (a : Residue p) (n : Nat) : a ^ (n : Int) = a ^ n := rfl

/-- Negating an integer exponent inverts the power, including exponent zero. -/
theorem zpow_neg (a : Residue p) (n : Int) : a ^ (-n) = (a ^ n)⁻¹ := by
  cases n with
  | ofNat k =>
    cases k with
    | zero => exact inv_one.symm
    | succ k => rfl
  | negSucc k => exact (inv_inv (a ^ (k + 1))).symm

/-- The complete pinned Lean 4.24 Field interface, on the original ring carrier.
No instance exists without explicit mathematical `PrimeModulus` evidence. -/
instance instField : Field (Residue p) where
  div_eq_mul_inv := div_eq_mul_inv
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel
  zpow_zero := fun a => Semiring.pow_zero a
  zpow_succ := fun a n => Semiring.pow_succ a n
  zpow_neg := zpow_neg

end Blaster.FiniteField.Residue
