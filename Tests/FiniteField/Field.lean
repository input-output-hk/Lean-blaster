import Blaster.FiniteField.InverseGraph
import Tests.FF04.Nominal

namespace Test.FiniteFieldField

open Blaster.FiniteField

-- Evidence is mathematical and local: importing field operations must not
-- silently register primality for concrete moduli.
theorem primeTwo : Prime 2 := by
  apply prime_of_bounded 2 1 (by decide) (by decide)
  intro m hm hm2
  omega

theorem primeSeven : Prime 7 := by
  apply prime_of_bounded 7 2 (by decide) (by decide)
  intro m hm hm2
  have heq : m = 2 := by omega
  subst m
  decide

local instance primeModulusTwo : PrimeModulus 2 := ⟨primeTwo⟩
local instance primeModulusSeven : PrimeModulus 7 := ⟨primeSeven⟩

section Generic

variable {p : Nat} [PrimeModulus p]

theorem inverseZero : (0 : Residue p)⁻¹ = 0 := Residue.inv_zero

theorem inverseOne : (1 : Residue p)⁻¹ = 1 := Residue.inv_one

theorem inverseInvolution (a : Residue p) : a⁻¹⁻¹ = a := Residue.inv_inv a

theorem inverseCancel (a : Residue p) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  Residue.mul_inv_cancel ha

theorem divisionDefinition (a b : Residue p) : a / b = a * b⁻¹ :=
  Residue.div_eq_mul_inv a b

theorem divisionZero (a : Residue p) : a / 0 = 0 := by
  rw [Residue.div_eq_mul_inv, Residue.inv_zero, Lean.Grind.Semiring.mul_zero]

theorem zeroDivision (a : Residue p) : 0 / a = 0 := by
  rw [Residue.div_eq_mul_inv, Lean.Grind.Semiring.zero_mul]

theorem zeroByZero : (0 : Residue p) / 0 = 0 := divisionZero 0

theorem selfDivision (a : Residue p) (ha : a ≠ 0) : a / a = 1 := by
  rw [Residue.div_eq_mul_inv, Residue.mul_inv_cancel ha]

theorem divisionMulCancel (a b : Residue p) (hb : b ≠ 0) : a / b * b = a := by
  rw [Residue.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.CommSemiring.mul_comm b⁻¹ b, Residue.mul_inv_cancel hb,
    Lean.Grind.Semiring.mul_one]

theorem naturalZeroZero : (0 : Residue p) ^ (0 : Nat) = 1 :=
  Lean.Grind.Semiring.pow_zero 0

theorem naturalZeroPositive (n : Nat) : (0 : Residue p) ^ (n + 1) = 0 := by
  rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.mul_zero]

theorem integerNaturalAgreement (a : Residue p) (n : Nat) :
    a ^ (n : Int) = a ^ n := Residue.zpow_natCast a n

theorem integerNegative (a : Residue p) (n : Nat) :
    a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := rfl

theorem integerNegation (a : Residue p) (n : Int) : a ^ (-n) = (a ^ n)⁻¹ :=
  Residue.zpow_neg a n

theorem integerZeroNegative (n : Nat) :
    (0 : Residue p) ^ (-((n + 1 : Nat) : Int)) = 0 := by
  rw [Residue.zpow_neg, Residue.zpow_natCast, naturalZeroPositive, Residue.inv_zero]

end Generic

theorem characteristicTwo : (2 : Residue 2) = 0 ∧ (0 : Residue 2) ≠ 1 :=
  ⟨by decide, Residue.zero_ne_one⟩

theorem characteristicSeven : (7 : Residue 7) = 0 ∧ (0 : Residue 7) ≠ 1 :=
  ⟨by decide, Residue.zero_ne_one⟩

-- At p = 2 the Fermat exponent is zero. The explicit inverse-zero branch
-- must still return zero, not the value of the zeroth natural power.
theorem concreteTwo :
    (0 : Residue 2)⁻¹ = 0 ∧ (1 : Residue 2)⁻¹ = 1 ∧
    (0 : Residue 2) / 0 = 0 ∧ (1 : Residue 2) / 0 = 0 ∧
    (1 : Residue 2) / 1 = 1 ∧ (0 : Residue 2) ^ (0 : Nat) = 1 ∧
    (0 : Residue 2) ^ (3 : Nat) = 0 ∧
    (0 : Residue 2) ^ (-1 : Int) = 0 ∧ (1 : Residue 2) ^ (-3 : Int) = 1 ∧
    (0 : Residue 2) ^ (0 : Int) = 1 := by decide

theorem concreteSeven :
    (3 : Residue 7)⁻¹ = 5 ∧ (3 : Residue 7) / 2 = 5 ∧
    (0 : Residue 7)⁻¹ = 0 ∧ (0 : Residue 7) / 0 = 0 ∧
    (3 : Residue 7) / 0 = 0 ∧ (0 : Residue 7) / 3 = 0 ∧
    (3 : Residue 7) / 3 = 1 ∧ (0 : Residue 7) ^ (0 : Nat) = 1 ∧
    (0 : Residue 7) ^ (3 : Nat) = 0 ∧ (0 : Residue 7) ^ (-3 : Int) = 0 ∧
    (3 : Residue 7) ^ (-1 : Int) = 5 ∧ (3 : Residue 7) ^ (-2 : Int) = 4 ∧
    (3 : Residue 7) ^ (3 : Int) = (3 : Residue 7) ^ (3 : Nat) := by decide

-- The nominal carrier must not inherit Fin's truncating quotient.
theorem divisionNotFinDivision :
    (3 : Residue 7) / 2 = 5 ∧ ((3 : Fin 7) / 2).val = 1 := by decide

theorem compositeRingOnly : True := by
  have : Nonempty (Lean.Grind.CommRing (Residue 6)) := ⟨inferInstance⟩
  have : Nonempty (Lean.Grind.IsCharP (Residue 6) 6) := ⟨inferInstance⟩
  have : Nonempty (Lean.Grind.Field (Residue 2)) := ⟨inferInstance⟩
  have : Nonempty (Lean.Grind.Field (Residue 7)) := ⟨inferInstance⟩
  fail_if_success have : PrimeModulus 6 := inferInstance
  fail_if_success have : Inv (Residue 6) := inferInstance
  fail_if_success have : Div (Residue 6) := inferInstance
  fail_if_success have : HPow (Residue 6) Int (Residue 6) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue 6) := inferInstance
  trivial

theorem compositeArithmetic :
    (2 : Residue 6) ≠ 0 ∧ (3 : Residue 6) ≠ 0 ∧
    (2 : Residue 6) * 3 = 0 ∧ (0 : Residue 6) ^ (0 : Nat) = 1 := by decide

theorem nonzeroModulusNotField (p : Nat) [NeZero p] : True := by
  fail_if_success have : Inv (Residue p) := inferInstance
  fail_if_success have : Div (Residue p) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue p) := inferInstance
  trivial

theorem compatibilityCarrier (p : Nat) : Blaster.FF04.Residue p = Residue p := rfl

theorem compatibilityDivision (p : Nat) [PrimeModulus p]
    (a b : Blaster.FF04.Residue p) : a / b = (show Residue p from a) / b := rfl

end Test.FiniteFieldField
