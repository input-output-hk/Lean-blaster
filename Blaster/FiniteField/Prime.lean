/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Lean

/-! Selected prime/divisor arguments from HexArith at
`5ae42d0127e49eb3973ae01a5304a7adb2a9ee65`, adapted to Lean 4.24.0.
No trial-prime implementation or primality decision instance is imported. -/

set_option maxHeartbeats 800000

namespace Blaster.FiniteField

/--
A natural number is prime when it is at least `2` and its positive divisors are
trivial. This is the Mathlib-free prime predicate used by downstream modular
arithmetic layers.
-/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

namespace Prime

/-- Every prime is at least `2`. -/
theorem two_le {p : Nat} (hp : Blaster.FiniteField.Prime p) : 2 ≤ p := hp.1

/-- Every prime is greater than `1`. -/
theorem one_lt {p : Nat} (hp : Blaster.FiniteField.Prime p) : 1 < p := hp.two_le

/-- Every prime is positive. -/
theorem pos {p : Nat} (hp : Blaster.FiniteField.Prime p) : 0 < p :=
  Nat.lt_of_lt_of_le (by decide) hp.two_le

/-- Every prime is nonzero. -/
theorem ne_zero {p : Nat} (hp : Blaster.FiniteField.Prime p) : p ≠ 0 := Nat.ne_of_gt hp.pos

/-- Every prime is distinct from `1`. -/
theorem ne_one {p : Nat} (hp : Blaster.FiniteField.Prime p) : p ≠ 1 := Nat.ne_of_gt hp.one_lt

/-- Build coprimality between a prime and a number it does not divide. -/
theorem coprime_of_not_dvd {p a : Nat} (hp : Blaster.FiniteField.Prime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.Coprime]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply ha
    rw [← hgcd]
    exact Nat.gcd_dvd_right p a

/--
Euclid's lemma for the local prime predicate, in iff form: a prime divides a
product iff it divides one of the factors.
-/
theorem dvd_mul {p a b : Nat} (hp : Blaster.FiniteField.Prime p) :
    p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    by_cases hb : p ∣ b
    · exact Or.inr hb
    · exact Or.inl ((coprime_of_not_dvd hp hb).dvd_of_dvd_mul_right h)
  · intro h
    cases h with
    | inl ha => exact Nat.dvd_trans ha (Nat.dvd_mul_right a b)
    | inr hb => exact Nat.dvd_trans hb (Nat.dvd_mul_left b a)

/-- A prime that divides a power divides its base. -/
theorem dvd_of_dvd_pow {p a k : Nat} (hp : Blaster.FiniteField.Prime p)
    (h : p ∣ a ^ k) : p ∣ a := by
  induction k with
  | zero =>
      exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | succ k ih =>
      rw [Nat.pow_succ] at h
      exact (hp.dvd_mul.mp h).elim ih id

end Prime

/-- Primality is equivalent to excluding divisors strictly between one and the subject. -/
theorem prime_iff_forall_lt (p : Nat) :
    Prime p ↔ 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → ¬ m ∣ p := by
  constructor
  · rintro ⟨hp, hdiv⟩
    refine ⟨hp, ?_⟩
    intro m hmlt hm2 hmdvd
    rcases hdiv m hmdvd with rfl | rfl <;> omega
  · rintro ⟨hp, hno⟩
    refine ⟨hp, ?_⟩
    intro m hmdvd
    have hppos : 0 < p := by omega
    have hmle : m ≤ p := Nat.le_of_dvd hppos hmdvd
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rcases Nat.lt_or_ge m 1 with hm1 | hm1
      · have hm0 : m = 0 := by omega
        subst hm0
        have : p = 0 := Nat.zero_dvd.mp hmdvd
        omega
      · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge m p with hmlt | hmge
      · exact absurd hmdvd (hno m hmlt hm2)
      · exact Or.inr (Nat.le_antisymm hmle hmge)

/-- Checked evidence that a natural-number modulus is prime. No concrete instances
are registered: admission must carry its own proof. -/
class PrimeModulus (p : Nat) : Prop where
  /-- The modulus satisfies the mathematical divisor characterization. -/
  prime : Prime p

namespace PrimeModulus

/-- A checked prime modulus is at least two. -/
theorem two_le (p : Nat) [PrimeModulus p] : 2 ≤ p :=
  (PrimeModulus.prime (p := p)).two_le

/-- A checked prime modulus is positive. -/
theorem pos (p : Nat) [PrimeModulus p] : 0 < p :=
  (PrimeModulus.prime (p := p)).pos

/-- A checked prime modulus cannot be zero. -/
theorem ne_zero (p : Nat) [PrimeModulus p] : p ≠ 0 :=
  (PrimeModulus.prime (p := p)).ne_zero

/-- Checked primality supplies the nonzero-modulus interface. -/
instance (p : Nat) [PrimeModulus p] : NeZero p := ⟨ne_zero p⟩

end PrimeModulus

/-- A nontrivial divisor yields a divisor at most the square root: of `m` and
its cofactor, the smaller one squares to at most `n`. -/
theorem exists_trial_divisor {n m : Nat} (hn : 0 < n) (hm : m ∣ n)
    (hm1 : m ≠ 1) (hmn : m ≠ n) :
    ∃ d, 2 ≤ d ∧ d * d ≤ n ∧ d ∣ n := by
  rcases hm with ⟨c, hc⟩
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    simp at hc
    omega
  have hm2 : 2 ≤ m := by omega
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hc
    omega
  have hc1 : c ≠ 1 := by
    intro h
    subst c
    simp at hc
    exact hmn hc.symm
  have hc2 : 2 ≤ c := by omega
  by_cases hmc : m ≤ c
  · refine ⟨m, hm2, ?_, ⟨c, hc⟩⟩
    rw [hc]
    exact Nat.mul_le_mul_left m hmc
  · have hcm : c ≤ m := Nat.le_of_not_ge hmc
    refine ⟨c, hc2, ?_, ⟨m, ?_⟩⟩
    · rw [hc]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left c hcm
    · simpa [Nat.mul_comm] using hc

/-- A caller-supplied square bound reduces primality to finitely many divisors.
The proof uses the smaller member of a nontrivial factor pair, not a square-root
function or a generic trial-primality checker. -/
theorem prime_of_bounded (p b : Nat) (hp : 2 ≤ p)
    (hb : p < (b + 1) * (b + 1))
    (h : ∀ m, m < b + 1 → 2 ≤ m → ¬ m ∣ p) : Prime p := by
  refine ⟨hp, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  obtain ⟨d, hd2, hdsq, hdvd⟩ := exists_trial_divisor (by omega) hm hm1 hmp
  have hdb : d < b + 1 := by
    by_cases hlt : d < b + 1
    · exact hlt
    · have hle : b + 1 ≤ d := by omega
      have := Nat.mul_le_mul hle hle
      omega
  exact False.elim (h d hdb hd2 hdvd)

/-- Failure of primality yields a proper nontrivial divisor. -/
private theorem exists_small_divisor_of_not_prime {d : Nat} (h2 : 2 ≤ d)
    (hnp : ¬ Prime d) : ∃ m, 2 ≤ m ∧ m < d ∧ m ∣ d := by
  have hfail : ¬ ∀ m, m < d → 2 ≤ m → ¬ m ∣ d := by
    intro hall
    exact hnp ((prime_iff_forall_lt d).mpr ⟨h2, hall⟩)
  rcases Classical.not_forall.mp hfail with ⟨m, hm⟩
  by_cases hmlt : m < d
  · by_cases hm2 : 2 ≤ m
    · by_cases hdvd : m ∣ d
      · exact ⟨m, hm2, hmlt, hdvd⟩
      · exact absurd (fun _ _ => hdvd) hm
    · exact absurd (fun _ h2m => absurd h2m hm2) hm
  · exact absurd (fun hlt => absurd hlt hmlt) hm

/-- Every natural number at least `2` has a prime divisor. -/
theorem exists_prime_dvd {d : Nat} (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d := by
  classical
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hp : Prime d
    · exact ⟨d, hp, Nat.dvd_refl d⟩
    · obtain ⟨m, hm2, hmlt, hmdvd⟩ := exists_small_divisor_of_not_prime h hp
      obtain ⟨q, hq, hqm⟩ := ih m hmlt hm2
      exact ⟨q, hq, Nat.dvd_trans hqm hmdvd⟩

/-- A composite number has a prime divisor whose square is at most the
number. This is the small-divisor witness the Pocklington argument finishes
with. -/
theorem exists_prime_le_sqrt {n : Nat} (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n := by
  obtain ⟨m, hm2, hmlt, hmdvd⟩ := exists_small_divisor_of_not_prime h hcomp
  obtain ⟨d, hd2, hdsq, hddvd⟩ :=
    exists_trial_divisor (by omega : 0 < n) hmdvd (by omega) (by omega)
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd hd2
  refine ⟨q, hq, Nat.dvd_trans hqd hddvd, ?_⟩
  have hqle : q ≤ d := Nat.le_of_dvd (by omega) hqd
  have := Nat.mul_le_mul hqle hqle
  omega

end Blaster.FiniteField
