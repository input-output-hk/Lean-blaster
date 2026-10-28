/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Blaster.FiniteField.Prime

/-!
The sieve-free Brillhart-Lehmer-Selfridge cube-root primality criterion.

Selectively ported from `HexPrimality/Cert3.lean` at
`e89daa43f1c6f2038a59674598e2a5097e64c3df`, directly specializing its argument
to the case where both nontrivial factors have positive coefficients. No
certificate checker or bounded divisibility sieve is needed here.
-/

namespace Blaster.FiniteField

/-- A number strictly between consecutive squares is not a square. -/
theorem not_square_of_sqrt_witness {w D : Nat} (h1 : w * w < D)
    (h2 : D < (w + 1) * (w + 1)) : ∀ t, t * t ≠ D := by
  intro t ht
  rcases Nat.lt_or_ge t (w + 1) with hlt | hge
  · have : t * t ≤ w * w := Nat.mul_le_mul (by omega) (by omega)
    omega
  · have : (w + 1) * (w + 1) ≤ t * t := Nat.mul_le_mul hge hge
    omega

/-- If every prime divisor of `n` is one modulo `F`, so is every positive divisor. -/
private theorem divisor_mod_one {n F : Nat} (hF : 2 ≤ F)
    (hdivmod : ∀ p, Prime p → p ∣ n → F ∣ p - 1) :
    ∀ d, d ∣ n → 0 < d → d % F = 1 := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hdn hd0
    rcases Nat.lt_or_ge d 2 with h1 | h2
    · have hd1 : d = 1 := by omega
      subst hd1
      exact Nat.mod_eq_of_lt (by omega)
    · obtain ⟨q, hq, hqd⟩ := exists_prime_dvd h2
      have hq2 := hq.two_le
      have hq1 : q % F = 1 := by
        obtain ⟨u, hu⟩ := hdivmod q hq (Nat.dvd_trans hqd hdn)
        have hcomm : F * u = u * F := Nat.mul_comm F u
        have hqe : q = 1 + u * F := by omega
        rw [hqe, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hdq_dvd : d / q ∣ d := ⟨q, (Nat.div_mul_cancel hqd).symm⟩
      have hdq_pos : 0 < d / q :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq.pos
      have ihq := ih (d / q) (Nat.div_lt_self (by omega) hq.one_lt)
        (Nat.dvd_trans hdq_dvd hdn) hdq_pos
      have hde : d = q * (d / q) := (Nat.mul_div_cancel' hqd).symm
      rw [hde, Nat.mul_mod, hq1, ihq]
      simpa using Nat.mod_eq_of_lt (show 1 < F by omega)

/-- Expand the square of a sum into the three product terms. -/
private theorem sq_expand (x y : Nat) :
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm y x]
  omega

/-- With `a ≤ b`, `a + b = r`, and `ab = 2s`, the discriminant is `(b-a)²`. -/
private theorem discriminant_eq {a b r s : Nat} (hab : a ≤ b)
    (hsum : a + b = r) (hprod : a * b = 2 * s) :
    r * r = (b - a) * (b - a) + 8 * s := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  subst hsum
  have hc : a + c - a = c := by omega
  rw [hc]
  have h1 := sq_expand a (a + c)
  have h2 := sq_expand a c
  have h3 : a * (a + c) = a * a + a * c := Nat.mul_add a a c
  omega

/-- The cube-root size bound caps the quotient decomposition by `2s ≤ 2F+r`. -/
private theorem two_s_le {F r s n : Nat} (_hF : 2 ≤ F) (hr : 1 ≤ r)
    (hn : n - 1 = F * (2 * F * s + r)) (hn2 : 2 ≤ n)
    (hbound : n < (F + 1) * (2 * F * F + (r - 1) * F + 1)) :
    2 * s ≤ 2 * F + r := by
  by_cases hcontra : 2 * s ≤ 2 * F + r
  · exact hcontra
  exfalso
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hsub : r' + 1 - 1 = r' := by omega
  rw [hsub] at hbound
  have h1 : 2 * F + (r' + 1) + 1 ≤ 2 * s := by omega
  have h2 : F * F * (2 * F + (r' + 1) + 1) ≤ F * F * (2 * s) :=
    Nat.mul_le_mul_left _ h1
  have e1 : F * (2 * F * s + (r' + 1)) = 2 * (F * (F * s)) + F * r' + F := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have ac : F * (2 * F * s) = 2 * (F * (F * s)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have e2 : (F + 1) * (2 * F * F + r' * F + 1) =
      2 * (F * (F * F)) + F * (r' * F) + F + (2 * F * F + r' * F + 1) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have ac : F * (2 * F * F) = 2 * (F * (F * F)) := by
      simp [Nat.mul_assoc, Nat.mul_comm]
    omega
  have e3 : F * F * (2 * F + (r' + 1) + 1) =
      2 * (F * (F * F)) + F * (r' * F) + 2 * (F * F) := by
    rw [Nat.mul_add, Nat.mul_add]
    have ac1 : F * F * (2 * F) = 2 * (F * (F * F)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have ac2 : F * F * (r' + 1) = F * (r' * F) + F * F := by
      rw [Nat.mul_add, Nat.mul_one]
      have : F * F * r' = F * (r' * F) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      omega
    omega
  have e4 : F * F * (2 * s) = 2 * (F * (F * s)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e5 : F * r' = r' * F := Nat.mul_comm F r'
  have e6 : 2 * F * F = 2 * (F * F) := by
    simp [Nat.mul_assoc]
  rw [e3, e4] at h2
  rw [e1] at hn
  rw [e2] at hbound
  omega

/-- The sieve-free Brillhart-Lehmer-Selfridge cube-root criterion. If every
prime divisor is one modulo the even factored part `F`, the size and
nonsquare-discriminant conditions rule out a nontrivial factorization. -/
theorem pocklington3 {n F r s : Nat} (hn3 : 3 ≤ n)
    (hF : F ∣ n - 1) (hFeven : F % 2 = 0) (hF0 : 0 < F)
    (hRodd : (n - 1) / F % 2 = 1)
    (hdec : (n - 1) / F = 2 * F * s + r) (hr1 : 1 ≤ r) (hr2 : r < 2 * F)
    (hbound : n < (F + 1) * (2 * F * F + (r - 1) * F + 1))
    (hdisc : s = 0 ∨ r * r < 8 * s ∨ ∀ t, t * t ≠ r * r - 8 * s) :
    (∀ p, Prime p → p ∣ n → F ∣ p - 1) → Prime n := by
  intro hdivmod
  have hF2 : 2 ≤ F := by omega
  have hn1 : n - 1 = F * (2 * F * s + r) := by
    rw [← hdec]
    exact (Nat.mul_div_cancel' hF).symm
  have hcap := two_s_le hF2 hr1 hn1 (by omega) hbound
  by_cases hp : Prime n
  · exact hp
  exfalso
  -- A composite splits into two nontrivial factors, each one modulo F.
  obtain ⟨q, hq, hqn⟩ := exists_prime_dvd (show 2 ≤ n by omega)
  have hq2 := hq.two_le
  have hnq_dvd : n / q ∣ n := ⟨q, by
    rw [Nat.mul_comm]
    exact (Nat.mul_div_cancel' hqn).symm⟩
  have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hq.pos
  have hnq2 : 2 ≤ n / q := by
    rcases Nat.lt_or_ge (n / q) 2 with h | h
    · exfalso
      have h1 : n / q = 1 := by omega
      have h2 := Nat.mul_div_cancel' hqn
      rw [h1, Nat.mul_one] at h2
      exact hp (h2 ▸ hq)
    · exact h
  have hq_mod : q % F = 1 :=
    divisor_mod_one hF2 hdivmod q hqn hq.pos
  have hnq_mod : n / q % F = 1 :=
    divisor_mod_one hF2 hdivmod (n / q) hnq_dvd hnq_pos
  obtain ⟨a, hqe, ha1⟩ : ∃ a, q = F * a + 1 ∧ 1 ≤ a := by
    refine ⟨q / F, ?_, ?_⟩
    · have := Nat.div_add_mod q F
      omega
    · rcases Nat.eq_zero_or_pos (q / F) with h0 | h
      · exfalso
        have := Nat.div_add_mod q F
        rw [h0, Nat.mul_zero] at this
        omega
      · exact h
  obtain ⟨b, hbe, hb1⟩ : ∃ b, n / q = F * b + 1 ∧ 1 ≤ b := by
    refine ⟨n / q / F, ?_, ?_⟩
    · have := Nat.div_add_mod (n / q) F
      omega
    · rcases Nat.eq_zero_or_pos (n / q / F) with h0 | h
      · exfalso
        have := Nat.div_add_mod (n / q) F
        rw [h0, Nat.mul_zero] at this
        omega
      · exact h
  -- The factorization gives abF + (a+b) = 2Fs + r.
  have hne : n = (F * a + 1) * (F * b + 1) := by
    rw [← hqe, ← hbe]
    exact (Nat.mul_div_cancel' hqn).symm
  have hexp : (F * a + 1) * (F * b + 1) =
      F * (a * b * F + (a + b)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have ac1 : F * a * (F * b) = F * (a * b * F) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    omega
  have heq : a * b * F + (a + b) = 2 * F * s + r := by
    refine Nat.eq_of_mul_eq_mul_left hF0 ?_
    have hleft : F * (a * b * F + (a + b)) = n - 1 := by
      rw [hne] at hn1 ⊢
      omega
    rw [hleft, hn1]
  have hr_odd : r % 2 = 1 := by
    rw [hdec] at hRodd
    have ac : 2 * F * s = 2 * (F * s) := by
      simp [Nat.mul_assoc]
    omega
  have hg_odd : (a + b) % 2 = 1 := by
    obtain ⟨F', hF'⟩ : ∃ F', F = 2 * F' := ⟨F / 2, by omega⟩
    have ac1 : a * b * F = 2 * (a * b * F') := by
      rw [hF']
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have ac2 : 2 * F * s = 2 * (F * s) := by
      simp [Nat.mul_assoc]
    omega
  have hP_even : a * b % 2 = 0 := by
    by_cases ha2 : a % 2 = 0
    · obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
      have : a * b = 2 * (a' * b) := by
        rw [ha']
        simp [Nat.mul_assoc]
      omega
    · have hb2 : b % 2 = 0 := by omega
      obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
      have : a * b = 2 * (a * b') := by
        rw [hb']
        simp [Nat.mul_assoc, Nat.mul_comm]
      omega
  have hmod : (a + b) % F = r % F := by
    have h1 : (a * b * F + (a + b)) % F = (a + b) % F := by
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_right ..
    have h2 : (2 * F * s + r) % F = r % F := by
      have ac : 2 * F * s = 2 * s * F := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      rw [ac, Nat.add_comm]
      exact Nat.add_mul_mod_self_right ..
    rw [← h1, heq, h2]
  have hk0 : a + b = r ∧ a * b = 2 * s := by
    rcases Nat.lt_trichotomy (a + b) r with hlt | heqr | hgt
    · -- A positive offset below r is even, contradicting r < 2F.
      exfalso
      have hdvd : F ∣ r - (a + b) :=
        Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h
        · rw [h0, Nat.mul_zero] at hk
          omega
        · exact h
      have hPk : a * b = 2 * s + k := by
        refine Nat.eq_of_mul_eq_mul_right hF0 ?_
        have e : (2 * s + k) * F = 2 * F * s + F * k := by
          rw [Nat.add_mul]
          have ac1 : 2 * s * F = 2 * F * s := by
            simp [Nat.mul_comm, Nat.mul_left_comm]
          have ac2 : k * F = F * k := Nat.mul_comm k F
          omega
        have e2 : a * b * F = (a * b) * F := rfl
        rw [e2, e]
        omega
      have hkeven : k % 2 = 0 := by omega
      have hk2 : 2 ≤ k := by omega
      have : 2 * F ≤ F * k := by
        have := Nat.mul_le_mul_left F hk2
        omega
      omega
    · refine ⟨heqr, ?_⟩
      refine Nat.eq_of_mul_eq_mul_right hF0 ?_
      have ac1 : 2 * s * F = 2 * F * s := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have e2 : a * b * F = (a * b) * F := rfl
      omega
    · -- A positive offset above r contradicts the cube-root size bound.
      exfalso
      have hdvd : F ∣ (a + b) - r :=
        Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h
        · rw [h0, Nat.mul_zero] at hk
          omega
        · exact h
      have hPk : a * b + k = 2 * s := by
        refine Nat.eq_of_mul_eq_mul_right hF0 ?_
        have e : (a * b + k) * F = a * b * F + F * k := by
          rw [Nat.add_mul]
          have ac2 : k * F = F * k := Nat.mul_comm k F
          omega
        have e3 : (2 * s) * F = 2 * F * s := by
          simp [Nat.mul_comm, Nat.mul_left_comm]
        rw [e, e3]
        omega
      have hkeven : k % 2 = 0 := by omega
      have hk2 : 2 ≤ k := by omega
      have hFk : 2 * F ≤ F * k := by
        have := Nat.mul_le_mul_left F hk2
        omega
      have hab : a + b ≤ a * b + 1 := by
        obtain ⟨u, rfl⟩ : ∃ u, a = 1 + u := ⟨a - 1, by omega⟩
        obtain ⟨v, rfl⟩ : ∃ v, b = 1 + v := ⟨b - 1, by omega⟩
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      have hsum : 2 * F + r ≤ a + b := by omega
      omega
  obtain ⟨hsum, hprod⟩ := hk0
  obtain ⟨t, ht⟩ : ∃ t, r * r = t * t + 8 * s := by
    rcases Nat.le_total a b with hab | hab
    · exact ⟨b - a, discriminant_eq hab hsum hprod⟩
    · exact ⟨a - b, discriminant_eq hab
        (by rw [Nat.add_comm]; exact hsum)
        (by rw [Nat.mul_comm]; exact hprod)⟩
  rcases hdisc with hs0 | h8lt | hnsq
  · subst hs0
    rcases Nat.mul_eq_zero.mp (by omega : a * b = 0) with h | h <;> omega
  · omega
  · exact hnsq t (by omega)

end Blaster.FiniteField
