/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Blaster.FiniteField.PrimeFermat

/-! Multiplicative order and Pocklington witness arguments, selectively adapted
from HexPrimality/Order.lean and Cert.lean at
`e89daa43f1c6f2038a59674598e2a5097e64c3df`. The order scan is proof-only
in this slice: concrete fixture arithmetic uses modular repeated squaring. -/

set_option maxHeartbeats 800000

namespace Blaster.FiniteField

/-- An injective list of natural numbers contained in another list cannot be longer.
This elementary counting fact replaces the upstream list-shim import. -/
private theorem nodup_subset_length_le {xs ys : List Nat}
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      have hn' := List.nodup_cons.mp hn
      have ha : a ∈ ys := hs (List.mem_cons_self ..)
      have hsub : xs ⊆ ys.erase a := by
        intro b hb
        have hne : b ≠ a := by
          intro heq
          subst b
          exact hn'.1 hb
        exact (List.mem_erase_of_ne hne).mpr (hs (List.mem_cons_of_mem a hb))
      have hlen := ih hn'.2 hsub
      rw [List.length_erase_of_mem ha] at hlen
      have hpos := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

/-- Scan consecutive exponents while carrying the current power residue. -/
private def orderOfAux (b n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, k, r =>
      if r = 1 % n then k
      else orderOfAux b n fuel (k + 1) (r * b % n)

/-- Multiplicative order of `a` modulo `n`: the least `k > 0` with
`a ^ k % n = 1 % n` when `1 < n` and `Nat.Coprime a n`, and `0` on every
other input. -/
def orderOf (a n : Nat) : Nat :=
  if 1 < n ∧ Nat.Coprime a n then orderOfAux (a % n) n n 1 (a % n) else 0

/-- A successful scan returns the least witness in its search interval. -/
private theorem orderOfAux_spec (a n : Nat) :
    ∀ fuel k r, r = a ^ k % n → orderOfAux (a % n) n fuel k r ≠ 0 →
      k ≤ orderOfAux (a % n) n fuel k r ∧
      a ^ orderOfAux (a % n) n fuel k r % n = 1 % n ∧
      ∀ j, k ≤ j → j < orderOfAux (a % n) n fuel k r → a ^ j % n ≠ 1 % n := by
  intro fuel
  induction fuel with
  | zero =>
      intro k r _ h
      simp [orderOfAux] at h
  | succ fuel ih =>
      intro k r hr h
      unfold orderOfAux at h ⊢
      by_cases hk : r = 1 % n
      · rw [if_pos hk] at h ⊢
        exact ⟨Nat.le_refl _, hr ▸ hk, fun j hkj hjk => by omega⟩
      · rw [if_neg hk] at h ⊢
        have hr' : r * (a % n) % n = a ^ (k + 1) % n := by
          rw [hr, ← Nat.mul_mod, ← Nat.pow_succ]
        obtain ⟨hle, hpow, hmin⟩ := ih (k + 1) _ hr' h
        refine ⟨by omega, hpow, ?_⟩
        intro j hkj hjlt
        rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
        · exact fun hpow => hk (hr.trans hpow)
        · exact hmin j hlt hjlt

/-- A witness within the search interval makes the scan succeed. -/
private theorem orderOfAux_ne_zero_of_witness (a n : Nat) :
    ∀ fuel k r, r = a ^ k % n → 0 < k →
      ∀ j, k ≤ j → j < k + fuel → a ^ j % n = 1 % n →
        orderOfAux (a % n) n fuel k r ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro k r hr hk j hkj hjb _
      omega
  | succ fuel ih =>
      intro k r hr hk j hkj hjb hj
      unfold orderOfAux
      by_cases hcase : r = 1 % n
      · rw [if_pos hcase]
        omega
      · rw [if_neg hcase]
        have hne : j ≠ k := fun h => hcase (hr.trans (h ▸ hj))
        have hr' : r * (a % n) % n = a ^ (k + 1) % n := by
          rw [hr, ← Nat.mul_mod, ← Nat.pow_succ]
        exact ih (k + 1) _ hr' (by omega) j (by omega) (by omega) hj

/-- A positive power is divisible by its base. -/
private theorem dvd_pow_self' (a : Nat) {k : Nat} (hk : k ≠ 0) : a ∣ a ^ k := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k => exact ⟨a ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩

/-- A power congruent to `1` forces coprimality of the base: the gcd divides
both `a ^ k` and `n`, hence their remainder `1`. -/
theorem coprime_of_pow_mod_eq_one {a n k : Nat} (h1 : 1 < n) (hk : 0 < k)
    (h : a ^ k % n = 1 % n) : Nat.Coprime a n := by
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt h1
  rw [h1n] at h
  have hg_ak : Nat.gcd a n ∣ a ^ k :=
    Nat.dvd_trans (Nat.gcd_dvd_left a n) (dvd_pow_self' a (by omega))
  have hg_mod : Nat.gcd a n ∣ a ^ k % n :=
    (Nat.dvd_mod_iff (Nat.gcd_dvd_right a n)).mpr hg_ak
  rw [h] at hg_mod
  exact Nat.dvd_one.mp hg_mod

/-- Cancel a coprime power from a congruence with ordered representatives. -/
private theorem pow_mod_cancel_le {a n i x y : Nat} (hcop : Nat.Coprime a n)
    (hxy : x ≤ y) (h : a ^ i * x % n = a ^ i * y % n) : x % n = y % n := by
  have hdvd : n ∣ a ^ i * y - a ^ i * x :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  rw [← Nat.mul_sub] at hdvd
  have hdvd' : n ∣ y - x :=
    Nat.Coprime.dvd_of_dvd_mul_left ((hcop.pow_left i).symm) hdvd
  obtain ⟨t, ht⟩ := hdvd'
  have hy : y = x + n * t := by omega
  subst hy
  rw [Nat.add_mul_mod_self_left]

/-- Coprime cancellation: a common factor `a ^ i` cancels from a congruence
modulo `n`. -/
private theorem pow_mod_cancel {a n : Nat} (hcop : Nat.Coprime a n) {i x y : Nat}
    (h : a ^ i * x % n = a ^ i * y % n) : x % n = y % n := by
  rcases Nat.le_total x y with hxy | hxy
  · exact pow_mod_cancel_le hcop hxy h
  · exact (pow_mod_cancel_le hcop hxy h.symm).symm

/-- Fermat's little theorem in multiplicative form, from the residue form
`pow_prime_mod` by cancelling one factor of `a`. -/
theorem pow_pred_mod {p a : Nat} (hp : Prime p) (h : Nat.Coprime a p) :
    a ^ (p - 1) % p = 1 % p := by
  have hp2 := hp.two_le
  have hfermat := pow_prime_mod hp a
  have hsplit : a ^ p = a ^ 1 * a ^ (p - 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hrhs : a % p = a ^ 1 * 1 % p := by simp
  rw [hsplit, hrhs] at hfermat
  exact pow_mod_cancel h hfermat

/-- For a unit at a nontrivial modulus, the order is the bounded scan. -/
private theorem orderOf_eq_aux {a n : Nat} (h1 : 1 < n) (hcop : Nat.Coprime a n) :
    orderOf a n = orderOfAux (a % n) n n 1 (a % n) := by
  unfold orderOf
  rw [if_pos ⟨h1, hcop⟩]

/-- A positive order certifies a nontrivial modulus. -/
theorem one_lt_of_orderOf_pos {a n : Nat} (h : 0 < orderOf a n) : 1 < n := by
  by_cases hg : 1 < n ∧ Nat.Coprime a n
  · exact hg.1
  · unfold orderOf at h
    rw [if_neg hg] at h
    omega

/-- A positive order certifies coprimality. -/
theorem coprime_of_orderOf_pos {a n : Nat} (h : 0 < orderOf a n) :
    Nat.Coprime a n := by
  by_cases hg : 1 < n ∧ Nat.Coprime a n
  · exact hg.2
  · unfold orderOf at h
    rw [if_neg hg] at h
    omega

/-- A positive order is an exponent sending `a` to `1` modulo `n`. -/
theorem orderOf_pow_mod {a n : Nat} (h : 0 < orderOf a n) :
    a ^ orderOf a n % n = 1 % n := by
  have h1 := one_lt_of_orderOf_pos h
  have hcop := coprime_of_orderOf_pos h
  rw [orderOf_eq_aux h1 hcop] at h ⊢
  exact (orderOfAux_spec a n n 1 (a % n) (by simp) (by omega)).2.1

/-- Minimality of a positive order among positive exponents. -/
theorem orderOf_min {a n : Nat} (h : 0 < orderOf a n) :
    ∀ j, 0 < j → j < orderOf a n → a ^ j % n ≠ 1 % n := by
  have h1 := one_lt_of_orderOf_pos h
  have hcop := coprime_of_orderOf_pos h
  rw [orderOf_eq_aux h1 hcop] at h ⊢
  intro j hj hjlt
  exact (orderOfAux_spec a n n 1 (a % n) (by simp) (by omega)).2.2 j (by omega) hjlt

/-- Distinct power residues below `d` force `d ≤ n`, by pigeonhole inside
`List.range n`. -/
private theorem le_of_pow_residues_distinct {a n d : Nat} (h1 : 1 < n)
    (hdist : ∀ i j, i < j → j < d → a ^ i % n ≠ a ^ j % n) : d ≤ n := by
  have hnodup : ((List.range d).map (fun i => a ^ i % n)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact hdist i j hij hj
  have hsub : ((List.range d).map (fun i => a ^ i % n)) ⊆ List.range n := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rw [List.mem_range]
    exact Nat.mod_lt _ (by omega)
  have hlen := nodup_subset_length_le hnodup hsub
  simp only [List.length_map, List.length_range] at hlen
  exact hlen

/-- A repeated power residue cancels to a witness exponent. -/
private theorem pow_witness_of_residue_eq {a n i j : Nat}
    (hcop : Nat.Coprime a n) (hij : i < j)
    (heq : a ^ i % n = a ^ j % n) : a ^ (j - i) % n = 1 % n := by
  have hstep : a ^ i * 1 % n = a ^ i * a ^ (j - i) % n := by
    rw [Nat.mul_one, ← Nat.pow_add]
    have hji : i + (j - i) = j := by omega
    rw [hji]
    exact heq
  exact (pow_mod_cancel hcop hstep).symm

/-- The least positive exponent sending `a` to `1` is at most `n`, by
pigeonhole on the residues `a ^ 0 % n, …, a ^ (d - 1) % n`. -/
private theorem le_of_least_pow_witness {a n d : Nat} (h1 : 1 < n)
    (hcop : Nat.Coprime a n)
    (hdmin : ∀ j, 1 ≤ j → j < d → a ^ j % n ≠ 1 % n) : d ≤ n := by
  refine le_of_pow_residues_distinct (a := a) h1 ?_
  intro i j hij hjd heq
  exact hdmin (j - i) (by omega) (by omega)
    (pow_witness_of_residue_eq hcop hij heq)

/-- A witness exponent produces a positive order: the scan up to the witness
finds the least one, pigeonhole bounds it by `n`, and the definitional scan
up to `n` therefore also finds it. -/
theorem orderOf_pos_of_pow_eq_one {a n k : Nat} (h1 : 1 < n) (hk : 0 < k)
    (h : a ^ k % n = 1 % n) : 0 < orderOf a n := by
  have hcop := coprime_of_pow_mod_eq_one h1 hk h
  have hne : orderOfAux (a % n) n k 1 (a % n) ≠ 0 :=
    orderOfAux_ne_zero_of_witness a n k 1 (a % n) (by simp) (by omega)
      k (by omega) (by omega) h
  obtain ⟨hd1, hdpow, hdmin⟩ := orderOfAux_spec a n k 1 (a % n) (by simp) hne
  have hdn : orderOfAux (a % n) n k 1 (a % n) ≤ n :=
    le_of_least_pow_witness h1 hcop hdmin
  have hne' : orderOfAux (a % n) n n 1 (a % n) ≠ 0 :=
    orderOfAux_ne_zero_of_witness a n n 1 (a % n) (by simp) (by omega)
      (orderOfAux (a % n) n k 1 (a % n)) hd1 (by omega) hdpow
  rw [orderOf_eq_aux h1 hcop]
  have := (orderOfAux_spec a n n 1 (a % n) (by simp) hne').1
  omega

/-- The order divides every exponent sending `a` to `1` modulo `n`. -/
theorem orderOf_dvd_of_pow_eq_one {a n k : Nat} (h1 : 1 < n) (hk : 0 < k)
    (h : a ^ k % n = 1 % n) : orderOf a n ∣ k := by
  have hpos := orderOf_pos_of_pow_eq_one h1 hk h
  have hpowmod : a ^ (k % orderOf a n) % n = 1 % n := by
    have hbig : a ^ k % n = a ^ (k % orderOf a n) % n := by
      calc a ^ k % n
          = a ^ (orderOf a n * (k / orderOf a n) + k % orderOf a n) % n := by
            rw [Nat.div_add_mod]
        _ = (a ^ (orderOf a n * (k / orderOf a n)) * a ^ (k % orderOf a n)) % n := by
            rw [Nat.pow_add]
        _ = ((a ^ (orderOf a n * (k / orderOf a n)) % n) *
              (a ^ (k % orderOf a n) % n)) % n := by
            rw [Nat.mul_mod]
        _ = (((a ^ orderOf a n) ^ (k / orderOf a n) % n) *
              (a ^ (k % orderOf a n) % n)) % n := by
            rw [Nat.pow_mul]
        _ = (((a ^ orderOf a n % n) ^ (k / orderOf a n) % n) *
              (a ^ (k % orderOf a n) % n)) % n := by
            rw [Nat.pow_mod]
        _ = (((1 % n) ^ (k / orderOf a n) % n) *
              (a ^ (k % orderOf a n) % n)) % n := by
            rw [orderOf_pow_mod hpos]
        _ = ((1 ^ (k / orderOf a n) % n) *
              (a ^ (k % orderOf a n) % n)) % n := by
            rw [← Nat.pow_mod]
        _ = ((1 % n) * (a ^ (k % orderOf a n) % n)) % n := by
            rw [Nat.one_pow]
        _ = (1 * a ^ (k % orderOf a n)) % n := by
            rw [← Nat.mul_mod]
        _ = a ^ (k % orderOf a n) % n := by
            rw [Nat.one_mul]
    rw [← hbig, h]
  by_cases hr : k % orderOf a n = 0
  · exact Nat.dvd_of_mod_eq_zero hr
  · exact absurd hpowmod
      (orderOf_min hpos _ (by omega) (Nat.mod_lt _ hpos))

/-- Any multiple of a positive order sends `a` to `1` modulo `n`. -/
theorem pow_eq_one_of_orderOf_dvd {a n k : Nat} (h : 0 < orderOf a n)
    (hd : orderOf a n ∣ k) : a ^ k % n = 1 % n := by
  obtain ⟨t, rfl⟩ := hd
  calc a ^ (orderOf a n * t) % n
      = (a ^ orderOf a n) ^ t % n := by rw [Nat.pow_mul]
    _ = (a ^ orderOf a n % n) ^ t % n := by rw [Nat.pow_mod]
    _ = (1 % n) ^ t % n := by rw [orderOf_pow_mod h]
    _ = 1 ^ t % n := by rw [← Nat.pow_mod]
    _ = 1 % n := by rw [Nat.one_pow]

/-- The order of a unit modulo a prime divides `p - 1`. -/
theorem orderOf_dvd_pred {p a : Nat} (hp : Prime p) (h : Nat.Coprime a p) :
    orderOf a p ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one hp.one_lt
    (by have := hp.two_le; omega) (pow_pred_mod hp h)

/-- Prime-power extraction into the order: if `q ^ j ∣ m`, `a ^ m ≡ 1`, and
`a ^ (m / q) ≢ 1` modulo `p`, then `q ^ j` divides the order of `a`. Stated
with `q ^ j ∣ m` as a hypothesis so no valuation API is needed. -/
theorem prime_pow_dvd_orderOf {q j m a p : Nat} (hq : Prime q) (hj : q ^ j ∣ m)
    (h1 : 1 < p) (hm : a ^ m % p = 1 % p) (hne : a ^ (m / q) % p ≠ 1 % p) :
    q ^ j ∣ orderOf a p := by
  cases j with
  | zero => simp
  | succ j =>
    have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      simp [Nat.zero_div] at hne
    have hpos := orderOf_pos_of_pow_eq_one h1 (by omega) hm
    have hdvd_m : orderOf a p ∣ m :=
      orderOf_dvd_of_pow_eq_one h1 (by omega) hm
    obtain ⟨t, ht⟩ := hdvd_m
    have hqt : ¬ q ∣ t := by
      rintro ⟨s, hs⟩
      have hq0 : 0 < q := hq.pos
      have hmq : m / q = orderOf a p * s := by
        rw [ht, hs, Nat.mul_comm q s, ← Nat.mul_assoc]
        exact Nat.mul_div_cancel _ hq0
      have hcongr : a ^ (m / q) % p = 1 % p :=
        pow_eq_one_of_orderOf_dvd hpos ⟨s, hmq⟩
      exact hne hcongr
    have hcop : Nat.Coprime (q ^ (j + 1)) t :=
      Nat.Coprime.pow_left _ (hq.coprime_of_not_dvd hqt)
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop (ht ▸ hj)

/-- A gcd-one witness stays nontrivial modulo each prime divisor. -/
private theorem mod_ne_one_of_gcd {p n x : Nat} (hp : 2 ≤ p) (hpn : p ∣ n)
    (hx : x < n) (hg : Nat.gcd ((x + n - 1) % n) n = 1) :
    x % p ≠ 1 % p := by
  intro heq
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1p] at heq
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · rw [Nat.zero_mod] at heq
      omega
    · exact h
  have hpx : p ∣ x - 1 := by
    have := Nat.div_add_mod x p
    exact ⟨x / p, by omega⟩
  have hpxn : p ∣ x + n - 1 := by
    obtain ⟨u, hu⟩ := hpx
    obtain ⟨v, hv⟩ := hpn
    exact ⟨u + v, by rw [Nat.mul_add]; omega⟩
  have hpmod : p ∣ (x + n - 1) % n := by
    have h1 : p ∣ n * ((x + n - 1) / n) :=
      Nat.dvd_trans hpn (Nat.dvd_mul_right n _)
    have h2 : (x + n - 1) % n = (x + n - 1) - n * ((x + n - 1) / n) := by
      have := Nat.div_add_mod (x + n - 1) n
      omega
    rw [h2]
    exact Nat.dvd_sub hpxn h1
  have hdvd1 := Nat.dvd_gcd hpmod hpn
  rw [hg] at hdvd1
  exact absurd (Nat.dvd_one.mp hdvd1) (by omega)

/-- A prime-power Pocklington witness forces that power to divide `p - 1`
for every prime divisor `p` of the subject. The gcd uses a reduced subtraction,
so the zero-residue case does not rely on truncated natural subtraction. -/
theorem pocklington_pow {n q j a p : Nat} (hn : 2 ≤ n)
    (hq : Prime q) (hj : q ^ j ∣ n - 1)
    (hferm : a ^ (n - 1) % n = 1 % n)
    (hgcd : Nat.gcd ((a ^ ((n - 1) / q) % n + n - 1) % n) n = 1)
    (hp : Prime p) (hpn : p ∣ n) : q ^ j ∣ p - 1 := by
  have hferm_p : a ^ (n - 1) % p = 1 % p := by
    calc a ^ (n - 1) % p
        = a ^ (n - 1) % n % p := (Nat.mod_mod_of_dvd _ hpn).symm
      _ = 1 % n % p := by rw [hferm]
      _ = 1 % p := Nat.mod_mod_of_dvd _ hpn
  have hne_p : a ^ ((n - 1) / q) % p ≠ 1 % p := by
    have hxlt : a ^ ((n - 1) / q) % n < n := Nat.mod_lt _ (by omega)
    have hne := mod_ne_one_of_gcd hp.two_le hpn hxlt hgcd
    intro hc
    apply hne
    rw [Nat.mod_mod_of_dvd _ hpn]
    exact hc
  have hord := prime_pow_dvd_orderOf hq hj hp.one_lt hferm_p hne_p
  have hcop : Nat.Coprime a p :=
    coprime_of_pow_mod_eq_one hp.one_lt (by omega) hferm_p
  exact Nat.dvd_trans hord (orderOf_dvd_pred hp hcop)

/-- Square-root Pocklington: if every prime divisor of `n` is one modulo
`F` and `n < F²`, then `n` is prime. Factor assembly is left to the caller;
no certificate datatype or checker is involved. -/
theorem pocklington {n F : Nat} (hn : 2 ≤ n) (hFF : n < F * F)
    (hstep : ∀ p, Prime p → p ∣ n → F ∣ p - 1) : Prime n := by
  classical
  by_cases hp : Prime n
  · exact hp
  exfalso
  obtain ⟨p, hpprime, hpn, hpsq⟩ := exists_prime_le_sqrt hn hp
  have hp2 := hpprime.two_le
  have hFle : F ≤ p - 1 := Nat.le_of_dvd (by omega) (hstep p hpprime hpn)
  have hFp : F ≤ p := by omega
  have hsq : F * F ≤ p * p := Nat.mul_le_mul hFp hFp
  omega

end Blaster.FiniteField
