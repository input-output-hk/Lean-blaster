/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Blaster.FiniteField.Prime

/-! Fermat's little theorem, selectively adapted from HexArith/Nat/Prime.lean
at `5ae42d0127e49eb3973ae01a5304a7adb2a9ee65`. The Pascal definitions
are proof-only; no binomial evaluator or trial-primality infrastructure is included. -/

set_option maxHeartbeats 800000

namespace Blaster.FiniteField

noncomputable section

/--
Binomial coefficients on natural numbers, defined by the Pascal recursion.
-/
noncomputable def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `choose n 0 = 1`: the zeroth column of Pascal's triangle. -/
@[simp, grind =] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [choose]

/--
`choose 0 (k + 1) = 0`: nontrivial entries vanish in the top row of Pascal's
triangle.
-/
@[simp, grind =] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := by
  rfl

/-- Pascal's recurrence: `choose (n + 1) (k + 1) = choose n k + choose n (k + 1)`. -/
@[simp, grind =] theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  rfl

/--
Entries past the diagonal of Pascal's triangle vanish: `choose n k = 0`
whenever `n < k`.
-/
theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp [choose]
          by_cases hk : n < k
          · simp [ih hk]
            exact ih (by omega)
          · exfalso
            omega

/-- The diagonal of Pascal's triangle is constantly one: `choose n n = 1`. -/
@[simp, grind =] theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose, ih, choose_eq_zero_of_lt (by omega : n < n + 1)]

/-- A positive integer below a modulus cannot be divisible by it. -/
private theorem not_dvd_of_pos_lt {p k : Nat} (hk : 0 < k) (hk' : k < p) :
    ¬ p ∣ k := by
  intro hpk
  rcases hpk with ⟨c, hc⟩
  have hc_pos : 0 < c := by
    cases c with
    | zero => omega
    | succ c => exact Nat.succ_pos c
  have : p ≤ k := by
    rw [hc]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hc_pos
  omega

/-- Choosing one element counts the row index. -/
private theorem choose_one_right (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose]
      rw [ih]
      omega

/-- Multiplicative Pascal identity used to move from row recurrence to prime divisibility. -/
private theorem choose_succ_mul_eq (n k : Nat) :
    (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [choose]
  | succ n ih =>
      cases k with
      | zero =>
          simp [choose, choose_one_right]
          omega
      | succ k =>
          grind [choose]

/-- Euclid-step correspondence turning the multiplicative Pascal identity into `p ∣ choose p k`. -/
private theorem choose_prime_dvd_from_mul_identity {p k : Nat} (hp : Prime p)
    (hk : 0 < k) (hk' : k < p) : p ∣ choose p k := by
  cases k with
  | zero => omega
  | succ k =>
      cases p with
      | zero => omega
      | succ p =>
          have hmul : p + 1 ∣ (k + 1) * choose (p + 1) (k + 1) := by
            rw [choose_succ_mul_eq]
            exact Nat.dvd_mul_right (p + 1) (choose p k)
          rcases (Prime.dvd_mul hp).mp hmul with hdiv | hdiv
          · exact False.elim (not_dvd_of_pos_lt hk hk' hdiv)
          · exact hdiv

/-- The `k`th binomial term `choose n k * a^(n-k) * b^k` in `(a + b)^n`. -/
private def chooseTerm (n a b k : Nat) : Nat :=
  choose n k * a ^ (n - k) * b ^ k

/-- Partial sum of the first binomial terms used to prove `(a + b)^n`. -/
private def chooseSum (n a b : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => chooseSum n a b k + chooseTerm n a b k

/-- Row recurrence for binomial partial sums across adjacent Pascal rows. -/
private theorem chooseSum_succ_row (n a b m : Nat) (hm : m ≤ n + 1) :
    chooseSum (n + 1) a b (m + 1) =
      a * chooseSum n a b (m + 1) + b * chooseSum n a b m := by
  induction m with
  | zero =>
      simp [chooseSum, chooseTerm, Nat.pow_succ]
      rw [Nat.mul_comm]
  | succ m ih =>
      rw [chooseSum, ih (by omega)]
      unfold chooseTerm
      by_cases hlt : m < n
      · have hpow : a ^ (n - m) = a * a ^ (n - (m + 1)) := by
          have hsub' : n - m = n - (m + 1) + 1 := by omega
          rw [hsub', Nat.pow_succ, Nat.mul_comm]
        simp [chooseSum, chooseTerm, choose_succ_succ, hpow, Nat.pow_succ,
          Nat.mul_add, Nat.add_mul, Nat.add_assoc]
        ac_rfl
      · have hmn : m = n := by omega
        subst m
        have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
        simp [chooseSum, chooseTerm, choose_succ_succ, hzero, Nat.pow_succ,
          Nat.mul_add, Nat.add_assoc]
        ac_rfl

/-- Binomial expansion packaged as equality with the full `chooseSum` row. -/
private theorem add_pow_chooseSum (n a b : Nat) :
    (a + b) ^ n = chooseSum n a b (n + 1) := by
  induction n with
  | zero =>
      simp [chooseSum, chooseTerm]
  | succ n ih =>
      calc
        (a + b) ^ (n + 1) = (a + b) ^ n * (a + b) := Nat.pow_succ (a + b) n
        _ = (a + b) ^ n * a + (a + b) ^ n * b := by rw [Nat.mul_add]
        _ = a * chooseSum n a b (n + 1) + b * chooseSum n a b (n + 1) := by
            rw [ih]
            ac_rfl
        _ = a * chooseSum n a b (n + 1 + 1) + b * chooseSum n a b (n + 1) := by
            have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
            have htail : chooseSum n a b (n + 1 + 1) = chooseSum n a b (n + 1) := by
              simp [chooseSum, chooseTerm, hzero]
            rw [htail]
        _ = chooseSum (n + 1) a b (n + 1 + 1) :=
            (chooseSum_succ_row n a b (n + 1) (by omega)).symm

/-- Middle binomial terms are divisible by `p` once their coefficients are. -/
private theorem chooseTerm_dvd_of_middle {p a b k : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hk0 : 0 < k) (hkp : k < p) : p ∣ chooseTerm p a b k := by
  unfold chooseTerm
  simpa [Nat.mul_assoc] using
    Nat.dvd_mul_right_of_dvd (hchoose k hk0 hkp) (a ^ (p - k) * b ^ k)

/-- Middle binomial terms vanish modulo `p` under the prime-row divisibility hypothesis. -/
private theorem chooseTerm_mod_eq_zero_of_middle {p a b k : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hk0 : 0 < k) (hkp : k < p) : chooseTerm p a b k % p = 0 := by
  exact Nat.mod_eq_zero_of_dvd (chooseTerm_dvd_of_middle hchoose hk0 hkp)

/-- Prefix sums modulo `p` reduce to the leading term after erasing middle terms. -/
private theorem chooseSum_prefix_mod {p a b m : Nat}
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k)
    (hm0 : 0 < m) (hmp : m ≤ p) : chooseSum p a b m % p = a ^ p % p := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          simp [chooseSum, chooseTerm]
      | succ m =>
          have hprev : chooseSum p a b (m + 1) % p = a ^ p % p := by
            exact ih (by omega) (by omega)
          have hterm :
              chooseTerm p a b (m + 1) % p = 0 :=
            chooseTerm_mod_eq_zero_of_middle hchoose (by omega) (by omega)
          calc
            chooseSum p a b (m + 1 + 1) % p
                = (chooseSum p a b (m + 1) + chooseTerm p a b (m + 1)) % p := by
                    rfl
            _ = (chooseSum p a b (m + 1) % p
                  + chooseTerm p a b (m + 1) % p) % p := Nat.add_mod _ _ _
            _ = a ^ p % p := by
                  rw [hprev, hterm, Nat.add_zero, Nat.mod_mod]

/-- Freshman's-dream step modulo `p`, abstracted over binomial divisibility. -/
private theorem add_pow_prime_mod_of_choose_dvd {p : Nat} (hp : Prime p) (a b : Nat)
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  have hp_pos : 0 < p := by
    have htwo := hp.1
    omega
  have hprefix : chooseSum p a b p % p = a ^ p % p :=
    chooseSum_prefix_mod hchoose hp_pos (Nat.le_refl p)
  have hlast : chooseTerm p a b p = b ^ p := by
    simp [chooseTerm, choose_self]
  calc
    (a + b) ^ p % p = chooseSum p a b (p + 1) % p := by
      rw [add_pow_chooseSum]
    _ = (chooseSum p a b p + chooseTerm p a b p) % p := by
      rfl
    _ = (chooseSum p a b p % p + chooseTerm p a b p % p) % p := Nat.add_mod _ _ _
    _ = (a ^ p % p + b ^ p % p) % p := by
      rw [hprefix, hlast]
    _ = (a ^ p + b ^ p) % p := by
      rw [← Nat.add_mod]

/-- Derives Fermat's little theorem by induction from the Freshman's-dream step. -/
private theorem pow_prime_mod_from_add_pow {p : Nat} (hp : Prime p) (a : Nat)
    (hadd : ∀ a b, (a + b) ^ p % p = (a ^ p + b ^ p) % p) :
    a ^ p % p = a % p := by
  have hp_pos : 0 < p := by
    have htwo := hp.1
    omega
  induction a with
  | zero => simp [Nat.zero_pow hp_pos]
  | succ a ih =>
      have h := hadd a 1
      simp [Nat.one_pow] at h
      calc
        (a + 1) ^ p % p = (a ^ p + 1) % p := h
        _ = (a ^ p % p + 1) % p := (Nat.mod_add_mod (a ^ p) p 1).symm
        _ = (a % p + 1) % p := by rw [ih]
        _ = (a + 1) % p := Nat.mod_add_mod a p 1

/--
Every nontrivial binomial coefficient in the `p`th row of Pascal's triangle is
divisible by `p` when `p` is prime. This is the binomial-divisibility fact used
to erase the middle terms in `add_pow_prime_mod`.
-/
theorem choose_prime_dvd {p k : Nat} (hp : Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ choose p k := by
  exact choose_prime_dvd_from_mul_identity hp hk hk'

/--
Freshman's dream modulo a prime: `(a + b)^p` is congruent to `a^p + b^p`
modulo `p`, because all middle binomial terms vanish.
-/
theorem add_pow_prime_mod {p : Nat} (hp : Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  exact add_pow_prime_mod_of_choose_dvd hp a b (fun k hk hk' =>
    choose_prime_dvd hp hk hk')

/--
Fermat's little theorem in the residue form used by downstream modular
arithmetic code: raising a natural number to the `p`th power preserves its
residue modulo a prime `p`.
-/
theorem pow_prime_mod {p : Nat} (hp : Prime p) (a : Nat) :
    a ^ p % p = a % p := by
  exact pow_prime_mod_from_add_pow hp a (fun a b => add_pow_prime_mod hp a b)

end

end Blaster.FiniteField
