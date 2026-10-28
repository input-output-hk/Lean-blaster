/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Tests.Pure
import Blaster.FiniteField.PrimeOrder
import Blaster.FiniteField.PrimeBLS
import Blaster.FiniteField.PrimePower
import Blaster.FiniteField.Admission

/-!
The Curve25519 base-field proof, adapted from the literal witnesses in
HexPrimality/Examples/Curve25519.lean at
`e89daa43f1c6f2038a59674598e2a5097e64c3df`. This is a direct three-node
mathematical argument, not a certificate datatype, checker, or tactic.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Test.FiniteFieldLargePrime

open Blaster.FiniteField

private theorem prime2 : Prime 2 :=
  prime_of_bounded 2 1 (by decide) (by decide) (by decide)
private theorem prime223 : Prime 223 :=
  prime_of_bounded 223 14 (by decide) (by decide) (by decide)
private theorem prime353 : Prime 353 :=
  prime_of_bounded 353 18 (by decide) (by decide) (by decide)
private theorem prime4153 : Prime 4153 :=
  prime_of_bounded 4153 64 (by decide) (by decide) (by decide)
private theorem prime57467 : Prime 57467 :=
  prime_of_bounded 57467 239 (by decide) (by decide) (by decide)

/-- The selected modulus is Curve25519's base field, not its subgroup order. -/
def curve25519 : Nat :=
  57896044618658097711785492504343953926634992332820282019728792003956564819949

private def q : Nat :=
  74058212732561358302231226437062788676166966415465897661863160754340907
private def t : Nat := 31757755568855353

/-- Transport checked modular repeated-squaring equations into Pocklington's
mathematical witness obligations. All arithmetic hypotheses are kernel proofs. -/
private theorem factorStep {n c j a p : Nat} (hn : 2 ≤ n) (hc : Prime c)
    (hj : c ^ j ∣ n - 1) (he : n - 1 < 2 ^ 256)
    (hf : powMod 256 a (n - 1) n = 1 % n)
    (hg : Nat.gcd ((powMod 256 a ((n - 1) / c) n + n - 1) % n) n = 1)
    (hp : Prime p) (hpn : p ∣ n) : c ^ j ∣ p - 1 := by
  rw [powMod_eq _ _ _ _ he] at hf
  rw [powMod_eq _ _ _ _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) he)] at hg
  exact pocklington_pow hn hc hj hf hg hp hpn

private theorem primeT : Prime t := by
  apply pocklington3 (F := 7408952) (r := 4028945) (s := 289)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · exact Or.inr (Or.inr (not_square_of_sqrt_witness (w := 4028944)
      (by decide) (by decide)))
  · intro p hp hpn
    have h2 := factorStep (n := t) (c := 2) (j := 3) (a := 5)
      (by decide) prime2 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    have h223 := factorStep (n := t) (c := 223) (j := 1) (a := 2)
      (by decide) prime223 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    have h4153 := factorStep (n := t) (c := 4153) (j := 1) (a := 2)
      (by decide) prime4153 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime (8 * 223) 4153)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 8 223) h2 h223) h4153

private theorem primeQ : Prime q := by
  apply pocklington3 (F := 1288466195128439863020806)
    (r := 2028478494862525422475607) (s := 22304740449229861598212)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · exact Or.inr (Or.inr (not_square_of_sqrt_witness (w := 2028478494862525422475606)
      (by decide) (by decide)))
  · intro p hp hpn
    have h2 := factorStep (n := q) (c := 2) (j := 1) (a := 2)
      (by decide) prime2 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    have h353 := factorStep (n := q) (c := 353) (j := 1) (a := 2)
      (by decide) prime353 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    have h57467 := factorStep (n := q) (c := 57467) (j := 1) (a := 2)
      (by decide) prime57467 (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    have ht := factorStep (n := q) (c := t) (j := 1) (a := 2)
      (by decide) primeT (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by decide : Nat.Coprime (2 * 353 * 57467) t)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime (2 * 353) 57467)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 353) h2 h353) h57467) ht

/-- Kernel-checked primality of the exact selected Curve25519 base modulus. -/
theorem curve25519_prime : Prime curve25519 := by
  apply pocklington (F := q) (by decide) (by decide)
  intro p hp hpn
  exact factorStep (n := curve25519) (c := q) (j := 1) (a := 2)
    (by decide) primeQ (by decide) (by decide) (by decide +kernel) (by decide +kernel) hp hpn

/-- The decimal fixture and the RFC's modulus expression coincide. -/
theorem curve25519_eq : curve25519 = 2 ^ 255 - 19 := by decide

/-- Caller proof input: package the theorem, without registering a global instance. -/
theorem curve25519_evidence : PrimeModulus curve25519 := ⟨curve25519_prime⟩

/-- The RFC expression is also accepted as a reducible modulus alias. -/
def curve25519RFC : Nat := 2 ^ 255 - 19

open Lean Meta Blaster.Optimize in
run_meta do
  let check : TranslateEnvT Unit := do
    discard <| Optimize.main (mkRawNatLit 0)
    for modulus in #[mkRawNatLit curve25519, mkConst ``curve25519, mkConst ``curve25519RFC] do
      let type := mkApp (mkConst ``Residue) modulus
      let some d ← getResidueDescriptor? type
        | throwError "selected large residue modulus was not recognized"
      let admitted ← admitNativeField d (some (mkConst ``curve25519_evidence))
      unless admitted.residue.type == type && admitted.residue.modulusValue == curve25519 do
        throwError "large admission lost the exact carrier or normalized modulus"
      let expected := mkApp (mkConst ``PrimeModulus) (mkRawNatLit curve25519)
      unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx) (← inferType admitted.evidence) expected do
        throwError "large admission returned evidence for the wrong modulus"
      let missing ← try
        discard <| admitNativeField d
        pure false
      catch ex =>
        pure (((← ex.toMessageData.toString).splitOn "missing checked PrimeModulus").length > 1)
      unless missing do
        throwError "explicit large-prime evidence leaked into a later call"
    unless (← get).smtEnv.smtCommands.isEmpty && (← get).smtEnv.sessions.isEmpty do
      throwError "large-prime admission used a solver"
  discard <| check.run (default : TranslateEnv)

run_cmd do
  for declaration in #[``curve25519_prime, ``curve25519_eq, ``curve25519_evidence,
      ``powMod_eq, ``pocklington, ``pocklington3, ``pocklington_pow] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected large-prime axiom in {declaration}: {axiomName}"

end Test.FiniteFieldLargePrime
