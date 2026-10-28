/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Blaster.FF04.Polynorm
import Tests.FiniteField.LargePrime

/-!
Project-authored algebraic representatives, NOT recovered Nethermind or historical
constraints, SMT proof-rule examples, or CPC probes. Run from the repository root:

    lake env lean fixtures/finite-fields/audit/Semantic.lean

Each reflected equality has an ordinary `decide` certificate and a proposition
obtained through the local normalizer's semantic bridge. The selected large prime
is imported, not re-proved or replaced with a merely similarly sized modulus.
Ring normalization needs only `NeZero`, not primality or a field instance.
No heartbeat override: these inputs deliberately stay at the bounded default.
The normalizer's equality test is sufficient, not complete (zero monomials can
survive); rejecting one certificate is not in general a semantic refutation.
-/

namespace FFM19.Semantic

open Blaster.FiniteField Blaster.FF04.Polynorm

abbrev F7 := Residue 7
abbrev P := Test.FiniteFieldLargePrime.curve25519
local instance : NeZero P := ⟨by decide⟩
abbrev FP := Residue P
abbrev E7 := Expr F7
abbrev EP := Expr FP

theorem selectedModulus : P = 2 ^ 255 - 19 :=
  Test.FiniteFieldLargePrime.curve25519_eq

theorem selectedPrime : Prime P :=
  Test.FiniteFieldLargePrime.curve25519_prime

-- Context slots 0 and 1 mean x and y respectively.
def squareL : E7 := .pow (.add (.var 0) (.var 1)) 2
def squareR : E7 :=
  .add (.add (.pow (.var 0) 2) (.mul (.val 2) (.mul (.var 0) (.var 1))))
    (.pow (.var 1) 2)

theorem squareCertificate : squareL.toPolynomial = squareR.toPolynomial := by decide

theorem square (ctx : Context F7) :
    (ctx 0 + ctx 1) ^ 2 = (ctx 0) ^ 2 + 2 * (ctx 0 * ctx 1) + (ctx 1) ^ 2 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) squareCertificate

def wrapL : E7 := .add (.val 5) (.val 3)
def wrapR : E7 := .val 1

theorem wrapCertificate : wrapL.toPolynomial = wrapR.toPolynomial := by decide

theorem wrap : (5 : F7) + 3 = 1 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := fun _ => 0) wrapCertificate

def characteristicL : E7 := .mul (.val 7) (.var 0)
def characteristicR : E7 := .val 0

theorem characteristicCertificate :
    characteristicL.toPolynomial = characteristicR.toPolynomial := by decide

theorem characteristic (ctx : Context F7) : (7 : F7) * ctx 0 = 0 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) characteristicCertificate

-- This is a recursive source operation, explicitly unfolded for this list.
def sumF : List F7 → F7
  | [] => 0
  | a :: as => a + sumF as

def sumL : E7 := .add (.var 0) (.add (.var 1) (.add (.neg (.var 0)) (.val 0)))
def sumR : E7 := .var 1

theorem sumCertificate : sumL.toPolynomial = sumR.toPolynomial := by decide

theorem sumCancellation (ctx : Context F7) : sumF [ctx 0, ctx 1, -ctx 0] = ctx 1 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) sumCertificate

-- A selected-prime identity with small coefficients and degree two.
def largeL : EP := .mul (.add (.var 0) (.val 1)) (.sub (.var 0) (.val 1))
def largeR : EP := .sub (.pow (.var 0) 2) (.val 1)

theorem largeCertificate : largeL.toPolynomial = largeR.toPolynomial := by decide

theorem largeIdentity (ctx : Context FP) :
    (ctx 0 + 1) * (ctx 0 - 1) = (ctx 0) ^ 2 - 1 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) largeCertificate

-- x = y implies x^2 + 3*x = y^2 + 3*y. The checked certificate
-- factors the conclusion residual; it does not encode an SMT implication rule.
def implicationL : EP :=
  .mul (.sub (.var 0) (.var 1)) (.add (.add (.var 0) (.var 1)) (.val 3))
def implicationR : EP :=
  .sub (.add (.pow (.var 0) 2) (.mul (.val 3) (.var 0)))
    (.add (.pow (.var 1) 2) (.mul (.val 3) (.var 1)))

theorem implicationCertificate :
    implicationL.toPolynomial = implicationR.toPolynomial := by decide

theorem implicationResidualZero (ctx : Context FP) (h : ctx 0 = ctx 1) :
    implicationL.eval ctx = 0 := by
  simp only [implicationL, Expr.eval]
  grind

theorem largeImplication (ctx : Context FP) (h : ctx 0 = ctx 1) :
    (ctx 0) ^ 2 + 3 * ctx 0 = (ctx 1) ^ 2 + 3 * ctx 1 := by
  have hc := Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) implicationCertificate
  have hz := implicationResidualZero ctx h
  have hr : implicationR.eval ctx = 0 := hc.symm.trans hz
  simp only [implicationR, Expr.eval] at hr
  grind

-- Here rejection is accompanied by an actual counterexample, not a failed tactic.
def falseL : E7 := .var 0
def falseR : E7 := .add (.var 0) (.val 1)
def counterexample : Context F7 := fun _ => 0

theorem rejectsFalseCertificate :
    decide (falseL.toPolynomial = falseR.toPolynomial) = false := by decide

theorem falseCounterexample : falseL.eval counterexample ≠ falseR.eval counterexample := by
  decide

theorem falseUniversal : ¬ ∀ ctx : Context F7, falseL.eval ctx = falseR.eval ctx := by
  intro h
  exact falseCounterexample (h counterexample)

-- Executable transitive trust audit, including the imported prime provenance.
run_cmd do
  for declaration in #[``selectedModulus, ``selectedPrime,
      ``squareCertificate, ``square, ``wrapCertificate, ``wrap,
      ``characteristicCertificate, ``characteristic, ``sumCertificate, ``sumCancellation,
      ``largeCertificate, ``largeIdentity, ``implicationCertificate,
      ``implicationResidualZero, ``largeImplication, ``rejectsFalseCertificate,
      ``falseCounterexample, ``falseUniversal] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom {axiomName} in {declaration}"

end FFM19.Semantic
