/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Tests.FF04.Polynorm
import Tests.FiniteField.LargePrime

/-!
Project-authored, fully specified circuit representatives. These are NOT recovered
Nethermind/historical constraints, FF proof-rule examples, solver replay, or CPC
probes. Run from the repository root:

    lake env lean fixtures/finite-fields/audit/Circuits.lean

Certificates are equalities of the existing reflected normalizer's polynomials,
proved by ordinary `decide`. The semantic bridge plus the explicit residual-zero
lemmas connects source gate constraints to the conclusion. No native proof path,
field division, primality search, or unbounded heartbeat override is used here.
The imported Curve25519 fixture supplies the exact modulus and prime provenance;
the algebra itself only uses the nominal residue ring's `NeZero` instance.
-/

namespace FFM19.Circuits

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

/-! Five F7 constraints. Slots: 0=x, 1=y, 2=m, 3=s.
The gates assert x=2, y=3, m=x*y, s=m+x, s=0. They force s=1,
so no assignment satisfies all five. Every constraint is used in the certificate.
-/
def FiveConstraints (ctx : Context F7) : Prop :=
  ctx 0 = 2 ∧ ctx 1 = 3 ∧ ctx 2 = ctx 0 * ctx 1 ∧
    ctx 3 = ctx 2 + ctx 0 ∧ ctx 3 = 0

def fiveR0 : E7 := .sub (.var 0) (.val 2)
def fiveR1 : E7 := .sub (.var 1) (.val 3)
def fiveR2 : E7 := .sub (.var 2) (.mul (.var 0) (.var 1))
def fiveR3 : E7 := .sub (.var 3) (.add (.var 2) (.var 0))
def fiveR4 : E7 := .var 3

-- r4 - r3 - r2 - (y+1)*r0 - 2*r1 = 8 = 1 in F7.
def fiveL : E7 :=
  .sub (.sub (.sub (.sub fiveR4 fiveR3) fiveR2)
    (.mul (.add (.var 1) (.val 1)) fiveR0)) (.mul (.val 2) fiveR1)
def fiveR : E7 := .val 1

theorem fiveCertificate : fiveL.toPolynomial = fiveR.toPolynomial := by decide

theorem fiveIdentity (ctx : Context F7) :
    ctx 3 - (ctx 3 - (ctx 2 + ctx 0)) - (ctx 2 - ctx 0 * ctx 1) -
      (ctx 1 + 1) * (ctx 0 - 2) - 2 * (ctx 1 - 3) = 1 := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) fiveCertificate

theorem fiveResidualsZero (ctx : Context F7) (h : FiveConstraints ctx) :
    fiveR0.eval ctx = 0 ∧ fiveR1.eval ctx = 0 ∧ fiveR2.eval ctx = 0 ∧
      fiveR3.eval ctx = 0 ∧ fiveR4.eval ctx = 0 := by
  rcases h with ⟨hx, hy, hm, hs, hzero⟩
  simp only [fiveR0, fiveR1, fiveR2, fiveR3, fiveR4, Expr.eval]
  grind

theorem fiveCombinationZero (ctx : Context F7) (h : FiveConstraints ctx) :
    fiveL.eval ctx = 0 := by
  rcases fiveResidualsZero ctx h with ⟨h0, h1, h2, h3, h4⟩
  simp only [fiveL, Expr.eval, h0, h1, h2, h3, h4]
  grind

theorem fiveContradiction (ctx : Context F7) : ¬ FiveConstraints ctx := by
  intro h
  have hc : fiveL.eval ctx = (1 : F7) :=
    Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) fiveCertificate
  have hz := fiveCombinationZero ctx h
  exact (by decide : (0 : F7) ≠ 1) (hz.symm.trans hc)

/-! Eight selected-prime gates, with unconstrained inputs x,y.
Slots: 0=x, 1=y, 2=u, 3=v, 4=w, 5=t, 6=z, 7=a, 8=b, 9=out.

u=x+y; v=u*x; w=v+y; t=w*x; z=t+y; a=z*x; b=a+y; out=b*x.

The output expands to x^5 + x^4*y + x^3*y + x^2*y + x*y.
This is an eight-gate straight-line circuit, not a cryptographic production circuit.
-/
def ChainConstraints (ctx : Context FP) : Prop :=
  ctx 2 = ctx 0 + ctx 1 ∧
  ctx 3 = ctx 2 * ctx 0 ∧
  ctx 4 = ctx 3 + ctx 1 ∧
  ctx 5 = ctx 4 * ctx 0 ∧
  ctx 6 = ctx 5 + ctx 1 ∧
  ctx 7 = ctx 6 * ctx 0 ∧
  ctx 8 = ctx 7 + ctx 1 ∧
  ctx 9 = ctx 8 * ctx 0

def chainR0 : EP := .sub (.var 2) (.add (.var 0) (.var 1))
def chainR1 : EP := .sub (.var 3) (.mul (.var 2) (.var 0))
def chainR2 : EP := .sub (.var 4) (.add (.var 3) (.var 1))
def chainR3 : EP := .sub (.var 5) (.mul (.var 4) (.var 0))
def chainR4 : EP := .sub (.var 6) (.add (.var 5) (.var 1))
def chainR5 : EP := .sub (.var 7) (.mul (.var 6) (.var 0))
def chainR6 : EP := .sub (.var 8) (.add (.var 7) (.var 1))
def chainR7 : EP := .sub (.var 9) (.mul (.var 8) (.var 0))

def chainOutput : EP :=
  .add (.add (.add (.add (.pow (.var 0) 5)
    (.mul (.pow (.var 0) 4) (.var 1)))
    (.mul (.pow (.var 0) 3) (.var 1)))
    (.mul (.pow (.var 0) 2) (.var 1))) (.mul (.var 0) (.var 1))

-- Horner presentation of the weighted residual sum:
-- x^4*r0 + x^3*(r1+r2) + x^2*(r3+r4) + x*(r5+r6) + r7.
def chainL : EP :=
  .add chainR7 (.mul (.var 0)
    (.add (.add chainR6 chainR5) (.mul (.var 0)
      (.add (.add chainR4 chainR3) (.mul (.var 0)
        (.add (.add chainR2 chainR1) (.mul (.var 0) chainR0)))))))
def chainR : EP := .sub (.var 9) chainOutput

theorem chainCertificate : chainL.toPolynomial = chainR.toPolynomial := by decide

theorem chainIdentity (ctx : Context FP) :
    (ctx 9 - ctx 8 * ctx 0) + ctx 0 *
      ((ctx 8 - (ctx 7 + ctx 1)) + (ctx 7 - ctx 6 * ctx 0) + ctx 0 *
        ((ctx 6 - (ctx 5 + ctx 1)) + (ctx 5 - ctx 4 * ctx 0) + ctx 0 *
          ((ctx 4 - (ctx 3 + ctx 1)) + (ctx 3 - ctx 2 * ctx 0) + ctx 0 *
            (ctx 2 - (ctx 0 + ctx 1))))) =
    ctx 9 - ((ctx 0) ^ 5 + (ctx 0) ^ 4 * ctx 1 + (ctx 0) ^ 3 * ctx 1 +
      (ctx 0) ^ 2 * ctx 1 + ctx 0 * ctx 1) := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) chainCertificate

theorem chainResidualsZero (ctx : Context FP) (h : ChainConstraints ctx) :
    chainR0.eval ctx = 0 ∧ chainR1.eval ctx = 0 ∧ chainR2.eval ctx = 0 ∧
    chainR3.eval ctx = 0 ∧ chainR4.eval ctx = 0 ∧ chainR5.eval ctx = 0 ∧
    chainR6.eval ctx = 0 ∧ chainR7.eval ctx = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simp only [chainR0, chainR1, chainR2, chainR3, chainR4, chainR5, chainR6, chainR7,
    Expr.eval]
  grind

theorem chainCombinationZero (ctx : Context FP) (h : ChainConstraints ctx) :
    chainL.eval ctx = 0 := by
  rcases chainResidualsZero ctx h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simp only [chainL, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7]
  grind

theorem chainConclusion (ctx : Context FP) (h : ChainConstraints ctx) :
    ctx 9 = (ctx 0) ^ 5 + (ctx 0) ^ 4 * ctx 1 + (ctx 0) ^ 3 * ctx 1 +
      (ctx 0) ^ 2 * ctx 1 + ctx 0 * ctx 1 := by
  have hc := Expr.denote_eq_from_toPolynomial_eq (ctx := ctx) chainCertificate
  have hz := chainCombinationZero ctx h
  have hr : chainR.eval ctx = 0 := hc.symm.trans hz
  simp only [chainR, chainOutput, Expr.eval] at hr
  grind

-- Executable transitive trust audit, including the imported prime provenance.
run_cmd do
  for declaration in #[``selectedModulus, ``selectedPrime,
      ``fiveCertificate, ``fiveIdentity, ``fiveResidualsZero,
      ``fiveCombinationZero, ``fiveContradiction, ``chainCertificate,
      ``chainIdentity, ``chainResidualsZero, ``chainCombinationZero, ``chainConclusion] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom {axiomName} in {declaration}"

end FFM19.Circuits
