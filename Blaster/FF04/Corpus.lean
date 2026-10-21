import Blaster.FF04.Nominal
import Blaster.FF04.Polynorm

/-!
FF-04 bounded, explicitly reified certificate corpus. Both comparison files use
these exact goals over the same nominal `Residue 65537` representation. Reification
is not timed or implemented: this measures proof reconstruction, not solver time.
The algorithm is the core-only adaptation, not a build of upstream lean-smt.
-/
namespace Test.FiniteFieldPolynorm

open Blaster.FF04 Blaster.FF04.Polynorm

abbrev F := Residue 65537
abbrev E := Expr F

def distributeL : E := .mul (.add (.var 0) (.var 1)) (.var 2)
def distributeR : E := .add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))

def characteristicL : E := .add (.add (.mul (.val 65536) (.var 0)) (.var 0)) (.var 1)
def characteristicR : E := .var 1

def nestedL : E :=
  .mul (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
def nestedR : E :=
  .add (.add (.add (.add
    (.pow (.var 0) 4)
    (.mul (.val 4) (.mul (.pow (.var 0) 3) (.var 1))))
    (.mul (.val 6) (.mul (.pow (.var 0) 2) (.pow (.var 1) 2))))
    (.mul (.val 4) (.mul (.var 0) (.pow (.var 1) 3))))
    (.pow (.var 1) 4)

def coefficientsL : E :=
  .mul (.add (.mul (.val 123456789) (.var 0)) (.mul (.val 987654321) (.var 1)))
    (.add (.mul (.val 7654321) (.var 0)) (.mul (.val 1234567) (.var 1)))
def coefficientsR : E :=
  .add (.add
    (.mul (.val (123456789 * 7654321)) (.pow (.var 0) 2))
    (.mul (.val (123456789 * 1234567 + 987654321 * 7654321)) (.mul (.var 0) (.var 1))))
    (.mul (.val (987654321 * 1234567)) (.pow (.var 1) 2))

-- These are kernel-checked propositions, not assertions trusting an evaluated Bool.
theorem rejectsFalseCertificate :
    decide ((Expr.var 0 : E).toPolynomial = (Expr.add (.var 0) (.val 1) : E).toPolynomial)
      = false := by decide

theorem acceptsTrueCertificate :
    decide (distributeL.toPolynomial = distributeR.toPolynomial) = true := by decide

-- Upstream does not remove every zero-coefficient monomial. Preserve and expose
-- this limitation instead of claiming a complete decision procedure for equality.
def zeroProduct : Expr (Residue 6) :=
  .mul (.mul (.val 2) (.var 0)) (.mul (.val 3) (.var 0))

theorem zeroProductNotCanonical :
    decide (zeroProduct.toPolynomial = (Expr.val (0 : Residue 6)).toPolynomial)
      = false := by decide

theorem zeroProductSemanticallyZero (ctx : Context (Residue 6)) :
    zeroProduct.eval ctx = 0 := by
  simp only [zeroProduct, Expr.eval]
  grind

#print axioms Expr.denote_eq_from_toPolynomial_eq
#print axioms rejectsFalseCertificate
#print axioms acceptsTrueCertificate
#print axioms zeroProductNotCanonical
#print axioms zeroProductSemanticallyZero

end Test.FiniteFieldPolynorm
