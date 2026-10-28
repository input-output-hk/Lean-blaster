import Tests.Pure
import Blaster.FiniteField.Basic
import Blaster.FiniteField.Residue
import Blaster.FiniteField
import Tests.FF04.Nominal
import Tests.FF04.Corpus
import Tests.FF04.Replay

namespace Test.FiniteFieldCarrier

open Blaster.FiniteField

-- All ring assumptions are nonzeroness, not primality, even for symbolic p.
example (p : Nat) [NeZero p] : Lean.Grind.CommRing (Residue p) := inferInstance
example (p : Nat) [NeZero p] : Lean.Grind.IsCharP (Residue p) p := inferInstance
example (p : Nat) [NeZero p] : Inhabited (Residue p) := inferInstance
example (p : Nat) : DecidableEq (Residue p) := inferInstance
example (p : Nat) : Repr (Residue p) := inferInstance

theorem symbolicDistribute (p : Nat) [NeZero p] (a b c : Residue p) :
    a * (b + c) = a * b + a * c :=
  Lean.Grind.Semiring.left_distrib a b c

theorem symbolicPolynomial (p : Nat) [NeZero p] (a b : Residue p) :
    (a + b) * (a - b) = a * a - b * b := by
  grind

theorem symbolicNeg (p : Nat) [NeZero p] (a : Residue p) : -a + a = 0 :=
  Lean.Grind.Ring.neg_add_cancel a

theorem symbolicPower (p : Nat) [NeZero p] (a : Residue p) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n :=
  Lean.Grind.Semiring.pow_add a m n

theorem symbolicNatCast (p : Nat) [NeZero p] (m n : Nat) :
    ((m + n : Nat) : Residue p) = (m : Residue p) + (n : Residue p) :=
  Lean.Grind.Semiring.natCast_add m n

theorem symbolicIntCast (p : Nat) [NeZero p] (n : Int) :
    ((-n : Int) : Residue p) = -(n : Residue p) :=
  Lean.Grind.Ring.intCast_neg n

theorem symbolicCharacteristic (p : Nat) [NeZero p] (n : Nat) :
    (n : Residue p) = 0 ↔ n % p = 0 :=
  Lean.Grind.IsCharP.natCast_eq_zero_iff p n

-- The representation and extensionality do not require a ring instance.
theorem representationExt (p : Nat) (a b : Residue p) (h : a.rep = b.rep) : a = b :=
  Residue.ext h

theorem zeroEmpty (a : Residue 0) : False := Nat.not_lt_zero a.rep.val a.rep.isLt

-- These operations act on the empty carrier too; only the ring needs NeZero.
example : Add (Residue 0) := inferInstance
example : Mul (Residue 0) := inferInstance
example : Neg (Residue 0) := inferInstance
example : Sub (Residue 0) := inferInstance

example : True := by
  fail_if_success have : NeZero 0 := inferInstance
  fail_if_success have : Inhabited (Residue 0) := inferInstance
  fail_if_success have : OfNat (Residue 0) 0 := inferInstance
  fail_if_success have : NatCast (Residue 0) := inferInstance
  fail_if_success have : IntCast (Residue 0) := inferInstance
  fail_if_success have : HPow (Residue 0) Nat (Residue 0) := inferInstance
  fail_if_success have : Lean.Grind.CommRing (Residue 0) := inferInstance
  fail_if_success have : Lean.Grind.IsCharP (Residue 0) 0 := inferInstance
  trivial

example : Lean.Grind.CommRing (Residue 1) := inferInstance
example : Lean.Grind.IsCharP (Residue 1) 1 := inferInstance

theorem oneZeroRing : (0 : Residue 1) = 1 := by decide

theorem oneUnique (a b : Residue 1) : a = b := by
  apply Residue.ext
  apply Fin.ext
  have ha := a.rep.isLt
  have hb := b.rep.isLt
  omega

example : Lean.Grind.CommRing (Residue 6) := inferInstance
example : Lean.Grind.IsCharP (Residue 6) 6 := inferInstance

theorem compositeZeroDivisors : (2 : Residue 6) ≠ 0 ∧ (3 : Residue 6) ≠ 0 ∧
    (2 : Residue 6) * 3 = 0 := by decide

theorem compositeSubtraction : (1 : Residue 6) - 3 = 4 := by decide

theorem characteristicTwo (a : Residue 2) : a + a = 0 := by grind

theorem characteristicTwoNegation (a : Residue 2) : -a = a := by grind

theorem characteristicSeven (a : Residue 7) : 7 * a = 0 := by grind

theorem characteristicEleven (a : Residue 11) : 11 * a = 0 := by grind

theorem oddNegation : -(3 : Residue 7) = 4 ∧ -(3 : Residue 11) = 8 := by decide

def seven : Nat := 7
instance sevenNonzero : NeZero seven := ⟨by decide⟩
def nineteen : Nat := 19
abbrev SevenResidue := Residue seven

theorem modulusAlias : (19 : SevenResidue) = (5 : Residue 7) := by decide

theorem numeralIndexAlias :
    @OfNat.ofNat (Residue 7) nineteen inferInstance = (5 : Residue 7) := by decide

theorem closedPowers : (3 : Residue 7) ^ (4 : Nat) = 4 ∧
    (2 : Residue 11) ^ (10 : Nat) = 1 ∧ (0 : Residue 6) ^ (0 : Nat) = 1 := by decide

theorem closedCasts : ((19 : Nat) : Residue 7) = 5 ∧
    ((-19 : Int) : Residue 7) = 2 ∧ ((-13 : Int) : Residue 6) = 5 := by decide

-- No algebra import route, including the root imported by Tests.Pure, supplies
-- inverse/division just from nonzeroness, or for the numeric prime examples.
example (p : Nat) [NeZero p] : True := by
  fail_if_success have : Inv (Residue p) := inferInstance
  fail_if_success have : Div (Residue p) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue p) := inferInstance
  trivial

example : True := by
  fail_if_success have : Inv (Residue 0) := inferInstance
  fail_if_success have : Div (Residue 0) := inferInstance
  fail_if_success have : Inv (Residue 1) := inferInstance
  fail_if_success have : Div (Residue 1) := inferInstance
  fail_if_success have : Inv (Residue 6) := inferInstance
  fail_if_success have : Div (Residue 6) := inferInstance
  fail_if_success have : Inv (Residue 2) := inferInstance
  fail_if_success have : Div (Residue 2) := inferInstance
  fail_if_success have : Inv (Residue 7) := inferInstance
  fail_if_success have : Div (Residue 7) := inferInstance
  fail_if_success have : Inv (Residue 11) := inferInstance
  fail_if_success have : Div (Residue 11) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue 1) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue 6) := inferInstance
  fail_if_success have : Lean.Grind.Field (Residue 7) := inferInstance
  trivial

-- Compatibility is definitionally identical, including each retained spelling.
theorem compatibilityType (p : Nat) : Blaster.FF04.Residue p = Residue p := rfl

theorem compatibilityValue (p : Nat) (a : Blaster.FF04.Residue p) :
    (show Residue p from a) = a := rfl

theorem compatibilityMk (p : Nat) (a : Fin p) :
    Blaster.FF04.Residue.mk a = Residue.mk a := rfl

theorem compatibilityRep (p : Nat) (a : Residue p) :
    Blaster.FF04.Residue.rep a = a.rep := rfl

theorem compatibilityExt (p : Nat) (a b : Blaster.FF04.Residue p)
    (h : Blaster.FF04.Residue.rep a = Blaster.FF04.Residue.rep b) : a = b :=
  Blaster.FF04.Residue.ext h

theorem compatibilityInjEq (p : Nat) (a b : Fin p) :
    (Blaster.FF04.Residue.mk a = Blaster.FF04.Residue.mk b) = (a = b) :=
  Blaster.FF04.Residue.mk.injEq a b

-- Replay and the normalizer consume the canonical carrier, not a second key.
open Blaster.FF04.Replay

theorem canonicalReplay (x : Residue 7) (h : x = 2) : x * x = 4 := by
  ff04_replay "(
    (declare-const x (_ FiniteField 7))
    (assume @p1 (= x (ff.value 7 2)))
    (assume @p2 (not (= (ff.mul x x) (ff.value 7 4))))
    (step @p3 false :rule eq_resolve :premises (@p1 @p2)))"

open Blaster.FF04.Polynorm in
theorem canonicalNormalizer (ctx : Context (Residue 65537)) :
    Test.FiniteFieldPolynorm.distributeL.eval ctx =
      Test.FiniteFieldPolynorm.distributeR.eval ctx := by
  apply Expr.denote_eq_from_toPolynomial_eq
  decide

-- These are executable transitive audits, not just informational #print output.
run_cmd do
  let declarations := #[
    ``Residue.ext, ``Residue.instCommRing, ``Residue.instIsCharP,
    ``symbolicDistribute, ``symbolicPolynomial, ``symbolicNeg, ``symbolicPower,
    ``symbolicNatCast, ``symbolicIntCast, ``symbolicCharacteristic,
    ``representationExt, ``zeroEmpty, ``oneZeroRing, ``oneUnique,
    ``compositeZeroDivisors, ``compositeSubtraction,
    ``characteristicTwo, ``characteristicTwoNegation,
    ``characteristicSeven, ``characteristicEleven, ``oddNegation,
    ``sevenNonzero, ``modulusAlias, ``numeralIndexAlias, ``closedPowers, ``closedCasts,
    ``compatibilityType, ``compatibilityValue, ``compatibilityMk,
    ``compatibilityRep, ``compatibilityExt, ``compatibilityInjEq,
    ``canonicalReplay, ``canonicalNormalizer]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected carrier axiom in {declaration}: {axiomName}"

end Test.FiniteFieldCarrier
