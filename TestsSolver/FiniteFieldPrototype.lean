import Blaster.FF04.Replay

namespace Blaster.FF04.Tests
open Replay

/-- Actual cvc5 1.4.1 CPC output with explicit conclusions. The solver's
`trust` label is independently checked by Lean, not adopted as an axiom. -/
theorem originalGoal (x : Residue 7) (h : x = 2) : x * x = 4 := by
  ff04_replay "unsat
(
(declare-const x (_ FiniteField 7))
(define @t1 () (ff.value 7 2))
(define @t2 () (ff.value 7 4))
(define @t3 () (ff.mul x x))
(define @t4 () (= @t3 @t2))
(define @t5 () (not @t4))
(define @t6 () (not true))
(define @t7 () (= @t2 @t2))
(define @t8 () (ff.mul @t1 @t1))
(define @t9 () (= @t8 @t2))
(define @t10 () (not @t9))
(assume @p1 (= x @t1))
(assume @p2 @t5)
(step @p3 (= @t6 false) :rule evaluate :args (@t6))
(step @p4 (= @t7 true) :rule eq-refl :args (@t2))
(step @p5 @t7 :rule refl :args (@t2))
; WARNING: add trust step for TRUST_THEORY_REWRITE
; trust TRUST_THEORY_REWRITE
(step @p6 @t9 :rule trust :premises () :args (@t9))
(step @p7 (= @t9 @t7) :rule cong :premises (@p6 @p5) :args (@t9))
(step @p8 (= @t9 true) :rule trans :premises (@p7 @p4))
(step @p9 (= @t10 @t6) :rule cong :premises (@p8) :args (@t10))
(step @p10 (= @t10 false) :rule trans :premises (@p9 @p3))
(step @p11 (= @t3 @t8) :rule nary_cong :premises (@p1 @p1) :args (@t3))
(step @p12 (= @t4 @t9) :rule cong :premises (@p11 @p5) :args (@t4))
(step @p13 (= @t5 @t10) :rule cong :premises (@p12) :args (@t5))
(step @p14 (= @t5 false) :rule trans :premises (@p13 @p10))
(step @p15 false :rule eq_resolve :premises (@p2 @p14))
)"

-- False solver claims cannot discharge even an otherwise provable original goal.
example (x : Residue 7) (h : x = 2) : x * x = 4 := by
  fail_if_success ff04_replay "(
    (declare-const x (_ FiniteField 7))
    (assume @p1 (= x (ff.value 7 3)))
    (step @p2 false :rule trust))"
  fail_if_success ff04_replay "(
    (declare-const x (_ FiniteField 7))
    (step @p1 (= (ff.value 7 2) (ff.value 7 3)) :rule trust))"
  fail_if_success ff04_replay "(
    (declare-const x (_ FiniteField 11))
    (step @p1 false :rule trust))"
  fail_if_success ff04_replay "(
    (declare-const x (_ FiniteField 7))
    (step @p1 false :rule eq_resolve :premises (@missing)))"
  exact originalGoal x h

-- A contradiction in the original context must not leak into a premise-free step.
example (x : Residue 7) (bad : False) : x * x = 4 := by
  fail_if_success ff04_replay "(
    (declare-const x (_ FiniteField 7))
    (step @p1 false :rule trust))"
  exact False.elim bad

#print axioms originalGoal

-- Check transitive proof dependencies, including native-decision trust.
run_cmd do
  let axioms ← Lean.collectAxioms ``originalGoal
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected reconstruction axiom: {axiomName}"

end Blaster.FF04.Tests
