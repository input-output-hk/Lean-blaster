; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --macros-quant --macros-quant-mode=all --check-unsat-cores
; EXPECT: sat
; EXPECT: (((f 0 7) 8) ((g 7) 8))
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-fun g (Int) Int)
(declare-fun f (Int Int) Int)
; Reconstruct values and retain core dependencies through both macro paths.
(assert (! (forall ((x Int)) (= (g x) (+ x 1))) :named full))
(assert (! (forall ((x Int)) (= (f 0 x) (g x))) :named partial))
(check-sat)
(get-value ((f 0 7) (g 7)))
(push 1)
(assert (! (= (f 0 7) 7) :named contradiction))
(check-sat)
(pop 1)
(check-sat)
