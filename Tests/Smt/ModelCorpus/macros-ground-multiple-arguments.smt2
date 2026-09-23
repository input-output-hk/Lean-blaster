; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --macros-quant --macros-quant-mode=all --check-unsat-cores
; EXPECT: sat
; EXPECT: (((f 3 5 true 2) 205) ((f 4 5 true 2) 99) ((f 3 5 false 2) 88))
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-fun f (Int Int Bool Int) Int)
; Two fixed arguments and two variables in the reverse of binder order.
(assert (forall ((x Int) (y Int)) (= (f 3 y true x) (+ (* 100 x) y))))
; Both ways of leaving the defined slice must remain unconstrained.
(assert (= (f 4 5 true 2) 99))
(assert (= (f 3 5 false 2) 88))
(check-sat)
(get-value ((f 3 5 true 2) (f 4 5 true 2) (f 3 5 false 2)))
(push 1)
(assert (not (= (f 3 5 true 2) 205)))
(check-sat)
(pop 1)
(check-sat)
