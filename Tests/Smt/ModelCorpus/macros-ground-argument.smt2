; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --finite-model-find --macros-quant --macros-quant-mode=all
; EXPECT: sat
; EXPECT: (((apply identity 17) 17) ((apply other 17) 99))
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-sort Function 0)
(declare-fun apply (Function Int) Int)
(declare-const identity Function)
(declare-const other Function)
(assert (distinct identity other))
(assert (forall ((x Int)) (= (apply identity x) x)))
(assert (= (apply other 17) 99))
(check-sat)
(get-value ((apply identity 17) (apply other 17)))
(push 1)
(assert (not (= (apply identity 17) 17)))
(check-sat)
(pop 1)
(check-sat)
