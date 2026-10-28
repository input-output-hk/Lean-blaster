; SPDX-License-Identifier: Apache-2.0
; FFM-19 project-authored semantic input; not a recovered historical artifact.
(set-logic QF_FF)
(set-option :ff-solver gb)
(set-option :ff-field-polys false)
(declare-fun x () (_ FiniteField 7))
(declare-fun y () (_ FiniteField 7))
(declare-fun u () (_ FiniteField 7))
(assert (= (ff.mul x y) #f0m7))
(assert (= (ff.mul x u) #f1m7))
(assert (not (= y #f0m7)))
(check-sat)
