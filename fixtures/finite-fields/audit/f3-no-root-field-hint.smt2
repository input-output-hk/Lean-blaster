; SPDX-License-Identifier: Apache-2.0
; FFM-19 project-authored semantic input; not a recovered historical artifact.
(set-logic QF_FF)
(set-option :ff-solver gb)
(set-option :ff-field-polys false)
(declare-fun x () (_ FiniteField 3))
(assert (= (ff.add (ff.mul x x) #f1m3) #f0m3))
(assert (= (ff.mul x (ff.mul x x)) x))
(check-sat)
