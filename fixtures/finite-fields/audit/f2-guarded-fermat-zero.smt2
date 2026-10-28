; SPDX-License-Identifier: Apache-2.0
; FFM-19 project-authored semantic input; not a recovered historical artifact.
(set-logic QF_FF)
(set-option :ff-solver gb)
(set-option :ff-field-polys false)
(declare-fun x () (_ FiniteField 2))
(assert (= x #f0m2))
(assert (not (= (ite (= x #f0m2) #f0m2 #f1m2) #f0m2)))
(check-sat)
