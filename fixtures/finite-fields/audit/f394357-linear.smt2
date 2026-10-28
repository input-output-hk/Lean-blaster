; SPDX-License-Identifier: Apache-2.0
; FFM-19 project-authored semantic input; not a recovered historical artifact.
(set-logic QF_FF)
(set-option :ff-solver gb)
(set-option :ff-field-polys false)
(declare-fun a () (_ FiniteField 394357))
(assert (= (ff.mul (ff.add #f1m394357 (ff.mul #f394356m394357 a)) #f2m394357) #f0m394357))
(assert (not (= a #f1m394357)))
(check-sat)
