; SPDX-License-Identifier: Apache-2.0
; FFM-19 project-authored semantic input; not a recovered historical artifact.
(set-logic QF_FF)
(set-option :ff-solver gb)
(set-option :ff-field-polys false)
(declare-fun x () (_ FiniteField 3))
(assert (not (= x #f0m3)))
(assert (not (= x #f1m3)))
(assert (not (= x #f2m3)))
(check-sat)
