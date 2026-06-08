import Lean
import Blaster
import Stablecoin.Base

namespace Stablecoin

/-- Abstract stablecoin parameters: an uninterpreted constant (proven for all valid
    parameter values). "Params unchanged over time" is automatic — it is a constant.
    NOTE: opaque-vs-axiom translation through Blaster is resolved empirically in the
    Theorem 3 gate task; leave as `opaque` for now. -/
opaque params : Parameters

/-- `ParameterConstraints` (Constraints.lus) magnitude bounds. -/
def paramConstraints : Prop :=
  params.r_max ≥ params.r_min ∧
  params.fees.fee_b_sc > PER ∧ params.fees.fee_b_sc ≤ TWOPER ∧
  params.fees.fee_s_sc ≥ ZERO ∧ params.fees.fee_s_sc < PER ∧
  params.fees.fee_b_rc > PER ∧ params.fees.fee_b_rc ≤ TWOPER ∧
  params.fees.fee_s_rc ≥ ZERO ∧ params.fees.fee_s_rc < PER ∧
  params.n_sc_s > ZERO ∧ params.p_min > ZERO ∧
  params.r_min > Int.ediv (params.fees.fee_b_sc + 99) PER

end Stablecoin
