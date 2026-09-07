import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Lemmas validating the normalization and simplifications rules on `Eq` -/

protected theorem Blaster.ite_equal_then_else_equal_cond {t : Type} [DecidableEq t] (c₁ c₂ : Prop) [Decidable c₁] [Decidable c₂] (t₁ e₁ t₂ e₂ : t) :
  t₁ = t₂ → e₁ = e₂ → t₁ ≠ e₁ →
    ((if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) ↔ c₁ = c₂) := by grind

end Blaster
