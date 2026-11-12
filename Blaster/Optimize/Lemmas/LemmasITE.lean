import Blaster.Optimize.Decidable

namespace Blaster

/-! ## Lemmas validating the `Blaster.dite'` choice reductions on a constant condition.
    Stated on the partial application so that they also rewrite under binders the branches depend on.
-/

protected theorem dite'_true {α : Sort u} : @Blaster.dite' α True = fun t _ => t True.intro :=
  funext fun t => funext fun e =>
    (congrFun (congrFun (congrFun (congrFun (congrFun Blaster.dite_equiv.{u} α) True) instDecidableTrue) t) e).symm

protected theorem dite'_false {α : Sort u} : @Blaster.dite' α False = fun _ e => e not_false :=
  funext fun t => funext fun e =>
    (congrFun (congrFun (congrFun (congrFun (congrFun Blaster.dite_equiv.{u} α) False) instDecidableFalse) t) e).symm

end Blaster
