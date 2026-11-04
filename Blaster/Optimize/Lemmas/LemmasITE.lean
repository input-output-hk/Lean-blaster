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

/-- Validates moving a context `g` into the branches of a `Blaster.dite'`: a function applied to it,
    extra arguments applied to it, or a projection of it.
    The branches stay quantified, so the replay takes them from the goal. -/
protected theorem apply_dite' {α : Sort u} {β : Sort v} (g : α → β) (c : Prop) (t : c → α) (e : ¬ c → α) :
    g (Blaster.dite' c t e) = Blaster.dite' c (fun h => g (t h)) (fun h => g (e h)) :=
  (congrArg g (congrFun (congrFun (congrFun (congrFun (congrFun Blaster.dite_equiv.{u} α) c)
      (Classical.propDecidable c)) t) e).symm).trans
    ((@apply_dite α β g c (Classical.propDecidable c) t e).trans
      (congrFun (congrFun (congrFun (congrFun (congrFun Blaster.dite_equiv.{v} β) c)
        (Classical.propDecidable c)) _) _))

end Blaster
