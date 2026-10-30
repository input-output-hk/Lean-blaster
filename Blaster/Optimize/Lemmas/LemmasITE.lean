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

/-! ## Lemmas validating the `Blaster.dite'` reductions
  - `sif h : c then e1 else e2 ==> e1   (e1 =ₚₜᵣ e2)`
  - `(sif h : ¬ c then e1 else e2) x₁ … xₙ ==> (sif h : c then e2 else e1) x₁ … xₙ`
  - `(sif h : false = c then e1 else e2) x₁ … xₙ  ==> (sif h : true = c then e2 else e1) x₁ … xₙ`
  - `sif h : c then e1 else e2 ==> (h : c → e1) ∧ (h : ¬ c → e2)   (Type(e1) = Prop)`
-/
protected theorem dite'_abs {α : Sort u} {c : Prop} (a : α) :
  @Blaster.dite' α c (fun _ : c => a) (fun _ : ¬ c => a) = a := by
  unfold Blaster.dite'
  split <;> rfl

protected theorem dite'_prop_iff {c : Prop} (t : c → Prop) (e : ¬ c → Prop) :
    @Blaster.dite' Prop c t e ↔ ((∀ h : c, t h) ∧ (∀ h : ¬ c, e h)) := by
  unfold Blaster.dite'
  split <;> rename_i hdec
  · have hc : c := (Blaster.decide'_true c).mp hdec
    exact ⟨fun h => ⟨fun h' => Eq.mp (congrArg t (Subsingleton.elim hc h')) h,
                      fun h' => (h' hc).elim⟩,
           fun h => h.1 hc⟩
  · have hnc : ¬ c := (Blaster.decide'_false c).mp hdec
    exact ⟨fun h => ⟨fun h' => (hnc h').elim,
                      fun h' => Eq.mp (congrArg e (Subsingleton.elim hnc h')) h⟩,
           fun h => h.2 hnc⟩

protected theorem dite'_prop_eq {c : Prop} :
    @Blaster.dite' Prop c =
      (fun (t : c → Prop) (e : ¬ c → Prop) => (∀ h : c, t h) ∧ (∀ h : ¬ c, e h)) := by
  funext t e
  exact propext (Blaster.dite'_prop_iff t e)

protected theorem dite'_not_swap {α : Sort u} {c : Prop} :
    @Blaster.dite' α (¬ c) =
      (fun (t : ¬ c → α) (e : ¬ ¬ c → α) =>
        @Blaster.dite' α c (fun h : c => e (not_not_intro h)) t) := by
  funext t e
  unfold Blaster.dite'
  split <;> rename_i hL <;> split <;> rename_i hR
  · exact absurd ((Blaster.decide'_true c).mp hR) ((Blaster.decide'_true (¬ c)).mp hL)
  · congr 1
  · congr 1
  · exact absurd ((Blaster.decide'_false c).mp hR) ((Blaster.decide'_false (¬ c)).mp hL)

protected theorem not_false_eq_of_true_eq {c : Bool} (h : true = c) : ¬ (false = c) :=
  fun hf => Bool.false_ne_true (hf.trans h.symm)

protected theorem false_eq_of_not_true_eq {c : Bool} (h : ¬ (true = c)) : false = c :=
  (Bool.eq_false_iff.mpr (fun hc => h hc.symm)).symm

protected theorem dite'_bool_swap {α : Sort u} {c : Bool} :
    @Blaster.dite' α (false = c) =
      (fun (t : (false = c) → α) (e : ¬ (false = c) → α) =>
        @Blaster.dite' α (true = c)
          (fun h : true = c => e (Blaster.not_false_eq_of_true_eq h))
          (fun h : ¬ (true = c) => t (Blaster.false_eq_of_not_true_eq h))) := by
  funext t e
  unfold Blaster.dite'
  split <;> rename_i hL <;> split <;> rename_i hR
  · exact (Bool.false_ne_true (((Blaster.decide'_true (false = c)).mp hL).trans
      (((Blaster.decide'_true (true = c)).mp hR).symm))).elim
  · congr 1
  · congr 1
  · exfalso
    have hnf : ¬ (false = c) := (Blaster.decide'_false (false = c)).mp hL
    have hnt : ¬ (true = c) := (Blaster.decide'_false (true = c)).mp hR
    cases c
    · exact hnf rfl
    · exact hnt rfl

end Blaster
