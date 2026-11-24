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

/-! ## Lemmas validating the `Prop` simplification rules of `iteSimp?`, all derived from `dite'_prop_iff`:
  - `sif h : c then True else False ===> c`
  - `sif h : c then False else True ===> ¬ c`
  - `sif h : c then q else p ===> h : ¬ c → p` (when `c → q`)
  - `sif h : c then q else p ===> ¬ c ∧ (h : ¬ c → p)`, or `¬ c ∧ p` when `p` does not use `h` (when `c → ¬ q`)
  - `sif h : c then p else q ===> h : c → p` (when `¬ c → q`)
  - `sif h : c then p else q ===> c ∧ (h : c → p)`, or `c ∧ p` when `p` does not use `h` (when `¬ c → ¬ q`)
  The absorbed branch `q` does not use `h`; the hypothesis on it is the case of the rule: `True`
  (resp. `False`), a hypothesis, `c` or `¬ c` itself, or the negated `Bool` equation of `c`.
  The other branch is implicit, so that the replay takes it from the goal.
-/
protected theorem dite'_true_false (c : Prop) :
    @Blaster.dite' Prop c (fun _ => True) (fun _ => False) = c :=
  propext ⟨fun d => Classical.byContradiction fun nc => ((Blaster.dite'_prop_iff _ _).mp d).2 nc,
           fun hc => (Blaster.dite'_prop_iff _ _).mpr ⟨fun _ => trivial, fun nc => absurd hc nc⟩⟩

protected theorem dite'_false_true (c : Prop) :
    @Blaster.dite' Prop c (fun _ => False) (fun _ => True) = ¬ c :=
  propext ⟨fun d hc => ((Blaster.dite'_prop_iff _ _).mp d).1 hc,
           fun nc => (Blaster.dite'_prop_iff _ _).mpr ⟨fun hc => absurd hc nc, fun _ => trivial⟩⟩

protected theorem dite'_then_true (c q : Prop) (hq : c → q) {e : ¬ c → Prop} :
    @Blaster.dite' Prop c (fun _ => q) e = ∀ h : ¬ c, e h :=
  propext ⟨fun d => ((Blaster.dite'_prop_iff _ e).mp d).2,
           fun he => (Blaster.dite'_prop_iff _ e).mpr ⟨hq, he⟩⟩

protected theorem dite'_then_false (c q : Prop) (hq : c → ¬ q) {e : ¬ c → Prop} :
    @Blaster.dite' Prop c (fun _ => q) e = (¬ c ∧ ∀ h : ¬ c, e h) :=
  propext ⟨fun d => ⟨fun hc => hq hc (((Blaster.dite'_prop_iff _ e).mp d).1 hc),
                     ((Blaster.dite'_prop_iff _ e).mp d).2⟩,
           fun ⟨nc, he⟩ => (Blaster.dite'_prop_iff _ e).mpr ⟨fun hc => absurd hc nc, he⟩⟩

protected theorem dite'_then_false_const (c q : Prop) (hq : c → ¬ q) {p : Prop} :
    @Blaster.dite' Prop c (fun _ => q) (fun _ => p) = (¬ c ∧ p) :=
  (Blaster.dite'_then_false c q hq).trans
    (propext ⟨fun ⟨nc, hp⟩ => ⟨nc, hp nc⟩, fun ⟨nc, hp⟩ => ⟨nc, fun _ => hp⟩⟩)

protected theorem dite'_else_true (c q : Prop) (hq : ¬ c → q) {t : c → Prop} :
    @Blaster.dite' Prop c t (fun _ => q) = ∀ h : c, t h :=
  propext ⟨fun d => ((Blaster.dite'_prop_iff t _).mp d).1,
           fun ht => (Blaster.dite'_prop_iff t _).mpr ⟨ht, hq⟩⟩

protected theorem dite'_else_false (c q : Prop) (hq : ¬ c → ¬ q) {t : c → Prop} :
    @Blaster.dite' Prop c t (fun _ => q) = (c ∧ ∀ h : c, t h) :=
  propext ⟨fun d => ⟨Classical.byContradiction fun nc => hq nc (((Blaster.dite'_prop_iff t _).mp d).2 nc),
                     ((Blaster.dite'_prop_iff t _).mp d).1⟩,
           fun ⟨hc, ht⟩ => (Blaster.dite'_prop_iff t _).mpr ⟨ht, fun nc => absurd hc nc⟩⟩

protected theorem dite'_else_false_const (c q : Prop) (hq : ¬ c → ¬ q) {p : Prop} :
    @Blaster.dite' Prop c (fun _ => p) (fun _ => q) = (c ∧ p) :=
  (Blaster.dite'_else_false c q hq).trans
    (propext ⟨fun ⟨hc, hp⟩ => ⟨hc, hp hc⟩, fun ⟨hc, hp⟩ => ⟨hc, fun _ => hp⟩⟩)

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

/-- Validates rewriting the condition of a `Blaster.dite'`, as core `forall_prop_congr_dom` for the
    domain of a `∀`: each branch gets its hypothesis cast back to the old condition. -/
protected theorem dite'_congr_cond {α : Sort u} {b c : Prop} (h : b = c) (x : b → α) (y : ¬ b → α) :
    Blaster.dite' b x y =
      Blaster.dite' c (fun h' => x (h.mpr_prop h')) (fun h' => y (h.mpr_not h')) := by
  subst h
  rfl

/-- ## Lemmas validating the `Blaster.dite'` factorization reduction rules:
  - `sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e1 else e3) ==> sif h2 : c then e1 else (sif h1 : a then e2 else e3)`
  - `sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e3 else e2) ==> sif h2 : c then (sif h1 : a then e1 else e3) else e2`
-/

protected theorem dite'_eq_dite {α : Sort u} (p : Prop) (t : p → α) (e : ¬ p → α) :
    Blaster.dite' p t e = @dite α p (Classical.propDecidable p) t e :=
  (congrFun (congrFun (congrFun (congrFun (congrFun Blaster.dite_equiv α) p)
    (Classical.propDecidable p)) t) e).symm

protected theorem dite'_factorize_thn {α : Sort u} {a c : Prop}
    (t : c → α) (f : a → ¬ c → α) (g : ¬ a → ¬ c → α) :
    @Blaster.dite' α a
        (fun h1 : a  => @Blaster.dite' α c t (fun h2 : ¬ c => f h1 h2))
        (fun h1 : ¬ a => @Blaster.dite' α c t (fun h2 : ¬ c => g h1 h2))
      =
    @Blaster.dite' α c t
        (fun h2 : ¬ c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬ a => g h1 h2)) := by
  cases h : Blaster.decide' a
  · have hlam : (fun h2 : ¬c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬a => g h1 h2))
              = (fun h2 : ¬c => g ((Blaster.decide'_false a).mp h) h2) := by
      funext h2
      rw [Blaster.dite'_eq_dite, dif_neg ((Blaster.decide'_false a).mp h)]
    rw [hlam, Blaster.dite'_eq_dite, dif_neg ((Blaster.decide'_false a).mp h)]
  · have hlam : (fun h2 : ¬c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬a => g h1 h2))
              = (fun h2 : ¬c => f ((Blaster.decide'_true a).mp h) h2) := by
      funext h2
      rw [Blaster.dite'_eq_dite, dif_pos ((Blaster.decide'_true a).mp h)]
    rw [hlam, Blaster.dite'_eq_dite, dif_pos ((Blaster.decide'_true a).mp h)]

protected theorem dite'_factorize_els {α : Sort u} {a c : Prop}
    (e : ¬ c → α) (f : a → c → α) (g : ¬ a → c → α) :
    @Blaster.dite' α a
        (fun h1 : a  => @Blaster.dite' α c (fun h2 : c => f h1 h2) e)
        (fun h1 : ¬ a => @Blaster.dite' α c (fun h2 : c => g h1 h2) e)
  = @Blaster.dite' α c
        (fun h2 : c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬ a => g h1 h2)) e := by
  cases h : Blaster.decide' a
  · have hlam : (fun h2 : c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬a => g h1 h2))
              = (fun h2 : c => g ((Blaster.decide'_false a).mp h) h2) := by
      funext h2
      rw [Blaster.dite'_eq_dite, dif_neg ((Blaster.decide'_false a).mp h)]
    rw [hlam, Blaster.dite'_eq_dite, dif_neg ((Blaster.decide'_false a).mp h)]
  · have hlam : (fun h2 : c => @Blaster.dite' α a (fun h1 : a => f h1 h2) (fun h1 : ¬a => g h1 h2))
              = (fun h2 : c => f ((Blaster.decide'_true a).mp h) h2) := by
      funext h2
      rw [Blaster.dite'_eq_dite, dif_pos ((Blaster.decide'_true a).mp h)]
    rw [hlam, Blaster.dite'_eq_dite, dif_pos ((Blaster.decide'_true a).mp h)]

/-! # Lemmas validating the dite reduce simplification rules:
  - `(sif h : c then e1 else e2) x₁ … xₙ ==> e1 x₁ … xₙ (if c := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e1.hasLooseBVars)`
  - `(sif h : c then e1 else e2) x₁ … xₙ ==> e2 x₁ … xₙ (if ∃ e := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e2.hasLooseBVars ∧ e = ¬ c)`
  - `(sif h : c then e1 else e2) x₁ … xₙ ==> e1[h/h'] x₁ … xₙ (if c := h' ∈ hypothesisContext.hypothesisMap ∧ e1.hasLooseBVars)`
  - `(sif h : c then e1 else e2) x₁ … xₙ ==> e2[h/h'] x₁ … xₙ (if ∃ e := h' ∈ hypothesisContext.hypothesisMap ∧ e2.hasLooseBVars ∧ e = ¬ c)`
-/
protected theorem dite'_reduce_pos {α : Sort u} {c : Prop} (p : c) :
    @Blaster.dite' α c = (fun (t : c → α) (_ : ¬ c → α) => t p) := by
  funext t e
  have h : Blaster.decide' c = true := (Blaster.decide'_true c).mpr p
  unfold Blaster.dite'
  split <;> rename_i h'
  · congr 1
  · rw [h] at h'; exact (Bool.false_ne_true h'.symm).elim

protected theorem dite'_reduce_neg {α : Sort u} {c : Prop} (p : ¬ c) :
    @Blaster.dite' α c = (fun (_ : c → α) (e : ¬ c → α) => e p) := by
  funext t e
  have h : Blaster.decide' c = false := (Blaster.decide'_false c).mpr p
  unfold Blaster.dite'
  split <;> rename_i h'
  · rw [h] at h'; exact (Bool.false_ne_true h').elim
  · congr 1


end Blaster
