import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Const-expression accessors for the `Prop` simplification rules -/

protected theorem dite_from_then {a b c : Prop} (h1 : c) (h2 : a) : Blaster.dite' c (fun _ => a) (fun _ => b) := by
  dsimp [Blaster.dite']; cases h1 : Blaster.decide' c
  case true => simp; assumption
  case false => simp; have h2 := (Blaster.decide'_false _).mp h1; contradiction

protected theorem dite_from_else {a b c : Prop} (h1 : ¬ c) (h2 : b) : Blaster.dite' c (fun _ => a) (fun _ => b) := by
  dsimp [Blaster.dite']; cases h3 : Blaster.decide' c
  case true => simp; have h4 := (Blaster.decide'_true _).mp h3; contradiction
  case false => simp; assumption

protected theorem dite_from_else_eq_false {a b : Prop} {c : Bool} (h1 : false = c) (h2 : b) : Blaster.dite' c (fun _ => a) (fun _ => b) := by
  dsimp [Blaster.dite']; cases h3 : Blaster.decide' c
  case true => simp; have h4 := (Blaster.decide'_true _).mp h3; rw [h4] at h1; simp at h1
  case false => simp; assumption

protected theorem and_not_from_not_or {a b : Prop} (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b := by apply (not_or.1 h)

protected theorem false_eq_of_not_true_eq {c : Bool} (h : ¬ (true = c)) : false = c := by simp at h; rw [h]
protected theorem true_eq_of_not_false_eq {c : Bool} (h : ¬ (false = c)) : true = c := by simp at h; rw [h]

protected theorem not_true_eq_of_false_eq {c : Bool} (h : false = c) : ¬ (true = c) := by simp; rw [h]
protected theorem not_false_eq_of_true_eq {c : Bool} (h : true = c) : ¬ (false = c) := by simp; rw [h]

protected theorem and_implies_from_dite {c : Prop} {t : c → Prop} {e : ¬ c → Prop} (h : Blaster.dite' c t e) :
  (∀ (h : c), t h) ∧ (∀ (h : ¬ c), e h) := by
  revert h
  dsimp [Blaster.dite']; split <;> rename_i h2
  . have h3 := (Blaster.decide'_true c).1 h2; intro h4
    constructor
    . intro; assumption
    . intro; contradiction
  . have h3 := (Blaster.decide'_false c).1 h2; intro h4
    constructor
    . intro; contradiction
    . intro; assumption

protected theorem false_eq_imp_of_not_true_imp {c : Bool} {p : Prop} (h : ¬ (true = c) → p) : false = c → p := by
  simp at h; intro h2; rw [eq_comm] at h2; exact h h2


/-- Return `And.left` const expression and cache result. -/
def mkAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``And.left)

/-- Return `And.right` const expression and cache result. -/
def mkAndRight : TranslateEnvT Expr := mkExpr (mkConst ``And.right)

/-- Return `Blaster.dite_from_then` const expression and cache result. -/
def mkBlasterDiteFromThen : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.dite_from_then)

/-- Return `Blaster.dite_from_else` const expression and cache result. -/
def mkBlasterDiteFromElse : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.dite_from_else)

/-- Return `Blaster.dite_from_else_eq_false` const expression and cache result. -/
def mkBlasterDiteFromElseEqFalse : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.dite_from_else_eq_false)

/-- Return `And.intro` const expression and cache result. -/
def mkAndIntro : TranslateEnvT Expr := mkExpr (mkConst ``And.intro)

/-- Return `Or.inl` const expression and cache result. -/
def mkOrInl : TranslateEnvT Expr := mkExpr (mkConst ``Or.inl)

/-- Return `Or.inr` const expression and cache result. -/
def mkOrInr : TranslateEnvT Expr := mkExpr (mkConst ``Or.inr)

/-- Return `Blaster.and_not_from_not_or` const expression and cache result. -/
def mkBlasterAndNotFromNotOr : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.and_not_from_not_or)

/-- Return `Blaster.false_eq_of_not_true_eq` const expression and cache result. -/
def mkBlasterFalseEqNotTrueEq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.false_eq_of_not_true_eq)

/-- Return `Blaster.true_eq_of_not_false_eq` const expression and cache result. -/
def mkBlasterTrueEqNotFalseEq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.true_eq_of_not_false_eq)

/-- Return `Blaster.and_implies_from_dite` const expression and cache result. -/
def mkBlasterAndImpliesOfDite : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.and_implies_from_dite)

/-- Return `Blaster.false_eq_imp_of_not_true_imp` const expression and cache result. -/
def mkBlasterFalseEqImpOfNotTrueImp : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.false_eq_imp_of_not_true_imp)

/-! ## Lemmas validating the `And` simplification rules:
    - `a ∧ ¬ a ==> False`
    - `true = a ∧ false = a ==> False`
-/
protected theorem and_not_self_is_false (a : Prop) :
  (a ∧ ¬ a) = False := by
  simp only [and_not_self]

protected theorem true_and_false_is_false (a : Bool) :
  (true = a ∧ false = a) = False := by
  apply propext
  rw [Bool.true_eq, Bool.false_eq, Bool.eq_true_and_eq_false_self]

/-! ## Lemmas validating the `Or` simplification rules:
    - `a ∨ ¬ a ==> True`
    - `true = a ∨ false = a ==> True`
-/
protected theorem or_not_self_is_true (a : Prop) :
  (a ∨ ¬ a) = True := by
  simp only [Classical.em]

protected theorem true_or_false_is_true (a : Bool) :
  (true = a ∨ false = a) = True := by
  apply propext;
  rw [Bool.true_eq, Bool.false_eq, Bool.eq_true_or_eq_false_self]

/-! ## Lemmas validating the `Not` simplification rules:
  - `¬ (¬ e) ==> e`
  - `¬ (false = e) ==> true = e`
  - `¬ (true = e) ==> false = e`
  - `¬ (¬ a ∧ ¬ b) ==> a ∨ b`
  - `¬ (¬ a ∨ ¬ b) ==> a ∧ b`
-/
protected theorem double_not_classical (p : Prop) : (¬ (¬ p)) = p := by
  apply propext;
  exact Classical.not_not


protected theorem not_false_is_true (e : Bool) :
  (¬ (false = e)) = (true = e) := by
  apply propext;
  rw [Bool.false_eq, Bool.not_eq_false, Bool.true_eq]

protected theorem not_true_is_false (e : Bool):
  (¬ (true = e)) = (false = e) := by
  apply propext;
  rw [Bool.true_eq, Bool.not_eq_true, Bool.false_eq]

protected theorem not_and_not_eq_or (a b : Prop) :
  (¬ (¬ a ∧ ¬ b)) = (a ∨ b) :=
  propext ⟨fun h => Classical.byContradiction fun hn =>
             h ⟨fun ha => hn (Or.inl ha), fun hb => hn (Or.inr hb)⟩,
           fun h hn => h.elim hn.1 hn.2⟩

protected theorem not_or_not_eq_and (a b : Prop) :
  (¬ (¬ a ∨ ¬ b)) = (a ∧ b) :=
  propext ⟨fun h => ⟨Classical.byContradiction fun ha => h (Or.inl ha),
                     Classical.byContradiction fun hb => h (Or.inr hb)⟩,
           fun h hn => hn.elim (fun ha => ha h.1) (fun hb => hb h.2)⟩

/-! ## Lemmas validating the `Iff` expansion and the And/Or implicative reductions:
    - `p ↔ q ==> (p → q) ∧ (q → p)`
    - `e1 ∧ (e1 → e2) ==> e1 ∧ e2`
    - `e1 ∧ (e2 → e1) ==> e1`
    - `(e1 → e2) ∧ (¬ e1 → e2) ==> e2`, also with `¬ e1` in normal form
    - `e1 ∨ (e1 → e2) ==> True`
    - `e1 ∨ (e2 → e1) ==> (e2 → e1)`
-/
protected theorem iff_eq_implies_and_implies (p q : Prop) :
  (p ↔ q) = ((p → q) ∧ (q → p)) :=
  propext iff_iff_implies_and_implies

protected theorem and_imp_self_eq_and (p q : Prop) :
  (p ∧ (p → q)) = (p ∧ q) :=
  propext ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

protected theorem and_imp_right_eq_left (p q : Prop) :
  (p ∧ (q → p)) = p :=
  propext ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

protected theorem and_imp_not_imp_eq (p q : Prop) :
  ((p → q) ∧ (¬ p → q)) = q :=
  propext (imp_and_neg_imp_iff p)

protected theorem and_imp_not_norm_imp_eq (p np : Prop) (h : (¬ p) = np) (q : Prop) :
  ((p → q) ∧ (np → q)) = q :=
  h ▸ Blaster.and_imp_not_imp_eq p q

protected theorem or_imp_self_eq_true (p q : Prop) :
  (p ∨ (p → q)) = True :=
  propext ⟨fun _ => trivial,
           fun _ => (Classical.em p).elim Or.inl (fun hnp => Or.inr (fun hp => absurd hp hnp))⟩

protected theorem or_imp_right_eq_imp (p q : Prop) :
  (p ∨ (q → p)) = (q → p) :=
  propext ⟨fun h => h.elim (fun hp _ => hp) id, fun h => Or.inr h⟩


/-! ## Lemmas validating the `Eq` simplifications over Prop:
    - `False = e ==> ¬ e`
    - `True = e ==> e`
    - `e = ¬ e ==> False`
    - `¬ e1 = ¬ e2 ==> e1 = e2 (Classical)`
-/

protected theorem false_prop_is_neg (e : Prop) : (False = e) = ¬ e := by
  apply propext
  rw [eq_iff_iff]
  exact iff_false_left fun a => a

protected theorem true_prop_is_idem (e : Prop) : (True = e) = e := by
  apply propext
  rw [eq_iff_iff]
  exact iff_true_left trivial

protected theorem eq_neg_is_false (e : Prop) : (e = ¬ e) = False := by
  simp only [eq_iff_iff, iff_not_self]

protected theorem neg_eq_neg_is_eq (a b : Prop) :
  ((¬ a) = ¬ b) = (a = b) := by
  classical
  apply propext
  rw [eq_iff_iff, eq_iff_iff]
  exact Decidable.not_iff_not

/-! ## Lemmas validating the hypothesis-context `And` reductions:
    - `a ∧ b ==> b (if a holds in the hypothesis context)`
    - `a ∧ b ==> a (if b holds in the hypothesis context)`
    - `a ∧ b ==> False (if ¬ a holds in the hypothesis context)`
    - `a ∧ b ==> False (if ¬ b holds in the hypothesis context)`
-/
protected theorem and_left_hyp_eq_right (a b : Prop) (h : a) :
  (a ∧ b) = b :=
  propext ⟨And.right, fun hb => ⟨h, hb⟩⟩

protected theorem and_right_hyp_eq_left (a b : Prop) (h : b) :
  (a ∧ b) = a :=
  propext ⟨And.left, fun ha => ⟨ha, h⟩⟩

protected theorem and_left_neg_hyp_eq_false (a b : Prop) (h : ¬ a) :
  (a ∧ b) = False :=
  propext ⟨fun hab => h hab.1, False.elim⟩

protected theorem and_right_neg_hyp_eq_false (a b : Prop) (h : ¬ b) :
  (a ∧ b) = False :=
  propext ⟨fun hab => h hab.2, False.elim⟩

/-! ## Lemmas validating the hypothesis-context `Or` reductions:
    - `a ∨ b ==> True (if a holds in the hypothesis context)`
    - `a ∨ b ==> True (if b holds in the hypothesis context)`
    - `a ∨ b ==> b (if ¬ a holds in the hypothesis context)`
    - `a ∨ b ==> a (if ¬ b holds in the hypothesis context)`
-/
protected theorem or_left_hyp_eq_true (a b : Prop) (h : a) :
  (a ∨ b) = True :=
  propext ⟨fun _ => trivial, fun _ => Or.inl h⟩

protected theorem or_right_hyp_eq_true (a b : Prop) (h : b) :
  (a ∨ b) = True :=
  propext ⟨fun _ => trivial, fun _ => Or.inr h⟩

protected theorem or_left_neg_hyp_eq_right (a b : Prop) (h : ¬ a) :
  (a ∨ b) = b :=
  propext ⟨fun hab => hab.elim (fun ha => absurd ha h) id, Or.inr⟩

protected theorem or_right_neg_hyp_eq_left (a b : Prop) (h : ¬ b) :
  (a ∨ b) = a :=
  propext ⟨fun hab => hab.elim id (fun hb => absurd hb h), Or.inl⟩

/-! ## Lemma validating the hypothesis-free `ForallE` reductions:
  - `e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)`
-/
protected theorem implies_self_eq_true (a : Prop) : (a → a) = True := by
  apply propext
  exact imp_self

/-! ## Lemmas validating the COI reductions on quantifiers:
  - `∀ (n : t), e ==> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)`
  - `∃ (n : t), e ==> e (if isSortOrInhabited t ∧ ¬ e.hasLooseBVar 0)`
-/
protected theorem forall_coi.{u} (α : Sort u) (b : Prop) [Nonempty α] : (α → b) = b :=
  propext (forall_const α)

protected theorem exists_coi.{u} (α : Sort u) (b : Prop) [Nonempty α] : (∃ _ : α, b) = b :=
  propext (exists_const α)

/-! ## Lemmas validating the hypothesis-driven implication rules
  - `h: True → e ==> e [h/True.intro] (if Type(e) = Prop ∧ fVarInExpr h.fvarId! e ∧ the input type of h is True)`
  - `e → False ==> ¬ e`
  - `e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)`
  - `e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)`
  - `h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)`
  - `h : e1 → e2 ==> e2[h/h'] (if e1 := h' ∈ hypothesisContext.hypothesisMap ∧ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)`
-/
protected theorem implies_eq_right_of_hyp_dep (a : Prop) (b : a → Prop) (p : a) :
    (∀ h : a, b h) = b p := by
  apply propext
  constructor
  · intro hab; exact hab p
  · intro hp h
    exact cast (congrArg b (Subsingleton.elim h p).symm) hp


protected theorem implies_eq_neg_of_imp_not (a b : Prop) (h : a → ¬ b) : (a → b) = ¬ a := by
  apply propext
  constructor
  · intro hab ha; exact h ha (hab ha)
  · intro hna ha; exact absurd ha hna

protected theorem implies_eq_right_of_hyp (a b : Prop) (h : a) : (a → b) = b := by
  apply propext
  constructor
  · intro hab; exact hab h
  · intro hb _; exact hb

end Blaster
