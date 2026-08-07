import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Lemmas validating the normalization and simplifications rules on `Prop` -/

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

protected theorem Blaster.and_left {a b : Prop} (h : a ∧ b) : a := by apply (And.left h)
protected theorem Blaster.and_right {a b : Prop} (h : a ∧ b) : b := by apply (And.right h)

/-- Return `Blaster.and_implies_from_dite` const expression and cache result. -/
def mkBlasterAndImpliesOfDite : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.and_implies_from_dite)

/-- Return `Blaster.false_eq_imp_of_not_true_imp` const expression and cache result. -/
def mkBlasterFalseEqImpOfNotTrueImp : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.false_eq_imp_of_not_true_imp)

end Blaster
