import Lean

namespace Solver

protected noncomputable def decide' (c : Prop) : Bool :=
  match Classical.propDecidable c with
  | .isTrue _ => true
  | .isFalse _ => false

theorem decide'_true (c : Prop) : Solver.decide' c ↔ c := by
  dsimp [Solver.decide']
  cases Classical.propDecidable c <;> simp [*]

theorem decide'_false (c : Prop) : Solver.decide' c = false ↔ ¬ c := by
  conv => enter [2, 1]; rw [← Solver.decide'_true c]
  simp

/-- Similar to `ite` but ignores decidable instance. -/
protected noncomputable def ite' {α : Sort u} (p : Prop) (x y : α) :=
  match Solver.decide' p with
  | true => x
  | false => y

/-- Similar to `dite` but ignores decidable instance. -/
protected noncomputable def dite' {α : Sort u} (p : Prop) (t : p → α) (e : ¬ p → α) : α :=
  match h : (Solver.decide' p) with
  | true => t ((Solver.decide'_true p).mp h)
  | false => e ((Solver.decide'_false p).mp h)

theorem ite_equiv.{u} : @ite = fun (α : Sort u) p _ => @Solver.ite' α p := by
  funext α p _ x y
  dsimp [Solver.ite']; cases h0 : Solver.decide' p
  case false => simp; intro h1; have h2 := (Solver.decide'_false _).mp h0; contradiction
  case true => simp; intro h1; have h2 := (Solver.decide'_true _).mp h0; contradiction

theorem dite_equiv.{u} : @dite = fun (α : Sort u) p _ => @Solver.dite' α p := by
  funext α p _ x y
  dsimp [Solver.dite'];
  split <;> rename_i h1 <;> split <;> rename_i h2 <;> try rfl
  . have h3 := (Solver.decide'_false _).mp h2; contradiction
  . have h3 := (Solver.decide'_true _).mp h2; contradiction

theorem ite_to_dite'_equiv.{u} : @ite = fun (α : Sort u) p _d x y => @Solver.dite' α p (fun _ => x) (fun _ => y) := by
  funext α p _ x y
  dsimp [Solver.dite']; cases h0 : Solver.decide' p
  case false => simp; intro h1; have h2 := (Solver.decide'_false _).mp h0; contradiction
  case true => simp; intro h1; have h2 := (Solver.decide'_true _).mp h0; contradiction

theorem decide'_equiv : @decide = fun p _ => Solver.decide' p := by
  funext p _
  cases h : Solver.decide' p
  case false => simp; apply (Solver.decide'_false _).mp h
  case true  => simp; apply (Solver.decide'_true _).mp h

end Solver
