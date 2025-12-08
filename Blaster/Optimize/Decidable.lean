import Lean

namespace Blaster

protected noncomputable def decide' (c : Prop) : Bool :=
  match Classical.propDecidable c with
  | .isTrue _ => true
  | .isFalse _ => false

theorem decide'_true (c : Prop) : Blaster.decide' c ↔ c := by
  dsimp [Blaster.decide']
  cases Classical.propDecidable c <;> simp [*]

theorem decide'_false (c : Prop) : Blaster.decide' c = false ↔ ¬ c := by
  conv => enter [2, 1]; rw [← Blaster.decide'_true c]
  simp

/-- Similar to `ite` but ignores decidable instance. -/
protected noncomputable def ite' {α : Sort u} (p : Prop) (x y : α) :=
  match Blaster.decide' p with
  | true => x
  | false => y

/-- Similar to `dite` but ignores decidable instance. -/
protected noncomputable def dite' {α : Sort u} (p : Prop) (t : p → α) (e : ¬ p → α) : α :=
  match h : (Blaster.decide' p) with
  | true => t ((Blaster.decide'_true p).mp h)
  | false => e ((Blaster.decide'_false p).mp h)

theorem ite_equiv.{u} : @ite = fun (α : Sort u) p _ => @Blaster.ite' α p := by
  funext α p _ x y
  dsimp [Blaster.ite']; cases h0 : Blaster.decide' p
  case false => simp; intro h1; have h2 := (Blaster.decide'_false _).mp h0; contradiction
  case true => simp; intro h1; have h2 := (Blaster.decide'_true _).mp h0; contradiction

theorem dite_equiv.{u} : @dite = fun (α : Sort u) p _ => @Blaster.dite' α p := by
  funext α p _ x y
  dsimp [Blaster.dite'];
  split <;> rename_i h1 <;> split <;> rename_i h2 <;> try rfl
  . have h3 := (Blaster.decide'_false _).mp h2; contradiction
  . have h3 := (Blaster.decide'_true _).mp h2; contradiction

theorem ite_to_dite'_equiv.{u} : @ite = fun (α : Sort u) p _d x y => @Blaster.dite' α p (fun _ => x) (fun _ => y) := by
  funext α p _ x y
  dsimp [Blaster.dite']; cases h0 : Blaster.decide' p
  case false => simp; intro h1; have h2 := (Blaster.decide'_false _).mp h0; contradiction
  case true => simp; intro h1; have h2 := (Blaster.decide'_true _).mp h0; contradiction

theorem decide'_equiv : @decide = fun p _ => Blaster.decide' p := by
  funext p _
  cases h : Blaster.decide' p
  case false => simp; apply (Blaster.decide'_false _).mp h
  case true  => simp; apply (Blaster.decide'_true _).mp h

end Blaster
