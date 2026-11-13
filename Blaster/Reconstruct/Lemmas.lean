import Lean
import Blaster.Optimize.Decidable

/-! # Lemmas used to justify the rewriting rules applied by the optimizer

Each lemma is stated as an equality whose lhs/rhs match (up to definitional equality)
the expressions produced by the corresponding rewriting rule.
-/

namespace Blaster.Reconstruct

/-! ## Normalization of opaque constants (see `normConst`) -/

theorem nat_pred_eq : Nat.pred = fun n => Nat.sub n 1 := by
  funext n; cases n <;> rfl

theorem nat_succ_eq : Nat.succ = fun n => Nat.add 1 n := by
  funext n; exact (Nat.one_add n).symm

theorem nat_ble_eq : Nat.ble = fun x y => Blaster.decide' (x ≤ y) := by
  funext x y
  cases h : Nat.ble x y
  . have h1 : ¬ (x ≤ y) := fun h2 => by
      have := Nat.ble_eq_true_of_le h2
      rw [h] at this; contradiction
    exact ((Blaster.decide'_false _).mpr h1).symm
  . exact ((Blaster.decide'_true _).mpr (Nat.le_of_ble_eq_true h)).symm

theorem nat_le_fun_eq_not_lt : Nat.le = fun x y => ¬ (y < x) := by
  funext x y; exact propext ⟨fun h => Nat.not_lt.mpr h, fun h => Nat.not_lt.mp h⟩

theorem int_le_fun_eq_not_lt : Int.le = fun x y => ¬ (y < x) := by
  funext x y; exact propext ⟨fun h => Int.not_lt.mpr h, fun h => Int.not_lt.mp h⟩

theorem nat_ble_fun_eq_not_lt : Nat.ble = fun x y => Blaster.decide' (¬ (y < x)) := by
  rw [nat_ble_eq]; funext x y
  exact congrArg Blaster.decide' (propext ⟨fun h => Nat.not_lt.mpr h, fun h => Nat.not_lt.mp h⟩)

theorem nat_beq_eq : Nat.beq = fun x y => x == y := by
  funext x y
  cases h : Nat.beq x y
  . have h1 := Nat.ne_of_beq_eq_false h
    simp [h1]
  . have h1 := Nat.eq_of_beq_eq_true h
    simp [h1]

theorem nat_beq_denorm (x y : Nat) : Nat.beq x y = decide (x = y) := by
  cases h : Nat.beq x y
  . exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  . exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem nat_ble_denorm (x y : Nat) : Nat.ble x y = decide (x ≤ y) := by
  cases h : Nat.ble x y
  . exact (decide_eq_false (fun h2 => by have := Nat.ble_eq_true_of_le h2; rw [h] at this; contradiction)).symm
  . exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem int_negSucc_eq : Int.negSucc = fun n => Int.neg (Int.ofNat (Nat.add 1 n)) := by
  funext n
  show Int.negSucc n = Int.neg (Int.ofNat (1 + n))
  rw [Nat.add_comm]; rfl

/-- Denormalization of `Int.negSucc` (see `int_negSucc_eq`), e.g., to reduce `match` expressions. -/
theorem neg_natCast_add_eq_negSucc (k m : Nat) (h : 0 < k) : -((k + m : Nat) : Int) = Int.negSucc (m + (k - 1)) := by
  cases k with
  | zero => contradiction
  | succ k => simp only [Nat.add_sub_cancel]; rw [Nat.add_comm]; rfl

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Denormalization lemmas

The optimizer replaces `ite`, `dite` and `decide` with `Blaster.dite'` and `Blaster.decide'`, which
ignore decidable instances. The following lemmas rewrite them back to their standard counterparts
(with classical decidable instances) such that Lean decision procedures can reason about them.
-/

theorem dite'_eq_dite {α : Sort u} (c : Prop) (t : c → α) (e : ¬ c → α) :
    Blaster.dite' c t e = @dite α c (Classical.propDecidable c) t e := by
  simp only [Blaster.dite_equiv]

theorem decide'_eq_decide (c : Prop) :
    Blaster.decide' c = @decide c (Classical.propDecidable c) := by
  simp only [Blaster.decide'_equiv]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Primitive operators

The optimizer keeps primitive operators (e.g., `Nat.add`) instead of their notation counterparts
(e.g., `HAdd.hAdd`). The following lemmas rewrite them back to notation such that Lean
decision procedures (e.g., `simp`, `omega`) can reason about them.
-/

theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_pow_eq (a b : Nat) : Nat.pow a b = a ^ b := rfl
theorem string_append_eq (a b : String) : String.append a b = a ++ b := rfl
theorem except_throw_eq {ε : Type u} {α : Type v} (e : ε) : (throw e : Except ε α) = Except.error e := rfl
theorem except_pure_eq {ε : Type u} {α : Type v} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
theorem list_append_eq {α : Type u} (a b : List α) : List.append a b = a ++ b := rfl
/-- Move numerals to the right of additions, i.e., the form expected by equation lemmas (`n + 1`). -/
theorem nat_lit_add_comm (k : Nat) (n : Nat) :
    @OfNat.ofNat Nat k (instOfNatNat k) + n = n + @OfNat.ofNat Nat k (instOfNatNat k) :=
  Nat.add_comm _ _
theorem int_add_eq (a b : Int) : Int.add a b = a + b := rfl
theorem int_mul_eq (a b : Int) : Int.mul a b = a * b := rfl
theorem int_neg_eq (a : Int) : Int.neg a = -a := rfl
theorem int_ediv_eq (a b : Int) : Int.ediv a b = a / b := rfl
theorem int_emod_eq (a b : Int) : Int.emod a b = a % b := rfl
theorem int_pow_eq (a : Int) (b : Nat) : Int.pow a b = a ^ b := rfl

end Blaster.Reconstruct

/-- Rewrite Blaster's internal representation back to standard Lean notation in all hypotheses and the goal. -/
macro "blaster_denorm" : tactic =>
  `(tactic| (try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide,
              Blaster.Reconstruct.nat_add_eq, Blaster.Reconstruct.nat_sub_eq, Blaster.Reconstruct.nat_mul_eq,
              Blaster.Reconstruct.nat_div_eq, Blaster.Reconstruct.nat_mod_eq, Blaster.Reconstruct.nat_pow_eq,
              Blaster.Reconstruct.int_add_eq, Blaster.Reconstruct.int_mul_eq, Blaster.Reconstruct.int_neg_eq,
              Blaster.Reconstruct.int_ediv_eq, Blaster.Reconstruct.int_emod_eq, Blaster.Reconstruct.int_pow_eq,
              Blaster.Reconstruct.nat_beq_denorm, Blaster.Reconstruct.nat_ble_denorm,
              Blaster.Reconstruct.string_append_eq, Blaster.Reconstruct.list_append_eq,
              Blaster.Reconstruct.except_throw_eq, Blaster.Reconstruct.except_pure_eq,
              Int.ofNat_eq_coe] at *))

namespace Blaster.Reconstruct

/-! ## Congruence lemmas -/

/-- Congruence for `Blaster.dite'` when the condition is rewritten. -/
theorem dite'_congr {α : Sort u} {c c' : Prop} {t : c → α} {e : ¬ c → α} {t' : c' → α} {e' : ¬ c' → α}
    (hc : c = c') (ht : ∀ h : c', t (hc.mpr h) = t' h) (he : ∀ h : ¬ c', e (fun h0 => h (hc.mp h0)) = e' h) :
    Blaster.dite' c t e = Blaster.dite' c' t' e' := by
  subst hc
  have h1 : t = t' := funext ht
  have h2 : e = e' := funext he
  rw [h1, h2]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Commutativity (see `reorderOperands`) -/

theorem nat_add_comm' (a b : Nat) : Nat.add a b = Nat.add b a := Nat.add_comm a b
theorem nat_mul_comm' (a b : Nat) : Nat.mul a b = Nat.mul b a := Nat.mul_comm a b
theorem nat_bitwise_or_comm' (a b : Nat) : Nat.bitwise or a b = Nat.bitwise or b a := Nat.or_comm a b
theorem nat_bitwise_and_comm' (a b : Nat) : Nat.bitwise and a b = Nat.bitwise and b a := Nat.and_comm a b
theorem nat_or_eq_bitwise' (a b : Nat) : a ||| b = Nat.bitwise or a b := rfl
theorem nat_and_eq_bitwise' (a b : Nat) : a &&& b = Nat.bitwise and a b := rfl
theorem int_add_comm' (a b : Int) : Int.add a b = Int.add b a := Int.add_comm a b
theorem int_mul_comm' (a b : Int) : Int.mul a b = Int.mul b a := Int.mul_comm a b
theorem eq_comm' {α : Sort u} (a b : α) : (a = b) = (b = a) := propext eq_comm
theorem and_comm' (a b : Prop) : (a ∧ b) = (b ∧ a) := propext And.comm
theorem or_comm' (a b : Prop) : (a ∨ b) = (b ∨ a) := propext Or.comm
theorem bool_and_comm' (a b : Bool) : (a && b) = (b && a) := Bool.and_comm a b
theorem bool_or_comm' (a b : Bool) : (a || b) = (b || a) := Bool.or_comm a b
theorem beq_comm' {α : Type u} [inst : BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Propositional connectives (see `optimizeNot`, `optimizeAnd`, `optimizeOr`, `optimizeIff`) -/

theorem not_false_eq' : (¬ False) = True := propext ⟨fun _ => trivial, fun _ h => h⟩
theorem not_true_eq' : (¬ True) = False := propext ⟨fun h => h trivial, fun h => h.elim⟩
theorem not_not_eq' (p : Prop) : (¬ ¬ p) = p := propext Classical.not_not
theorem not_true_eq_bool (e : Bool) : (¬ (true = e)) = (false = e) := by cases e <;> simp
theorem not_false_eq_bool (e : Bool) : (¬ (false = e)) = (true = e) := by cases e <;> simp
theorem nat_not_zero_lt (e : Nat) : (¬ (0 < e)) = (0 = e) := by
  apply propext; constructor <;> intro h <;> omega
theorem not_and_not_eq (a b : Prop) : (¬ (¬ a ∧ ¬ b)) = (a ∨ b) := by
  apply propext; constructor
  . intro h; by_cases ha : a
    . exact Or.inl ha
    . by_cases hb : b
      . exact Or.inr hb
      . exact (h ⟨ha, hb⟩).elim
  . intro h ⟨ha, hb⟩; cases h <;> contradiction
theorem not_or_not_eq (a b : Prop) : (¬ (¬ a ∨ ¬ b)) = (a ∧ b) := by
  apply propext; constructor
  . intro h; exact ⟨Classical.byContradiction (fun ha => h (Or.inl ha)),
                    Classical.byContradiction (fun hb => h (Or.inr hb))⟩
  . intro ⟨ha, hb⟩ h; cases h <;> contradiction

theorem false_and' (p : Prop) : (False ∧ p) = False := false_and p
theorem true_and' (p : Prop) : (True ∧ p) = p := true_and p
theorem and_self' (p : Prop) : (p ∧ p) = p := and_self p
theorem and_not_self' (p : Prop) : (p ∧ ¬ p) = False := propext ⟨fun ⟨h1, h2⟩ => h2 h1, False.elim⟩
theorem and_bool_neg (e : Bool) : ((true = e) ∧ (false = e)) = False := by cases e <;> simp
theorem and_imp_self (a c : Prop) : (a ∧ (a → c)) = (a ∧ c) :=
  propext ⟨fun ⟨h1, h2⟩ => ⟨h1, h2 h1⟩, fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩⟩
theorem and_imp_left (a c : Prop) : (a ∧ (c → a)) = a := propext ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩
theorem imp_and_not_imp (c d : Prop) : ((c → d) ∧ (¬ c → d)) = d := by
  apply propext; constructor
  . intro ⟨h1, h2⟩; by_cases h : c
    . exact h1 h
    . exact h2 h
  . intro h; exact ⟨fun _ => h, fun _ => h⟩
theorem and_eq_right_of {a : Prop} (b : Prop) (h : a) : (a ∧ b) = b := propext ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
theorem and_eq_left_of (a : Prop) {b : Prop} (h : b) : (a ∧ b) = a := propext ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩
theorem and_eq_false_of_not_left {a : Prop} (b : Prop) (h : ¬a) : (a ∧ b) = False :=
  propext ⟨fun h' => h h'.1, False.elim⟩
theorem and_eq_false_of_not_right (a : Prop) {b : Prop} (h : ¬b) : (a ∧ b) = False :=
  propext ⟨fun h' => h h'.2, False.elim⟩

theorem false_or' (p : Prop) : (False ∨ p) = p := false_or p
theorem true_or' (p : Prop) : (True ∨ p) = True := true_or p
theorem or_self' (p : Prop) : (p ∨ p) = p := or_self p
theorem or_not_self' (p : Prop) : (p ∨ ¬ p) = True := propext ⟨fun _ => trivial, fun _ => Classical.em p⟩
theorem or_bool_neg (e : Bool) : ((true = e) ∨ (false = e)) = True := by cases e <;> simp
theorem or_imp_self (a c : Prop) : (a ∨ (a → c)) = True := by
  apply propext; constructor
  . intro _; trivial
  . intro _; by_cases h : a
    . exact Or.inl h
    . exact Or.inr (fun h' => (h h').elim)
theorem or_imp_left (a c : Prop) : (a ∨ (c → a)) = (c → a) :=
  propext ⟨fun h => h.elim (fun h' _ => h') id, Or.inr⟩
theorem or_eq_true_of_left {a : Prop} (b : Prop) (h : a) : (a ∨ b) = True := propext ⟨fun _ => trivial, fun _ => Or.inl h⟩
theorem or_eq_true_of_right (a : Prop) {b : Prop} (h : b) : (a ∨ b) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h⟩
theorem or_eq_right_of_not {a : Prop} (b : Prop) (h : ¬a) : (a ∨ b) = b :=
  propext ⟨fun h' => h'.elim (fun ha => (h ha).elim) id, Or.inr⟩
theorem or_eq_left_of_not (a : Prop) {b : Prop} (h : ¬b) : (a ∨ b) = a :=
  propext ⟨fun h' => h'.elim id (fun hb => (h hb).elim), Or.inl⟩
theorem iff_eq_and_imp (a b : Prop) : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  propext ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Boolean operators (see `optimizeBoolAnd`, `optimizeBoolOr`, `optimizeBoolNot`) -/

theorem bool_false_and (b : Bool) : (false && b) = false := rfl
theorem bool_true_and (b : Bool) : (true && b) = b := rfl
theorem bool_and_self (b : Bool) : (b && b) = b := by cases b <;> rfl
theorem bool_and_not_self (b : Bool) : (b && !b) = false := by cases b <;> rfl
theorem bool_and_eq_right_of {a : Bool} (b : Bool) (h : true = a) : (a && b) = b := by subst h; rfl
theorem bool_and_eq_left_of (a : Bool) {b : Bool} (h : true = b) : (a && b) = a := by subst h; cases a <;> rfl
theorem bool_and_eq_false_of_left {a : Bool} (b : Bool) (h : false = a) : (a && b) = false := by subst h; rfl
theorem bool_and_eq_false_of_right (a : Bool) {b : Bool} (h : false = b) : (a && b) = false := by
  subst h; cases a <;> rfl
theorem bool_false_or (b : Bool) : (false || b) = b := rfl
theorem bool_true_or (b : Bool) : (true || b) = true := rfl
theorem bool_or_self (b : Bool) : (b || b) = b := by cases b <;> rfl
theorem bool_or_not_self (b : Bool) : (b || !b) = true := by cases b <;> rfl
theorem bool_or_eq_true_of_left {a : Bool} (b : Bool) (h : true = a) : (a || b) = true := by subst h; rfl
theorem bool_or_eq_true_of_right (a : Bool) {b : Bool} (h : true = b) : (a || b) = true := by
  subst h; cases a <;> rfl
theorem bool_or_eq_right_of {a : Bool} (b : Bool) (h : false = a) : (a || b) = b := by subst h; rfl
theorem bool_or_eq_left_of (a : Bool) {b : Bool} (h : false = b) : (a || b) = a := by subst h; cases a <;> rfl
theorem bool_not_true : (!true) = false := rfl
theorem bool_not_false : (!false) = true := rfl
theorem bool_not_not (b : Bool) : (!!b) = b := by cases b <;> rfl
theorem bool_not_decide' (p : Prop) : (!Blaster.decide' p) = Blaster.decide' (¬ p) := by
  cases h : Blaster.decide' p
  . have h1 := (Blaster.decide'_false p).mp h
    exact ((Blaster.decide'_true (¬ p)).mpr h1).symm
  . have h1 := (Blaster.decide'_true p).mp h
    exact ((Blaster.decide'_false (¬ p)).mpr (fun h2 => h2 h1)).symm

/-! ## `Blaster.decide'` (see `optimizeDecideCore`) -/

theorem decide'_False : Blaster.decide' False = false := (Blaster.decide'_false _).mpr id
theorem decide'_True : Blaster.decide' True = true := (Blaster.decide'_true _).mpr trivial
theorem decide'_true_eq (p : Bool) : Blaster.decide' (true = p) = p := by
  cases p
  . exact (Blaster.decide'_false _).mpr Bool.noConfusion
  . exact (Blaster.decide'_true _).mpr rfl
theorem decide'_false_eq (p : Bool) : Blaster.decide' (false = p) = !p := by
  cases p
  . exact (Blaster.decide'_true _).mpr rfl
  . exact (Blaster.decide'_false _).mpr Bool.noConfusion

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Quantifiers and implications (see `optimizeForall`) -/

theorem forall_true' (α : Sort u) : (α → True) = True := propext ⟨fun _ => trivial, fun _ _ => trivial⟩
theorem true_imp_eq (p : Prop) : (True → p) = p := propext ⟨fun h => h trivial, fun h _ => h⟩
theorem forall_true_dep (p : True → Prop) : (∀ h, p h) = p True.intro := propext ⟨fun h => h _, fun h _ => h⟩
theorem false_imp_eq (p : False → Prop) : (∀ h, p h) = True := propext ⟨fun _ => trivial, fun _ h => h.elim⟩
theorem imp_self_eq (p : Prop) : (p → p) = True := propext ⟨fun _ => trivial, fun _ h => h⟩
theorem imp_eq_not_of (a : Prop) {b : Prop} (h : ¬ b) : (a → b) = ¬ a := propext ⟨fun h1 h2 => h (h1 h2), fun h1 h2 => (h1 h2).elim⟩
theorem imp_eq_not_of_imp {a : Prop} (b : Prop) (h : a → ¬ b) : (a → b) = ¬ a :=
  propext ⟨fun h1 h2 => h h2 (h1 h2), fun h1 h2 => (h1 h2).elim⟩
theorem imp_eq_true_of_right (a : Prop) {b : Prop} (h : b) : (a → b) = True := propext ⟨fun _ => trivial, fun _ _ => h⟩
theorem imp_eq_true_of_not_left {a : Prop} (b : Prop) (h : ¬ a) : (a → b) = True :=
  propext ⟨fun _ => trivial, fun _ h' => (h h').elim⟩
theorem imp_eq_of_left {a : Prop} (b : Prop) (h : a) : (a → b) = b := propext ⟨fun h' => h' h, fun h' _ => h'⟩
theorem forall_eq_of_left {a : Prop} (p : a → Prop) (h : a) : (∀ x, p x) = p h :=
  propext ⟨fun h' => h' h, fun h' _ => h'⟩
theorem forall_const' (α : Sort u) [Nonempty α] (b : Prop) : (α → b) = b :=
  propext ⟨fun h => h (Classical.choice inferInstance), fun h _ => h⟩
theorem exists_const' (α : Sort u) [Nonempty α] (b : Prop) : (∃ _ : α, b) = b :=
  propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨Classical.choice inferInstance, h⟩⟩

/-! ## Equality (see `optimizeEq`) -/

/-- Any two proofs of a proposition are equal (proof irrelevance). -/
theorem eq_proof_irrel {p : Prop} (a b : p) : (a = b) = True := eq_true (proof_irrel a b)

theorem false_eq' (e : Prop) : (False = e) = ¬ e :=
  propext ⟨fun h h' => h ▸ h', fun h => propext ⟨False.elim, h⟩⟩
theorem true_eq' (e : Prop) : (True = e) = e := propext ⟨fun h => h ▸ trivial, fun h => (eq_true h).symm⟩
theorem eq_not_self' (e : Prop) : (e = ¬ e) = False := by
  apply propext; constructor
  . intro h; have h1 : ¬ e := fun he => (h ▸ he) he; exact h1 (h ▸ h1)
  . intro h; exact h.elim
theorem bool_eq_not_self (e : Bool) : (e = !e) = False := by cases e <;> simp
theorem true_eq_not (e : Bool) : (true = !e) = (false = e) := by cases e <;> simp
theorem false_eq_not (e : Bool) : (false = !e) = (true = e) := by cases e <;> simp
theorem not_eq_not_bool (a b : Bool) : ((!a) = !b) = (a = b) := by cases a <;> cases b <;> simp
theorem not_eq_not_prop (a b : Prop) : ((¬ a) = (¬ b)) = (a = b) := by
  apply propext; constructor
  . intro h; apply propext; constructor
    . intro ha; exact Classical.byContradiction (fun hb => (h ▸ hb : ¬ a) ha)
    . intro hb; exact Classical.byContradiction (fun ha => (h.symm ▸ ha : ¬ b) hb)
  . intro h; rw [h]
theorem int_neg_eq_neg (a b : Int) : (Int.neg a = Int.neg b) = (a = b) := propext Int.neg_inj

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Arithmetic cancellation under non-zero hypotheses (see `optimizeEq`) -/

theorem nat_ne_zero_of_pos {x : Nat} (h : 0 < x) : ¬ (0 = x) := fun h' => by omega
theorem nat_ne_zero_of_lit {x : Nat} (h : Nat.beq x 0 = false) : ¬ (0 = x) :=
  fun h' => by subst h'; contradiction
theorem int_ne_zero_of_pos {x : Int} (h : 0 < x) : ¬ (0 = x) := fun h' => by omega
theorem int_ne_zero_of_neg {x : Int} (h : x < 0) : ¬ (0 = x) := fun h' => by omega
theorem int_ne_zero_of_lit {x : Int} (h : (x == 0) = false) : ¬ (0 = x) :=
  fun h' => by subst h'; contradiction

theorem nat_mul_cancel_ll {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (Nat.mul x y = Nat.mul x z) = (y = z) :=
  propext ⟨Nat.eq_of_mul_eq_mul_left (by omega), fun h => h ▸ rfl⟩
theorem nat_mul_cancel_lr {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (Nat.mul x y = Nat.mul z x) = (y = z) := by
  rw [show Nat.mul z x = Nat.mul x z from Nat.mul_comm z x]; exact nat_mul_cancel_ll y z h
theorem nat_mul_cancel_rl {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (Nat.mul y x = Nat.mul x z) = (y = z) := by
  rw [show Nat.mul y x = Nat.mul x y from Nat.mul_comm y x]; exact nat_mul_cancel_ll y z h
theorem nat_mul_cancel_rr {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (Nat.mul y x = Nat.mul z x) = (y = z) := by
  rw [show Nat.mul y x = Nat.mul x y from Nat.mul_comm y x, show Nat.mul z x = Nat.mul x z from Nat.mul_comm z x]
  exact nat_mul_cancel_ll y z h
theorem int_mul_cancel_ll {x : Int} (y z : Int) (h : ¬ (0 = x)) : (Int.mul x y = Int.mul x z) = (y = z) :=
  propext ⟨Int.eq_of_mul_eq_mul_left (fun h' => h h'.symm), fun h => h ▸ rfl⟩
theorem int_mul_cancel_lr {x : Int} (y z : Int) (h : ¬ (0 = x)) : (Int.mul x y = Int.mul z x) = (y = z) := by
  rw [show Int.mul z x = Int.mul x z from Int.mul_comm z x]; exact int_mul_cancel_ll y z h
theorem int_mul_cancel_rl {x : Int} (y z : Int) (h : ¬ (0 = x)) : (Int.mul y x = Int.mul x z) = (y = z) := by
  rw [show Int.mul y x = Int.mul x y from Int.mul_comm y x]; exact int_mul_cancel_ll y z h
theorem int_mul_cancel_rr {x : Int} (y z : Int) (h : ¬ (0 = x)) : (Int.mul y x = Int.mul z x) = (y = z) := by
  rw [show Int.mul y x = Int.mul x y from Int.mul_comm y x, show Int.mul z x = Int.mul x z from Int.mul_comm z x]
  exact int_mul_cancel_ll y z h
/-- Cancellation lemmas in standard notation (used by `blaster_mul_cancel`). -/
theorem nat_mul_cancel_ll' {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (x * y = x * z) = (y = z) := nat_mul_cancel_ll y z h
theorem nat_mul_cancel_lr' {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (x * y = z * x) = (y = z) := nat_mul_cancel_lr y z h
theorem nat_mul_cancel_rl' {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (y * x = x * z) = (y = z) := nat_mul_cancel_rl y z h
theorem nat_mul_cancel_rr' {x : Nat} (y z : Nat) (h : ¬ (0 = x)) : (y * x = z * x) = (y = z) := nat_mul_cancel_rr y z h
theorem int_mul_cancel_ll' {x : Int} (y z : Int) (h : ¬ (0 = x)) : (x * y = x * z) = (y = z) := int_mul_cancel_ll y z h
theorem int_mul_cancel_lr' {x : Int} (y z : Int) (h : ¬ (0 = x)) : (x * y = z * x) = (y = z) := int_mul_cancel_lr y z h
theorem int_mul_cancel_rl' {x : Int} (y z : Int) (h : ¬ (0 = x)) : (y * x = x * z) = (y = z) := int_mul_cancel_rl y z h
theorem int_mul_cancel_rr' {x : Int} (y z : Int) (h : ¬ (0 = x)) : (y * x = z * x) = (y = z) := int_mul_cancel_rr y z h

macro "blaster_mul_cancel" : tactic =>
  `(tactic| simp (disch := omega) only [Blaster.Reconstruct.nat_mul_cancel_ll', Blaster.Reconstruct.nat_mul_cancel_lr',
      Blaster.Reconstruct.nat_mul_cancel_rl', Blaster.Reconstruct.nat_mul_cancel_rr',
      Blaster.Reconstruct.int_mul_cancel_ll', Blaster.Reconstruct.int_mul_cancel_lr',
      Blaster.Reconstruct.int_mul_cancel_rl', Blaster.Reconstruct.int_mul_cancel_rr'] at *)

theorem nat_zero_eq_mul {x y : Nat} (hx : ¬ (0 = x)) (hy : ¬ (0 = y)) : (0 = Nat.mul x y) = False :=
  propext ⟨fun h => by
    have := Nat.mul_eq_zero.mp h.symm
    cases this <;> omega, False.elim⟩
theorem int_zero_eq_mul {x y : Int} (hx : ¬ (0 = x)) (hy : ¬ (0 = y)) : (0 = Int.mul x y) = False :=
  propext ⟨fun h => by
    have := Int.mul_eq_zero.mp h.symm
    cases this <;> omega, False.elim⟩

/-! ## Inhabited types (see `optimizeForall`) -/

theorem nonempty_of_inhabited (α : Sort u) [Inhabited α] : Nonempty α := ⟨default⟩

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## `Blaster.dite'` normalization (see `optimizeDITEChoice`) -/

theorem dite'_not_swap {α : Sort u} (c : Prop) (a b : α) :
    Blaster.dite' (¬ c) (fun _ => a) (fun _ => b) = Blaster.dite' c (fun _ => b) (fun _ => a) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]
  by_cases h : c <;> simp [h]

theorem dite'_false_swap {α : Sort u} (c : Bool) (a b : α) :
    Blaster.dite' (false = c) (fun _ => a) (fun _ => b) = Blaster.dite' (true = c) (fun _ => b) (fun _ => a) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]
  cases c <;> simp

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Relational operators (see `optimizeLE`) -/

theorem nat_le_eq_not_lt (a b : Nat) : (a ≤ b) = ¬ (b < a) := propext Nat.not_lt.symm
theorem int_le_eq_not_lt (a b : Int) : (a ≤ b) = ¬ (b < a) := propext Int.not_lt.symm
theorem bool_le_eq_not_lt (a b : Bool) : (a ≤ b) = ¬ (b < a) := by cases a <;> cases b <;> decide
theorem string_le_eq_not_lt (a b : String) : (a ≤ b) = ¬ (b < a) := rfl

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Function propagation over `Blaster.dite'` (see `normChoiceApplication?` and `funPropagation?`) -/

theorem dite'_app {α : Sort u} {β : α → Sort v} (c : Prop) (t : c → (a : α) → β a) (e : ¬ c → (a : α) → β a)
    (x : α) : Blaster.dite' c t e x = Blaster.dite' c (fun h => t h x) (fun h => e h x) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]
  by_cases h : c <;> simp [h]

theorem apply_dite' {α : Sort u} {β : Sort v} (g : α → β) (c : Prop) (t : c → α) (e : ¬ c → α) :
    g (Blaster.dite' c t e) = Blaster.dite' c (fun h => g (t h)) (fun h => g (e h)) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]
  by_cases h : c <;> simp [h]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## `Blaster.dite'` with non-dependent branches (see `iteSimp?` and `recordDITESimp`) -/

theorem dite'_same {α : Sort u} (c : Prop) (a : α) : Blaster.dite' c (fun _ => a) (fun _ => a) = a := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_true_false (c : Prop) : Blaster.dite' c (fun _ => True) (fun _ => False) = c := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_false_true (c : Prop) : Blaster.dite' c (fun _ => False) (fun _ => True) = ¬ c := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_true_left (c p : Prop) : Blaster.dite' c (fun _ => True) (fun _ => p) = (¬ c → p) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_false_left (c p : Prop) : Blaster.dite' c (fun _ => False) (fun _ => p) = (¬ c ∧ p) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_true_right (c p : Prop) : Blaster.dite' c (fun _ => p) (fun _ => True) = (c → p) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

theorem dite'_false_right (c p : Prop) : Blaster.dite' c (fun _ => p) (fun _ => False) = (c ∧ p) := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; by_cases h : c <;> simp [h]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Boolean connectives of `Blaster.decide'` (see `decideOpDecide?` and `recordDecideOp`) -/

theorem decide'_and_decide' (p q : Prop) :
    (Blaster.decide' p && Blaster.decide' q) = Blaster.decide' (p ∧ q) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem decide'_and_bool (p : Prop) (b : Bool) : (Blaster.decide' p && b) = Blaster.decide' (p ∧ true = b) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> cases b <;> simp [hp]

theorem bool_and_decide' (b : Bool) (p : Prop) : (b && Blaster.decide' p) = Blaster.decide' (p ∧ true = b) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> cases b <;> simp [hp]

theorem decide'_or_decide' (p q : Prop) :
    (Blaster.decide' p || Blaster.decide' q) = Blaster.decide' (p ∨ q) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem decide'_or_bool (p : Prop) (b : Bool) : (Blaster.decide' p || b) = Blaster.decide' (p ∨ true = b) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> cases b <;> simp [hp]

theorem bool_or_decide' (b : Bool) (p : Prop) : (b || Blaster.decide' p) = Blaster.decide' (p ∨ true = b) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]; by_cases hp : p <;> cases b <;> simp [hp]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## `Blaster.dite'` with a constant condition (see `optimizeDITEChoice`) -/

theorem dite'_pos {α : Sort u} (c : Prop) (t : c → α) (e : ¬ c → α) (h : c) : Blaster.dite' c t e = t h := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; simp [h]

theorem dite'_neg {α : Sort u} (c : Prop) (t : c → α) (e : ¬ c → α) (h : ¬ c) : Blaster.dite' c t e = e h := by
  simp only [Blaster.Reconstruct.dite'_eq_dite]; simp [h]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-- Cast a proof along an equality of propositions. Used to keep expressions well-typed when a
    hypothesis is declared with a rewritten type (see `LambdaWaitForType`, `ForallWaitForType`).
    NOTE: Stated as a theorem such that the SMT translation interprets it by its statement.
-/
theorem castProof {P Q : Prop} (h : P = Q) (p : P) : Q := h ▸ p

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-- Swap the branches of a `dite'` whose condition `c₀` is equal to `¬ c` (dependent branches). -/
theorem dite'_swap_dep {α : Sort u} {c₀ c : Prop} (pc : c₀ = ¬ c) (t : c₀ → α) (e : ¬ c₀ → α) :
    Blaster.dite' c₀ t e =
      Blaster.dite' c (fun h => e (fun h₀ => (castProof pc h₀) h)) (fun h => t (castProof pc.symm h)) := by
  subst pc
  simp only [Blaster.Reconstruct.dite'_eq_dite]
  by_cases h : c
  . have : ¬ ¬ c := fun h' => h' h
    simp [h]
  . simp [h]

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## `BEq` and `decide'` bridges (see `optimizeBEq` and `optimizeDecideEq`) -/

theorem bool_false_beq (e : Bool) : (false == e) = !e := by cases e <;> rfl
theorem bool_true_beq (e : Bool) : (true == e) = e := by cases e <;> rfl
theorem bool_beq_not_self (e : Bool) : (e == !e) = false := by cases e <;> rfl
theorem bool_not_beq_not (a b : Bool) : ((!a) == !b) = (a == b) := by cases a <;> cases b <;> rfl
theorem beq_self' {α : Type u} [BEq α] [LawfulBEq α] (a : α) : (a == a) = true := beq_self_eq_true a
theorem true_eq_beq {α : Type u} [BEq α] [LawfulBEq α] (a b : α) : (true = (a == b)) = (a = b) := by
  apply propext; constructor
  . intro h; exact eq_of_beq h.symm
  . intro h; subst h; exact (beq_self_eq_true a).symm
theorem false_eq_beq {α : Type u} [BEq α] [LawfulBEq α] (a b : α) : (false = (a == b)) = ¬ (a = b) := by
  apply propext; constructor
  . intro h h'; subst h'; rw [beq_self_eq_true] at h; contradiction
  . intro h; cases h' : a == b
    . rfl
    . exact (h (eq_of_beq h')).elim
theorem bool_eq_beq {α : Type u} [BEq α] [LawfulBEq α] (c : Bool) (a b : α) :
    (c = (a == b)) = ((true = c) = (a = b)) := by
  cases c
  . rw [false_eq_beq]; apply propext; constructor
    . intro h; apply propext; constructor
      . intro h'; exact Bool.noConfusion h'
      . intro h'; exact (h h').elim
    . intro h h'; exact Bool.noConfusion (h.mpr h')
  . rw [true_eq_beq]; simp
theorem beq_eq_bool {α : Type u} [BEq α] [LawfulBEq α] (c : Bool) (a b : α) :
    ((a == b) = c) = ((true = c) = (a = b)) := by
  rw [← bool_eq_beq]; exact propext ⟨Eq.symm, Eq.symm⟩
theorem bool_eq_bool_eq_tt (a b : Bool) : ((true = a) = (true = b)) = (a = b) := by
  cases a <;> cases b <;> simp
theorem bool_eq_bool_eq_tf (a b : Bool) : ((true = a) = (false = b)) = (a = !b) := by
  cases a <;> cases b <;> simp
theorem bool_eq_bool_eq_ft (a b : Bool) : ((false = a) = (true = b)) = ((!a) = b) := by
  cases a <;> cases b <;> simp
theorem bool_eq_bool_eq_ff (a b : Bool) : ((false = a) = (false = b)) = ((!a) = !b) := by
  cases a <;> cases b <;> simp
theorem true_eq_decide' (e : Prop) : (true = Blaster.decide' e) = e := by
  apply propext; constructor
  . intro h; exact (Blaster.decide'_true e).mp h.symm
  . intro h; exact ((Blaster.decide'_true e).mpr h).symm
theorem false_eq_decide' (e : Prop) : (false = Blaster.decide' e) = ¬ e := by
  apply propext; constructor
  . intro h; exact (Blaster.decide'_false e).mp h.symm
  . intro h; exact ((Blaster.decide'_false e).mpr h).symm
theorem decide'_eq_decide' (e1 e2 : Prop) : (Blaster.decide' e1 = Blaster.decide' e2) = (e1 = e2) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]
  apply propext; constructor
  . intro h; apply propext; constructor <;> intro h' <;> by_cases h1 : e1 <;> by_cases h2 : e2 <;> simp_all
  . intro h; subst h; rfl
theorem decide'_eq_bool (e : Prop) (b : Bool) : (Blaster.decide' e = b) = (e = (true = b)) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]
  cases b <;> by_cases h : e <;> simp [h]
theorem bool_eq_decide' (e : Prop) (b : Bool) : (b = Blaster.decide' e) = (e = (true = b)) := by
  simp only [Blaster.Reconstruct.decide'_eq_decide]
  cases b <;> by_cases h : e <;> simp [h]

end Blaster.Reconstruct
