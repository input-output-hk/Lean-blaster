import Init.GrindInstances.Ring.Fin

/-!
# Nominal modular rings

`Residue p` has exactly the representation `Fin p`, without inheriting its
truncating division. Ring laws, characteristic, literals, casts and natural
powers require only `NeZero p`; the inherited additive and multiplicative
operations also exist on the empty carrier. No primality evidence, inverse,
division, or solver dependency is supplied here.
-/

namespace Blaster.FiniteField

/-- A nominal modular ring, deliberately not an abbreviation for `Fin p`. -/
structure Residue (p : Nat) where
  rep : Fin p
  deriving DecidableEq, Repr

namespace Residue

variable {p : Nat} [NeZero p]

instance : Inhabited (Residue p) := ⟨⟨0⟩⟩
instance : Add (Residue p) := ⟨fun a b => ⟨a.rep + b.rep⟩⟩
instance : Mul (Residue p) := ⟨fun a b => ⟨a.rep * b.rep⟩⟩
instance : Neg (Residue p) := ⟨fun a => ⟨-a.rep⟩⟩
instance : Sub (Residue p) := ⟨fun a b => ⟨a.rep - b.rep⟩⟩
instance (n : Nat) : OfNat (Residue p) n := ⟨⟨OfNat.ofNat n⟩⟩
instance : NatCast (Residue p) := ⟨fun n => ⟨Fin.ofNat p n⟩⟩
instance : IntCast (Residue p) := ⟨fun n => ⟨Lean.Grind.Ring.intCast (α := Fin p) |>.intCast n⟩⟩
instance : HPow (Residue p) Nat (Residue p) := ⟨fun a n => ⟨a.rep ^ n⟩⟩
instance : SMul Nat (Residue p) := ⟨fun n a => (n : Residue p) * a⟩
instance : SMul Int (Residue p) := ⟨fun n a => (n : Residue p) * a⟩

omit [NeZero p] in
/-- Equality transport is injective; no quotient or unchecked cast is involved. -/
theorem ext {a b : Residue p} (h : a.rep = b.rep) : a = b := by
  cases a; cases b; cases h; rfl

instance : Lean.Grind.CommRing (Residue p) where
  add_assoc a b c := ext (Lean.Grind.Semiring.add_assoc a.rep b.rep c.rep)
  add_comm a b := ext (Lean.Grind.Semiring.add_comm a.rep b.rep)
  add_zero a := ext (Lean.Grind.Semiring.add_zero a.rep)
  mul_assoc a b c := ext (Lean.Grind.Semiring.mul_assoc a.rep b.rep c.rep)
  mul_comm a b := ext (Lean.Grind.CommSemiring.mul_comm a.rep b.rep)
  mul_one a := ext (Lean.Grind.Semiring.mul_one a.rep)
  left_distrib a b c := ext (Lean.Grind.Semiring.left_distrib a.rep b.rep c.rep)
  one_mul a := ext (Lean.Grind.Semiring.one_mul a.rep)
  mul_zero a := ext (Lean.Grind.Semiring.mul_zero a.rep)
  right_distrib a b c := ext (Lean.Grind.Semiring.right_distrib a.rep b.rep c.rep)
  zero_mul a := ext (Lean.Grind.Semiring.zero_mul a.rep)
  neg_add_cancel a := ext (Lean.Grind.Ring.neg_add_cancel a.rep)
  sub_eq_add_neg a b := ext (Lean.Grind.Ring.sub_eq_add_neg a.rep b.rep)
  pow_zero a := ext (Lean.Grind.Semiring.pow_zero a.rep)
  pow_succ a n := ext (Lean.Grind.Semiring.pow_succ a.rep n)
  ofNat_succ n := ext (Lean.Grind.Semiring.ofNat_succ (α := Fin p) n)
  intCast_neg n := ext (Lean.Grind.Ring.intCast_neg (α := Fin p) n)
  neg_zsmul n a := ext (Lean.Grind.Ring.neg_zsmul n a.rep)
  zsmul_natCast_eq_nsmul n a := ext (Lean.Grind.Ring.zsmul_natCast_eq_nsmul n a.rep)

instance : Lean.Grind.IsCharP (Residue p) p := Lean.Grind.IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun n => by
    change (Residue.mk (Fin.ofNat p n) = Residue.mk (Fin.ofNat p 0)) ↔ _
    simp only [Residue.mk.injEq, Fin.ofNat, Fin.mk.injEq, Nat.zero_mod])

end Residue
end Blaster.FiniteField
