import Blaster

namespace Test.SmtTypeEq

theorem unit_ne_bool : Unit ≠ Bool := by
  intro h
  have hs : Subsingleton Bool := h ▸ (inferInstance : Subsingleton Unit)
  have he : (true : Bool) = false := @Subsingleton.elim Bool hs true false
  cases he

theorem type_equality : ∀ (α : Type), α = Unit → α ≠ Bool := by
  intro α h
  subst α
  exact unit_ne_bool

/-- error: translateEq?: equality between types is not supported -/
#guard_msgs in
#blaster (only-smt-lib: 1) [type_equality]

/-- error: translateEq?: equality between types is not supported -/
#guard_msgs in
#blaster (only-smt-lib: 1) [Unit ≠ Bool]

abbrev BoolAlias := Bool

/-- info: ✅ Valid -/
#guard_msgs in
#blaster (only-smt-lib: 1) [BoolAlias = Bool]

/-- info: ✅ Valid -/
#guard_msgs in
#blaster (only-smt-lib: 1) [∀ (α : Type), α = α]

/-- warning: ⚠️ Undetermined -/
#guard_msgs in
#blaster (only-smt-lib: 1) [∀ (p q : Prop), p = q]

/-- warning: ⚠️ Undetermined -/
#guard_msgs in
#blaster (only-smt-lib: 1) [∀ (x y : Nat), x = y]

end Test.SmtTypeEq
