import Blaster
import Tests.Proof.Support

/-! `Fin n` has exactly the values `0, ..., n-1`. In particular, `Fin 0` is
empty and three values of `Fin 2` cannot all be distinct. -/

theorem fin_zero_empty : ∀ _x : Fin 0, False := by
  blaster (timeout: 10)

theorem fin_two_pigeonhole : ∀ x y z : Fin 2, x = y ∨ y = z ∨ x = z := by
  blaster (timeout: 10)

theorem fin_two_val_lt : ∀ x : Fin 2, x.val < 2 := by
  blaster (timeout: 10)

theorem fin_two_values : ∀ x : Fin 2, x.val = 0 ∨ x.val = 1 := by
  blaster (timeout: 10)

theorem fin_two_distinct : (0 : Fin 2) ≠ 1 := by
  blaster (timeout: 10)

theorem fin_mk_val (x : Nat) (h : x < 2) : (Fin.mk x h).val = x := by
  blaster (timeout: 10)

theorem fin_add_val (x : Fin 5) : (x + 1).val = (x.val + 1) % 5 := by
  blaster (timeout: 10)

theorem fin_add_comm (x y : Fin 5) : x + y = y + x := by
  blaster (timeout: 10)

private structure WrappedFin where
  value : Fin 2

theorem fin_field_range (x : WrappedFin) : x.value.val < 2 := by
  blaster (timeout: 10)

private def finFieldBound : Nat := 2 ^ 381 - 19

theorem fin_large_bound : ∀ x : Fin finFieldBound, x.val < finFieldBound := by
  blaster (timeout: 10)

#reject "non-constant Fin bound is not supported" in
theorem fin_symbolic_bound (n : Nat) : ∀ x : Fin n, x.val = 0 := by
  blaster (timeout: 10)

/-! These false implications used to become valid when `Fin n` was modeled as
an unbounded `Int`, so keep them as soundness regressions. -/

#reject "Goal was falsified" in
theorem fin_pigeonhole_false : (∀ x y z : Fin 2, x = y ∨ y = z ∨ x = z) → False := by
  blaster (timeout: 10)

#reject "Goal was falsified" in
theorem fin_zero_false : (∀ x : Fin 0, x ≠ x) → False := by
  blaster (timeout: 10)
