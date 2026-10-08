import Tests.Proof.Lists

/-! Imported facts are selected automatically; invalid registrations are rejected. -/
set_option maxHeartbeats 0

namespace Tests.Library

-- No explicit summary: the imported insertion theorem must be discovered.
theorem imported_sort (xs : List Int) : Tests.Lists.sorted (Tests.Lists.isort xs) = true := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

#reject "must be monomorphic" in
@[blaster_library] theorem polymorphic_identity {α : Type u} (x : α) : x = x := by
  blaster

axiom foreignFalse : False

#reject "depends on the axioms" in
@[blaster_library] theorem foreign_fact : True ∧ False := by
  have h : True := by blaster
  exact ⟨h, foreignFalse⟩

#reject "depends on the axioms" in
@[blaster_library] theorem sorry_fact : True ∧ False := by
  have h : True := by blaster
  exact ⟨h, @sorryAx False true⟩

#reject "requires a theorem" in
@[blaster_library] def non_theorem : Nat := 0

#print axioms imported_sort
end Tests.Library
