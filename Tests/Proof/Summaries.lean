import Blaster
import Tests.Proof.Support

opaque summaryCall : Nat → Nat
theorem summaryIdentity (x : Nat) : summaryCall x = summaryCall x := rfl

example (law : ∀ x, x = 7 → summaryCall x = 9) : summaryCall 7 = 9 := by
  blaster (summaries: [law])

-- Instantiating a proved conditional must retain its precondition.
#reject "Goal was falsified" in
example (law : ∀ x, x = 7 → summaryCall x = 9) (x : Nat) : summaryCall x = 9 := by
  blaster (summaries: [law]) (timeout: 10)

open Lean Elab Command Meta
run_cmd Command.liftTermElabM do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let facts ← Blaster.Proof.Summary.instantiate goal.mvarId! #[mkConst ``summaryIdentity]
  unless facts.isEmpty do throwError "an absent call produced summary facts"

#reject "must be monomorphic" in
@[blaster_library] theorem polymorphicIdentity {α : Type u} (x : α) : x = x := by
  blaster
