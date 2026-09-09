import PlutusCore.UPLC.StagedCekProofs
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.Default
namespace PlutusCore.UPLC.CekBlocks

/-- Run a finite block while preserving terminal states and the final live state. -/
def advance (sv : BuiltinSemanticsVariant) (n : Nat) (st : State) : State :=
  match n, st with
  | 0, _ => st
  | _, .Halt _ | _, .Error => st
  | n+1, _ => advance sv n (step sv st)

theorem compose (sv : BuiltinSemanticsVariant) (n : Nat) (st : State) (fuel : Nat) :
    runSteps sv st (n+fuel) = runSteps sv (advance sv n st) fuel := by
  induction n generalizing st with
  | zero => simp [advance]
  | succ n ih =>
    cases st <;> simp only [advance, Nat.succ_add, runSteps]
    all_goals first | rfl | exact ih _

theorem run_terminal (sv : BuiltinSemanticsVariant) (n : Nat) (st : State) :
    runSteps sv st n = .Error ∨ ∃ v, runSteps sv st n = .Halt v := by
  induction n generalizing st with
  | zero => cases st <;> simp [runSteps]
  | succ n ih =>
    cases st <;> simp only [runSteps]
    all_goals first | simp | exact ih _

theorem extend_halt (sv : BuiltinSemanticsVariant) (n : Nat) (st : State)
    (v : CekValue) (h : runSteps sv st n = .Halt v) (extra : Nat) :
    runSteps sv st (n+extra) = .Halt v := by
  induction n generalizing st with
  | zero => cases st <;> simp_all [runSteps]
  | succ n ih =>
    cases st <;> simp_all only [Nat.succ_add, runSteps]
    all_goals first | rfl | exact ih _ h

theorem shorter_error (sv : BuiltinSemanticsVariant) (n : Nat) (st : State)
    (h : runSteps sv st n = .Error) (fuel : Nat) (le : fuel ≤ n) :
    runSteps sv st fuel = .Error := by
  rcases run_terminal sv fuel st with done | ⟨v,hv⟩
  · exact done
  · have extended := extend_halt sv fuel st v hv (n-fuel)
    rw [Nat.add_sub_of_le le, h] at extended
    cases extended

theorem shortcut (sv : BuiltinSemanticsVariant) (n : Nat) (st next : State)
    (h : advance sv n st = next) (live : runSteps sv next 0 = .Error) (fuel : Nat) :
    runSteps sv st fuel = if n ≤ fuel then runSteps sv next (fuel-n) else .Error := by
  by_cases enough : n ≤ fuel
  · simp only [enough, if_true]
    have eq := compose sv n st (fuel-n)
    simpa only [Nat.add_sub_of_le enough, h] using eq
  · simp only [enough, if_false]
    apply shorter_error sv n st _ fuel (by omega)
    have eq := compose sv n st 0
    simpa only [Nat.add_zero, h, live] using eq

theorem block_error (sv : BuiltinSemanticsVariant) (n : Nat) (st : State)
    (h : advance sv n st = .Error) (fuel : Nat) : runSteps sv st fuel = .Error := by
  simpa only [runSteps, ite_self] using shortcut sv n st .Error h rfl fuel

#print axioms compose
#print axioms shorter_error
end PlutusCore.UPLC.CekBlocks
