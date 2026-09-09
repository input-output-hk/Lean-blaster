import PlutusCore.UPLC.LoopCek

namespace PlutusCore.UPLC.LoopCek
open PlutusCore.Default CekMachine CekValue Term Builtins
open BuiltinFunctions.Evaluate
set_option maxHeartbeats 0

private theorem lookup_correct (sv : BuiltinSemanticsVariant) (n : Nat)
    (s : Stack) (env : Environment) (x : String) :
    (match lookupValue env x with
     | some v => runSteps sv (.Return s v) n
     | none => .Error) =
      runSteps sv (ifBoundOtherwiseError s env x) n := by
  cases env with
  | EmptyEnvironment => simp [lookupValue, ifBoundOtherwiseError, runSteps]
  | NonEmptyEnvironment rest y v =>
    by_cases h : x = y
    · simp [lookupValue, ifBoundOtherwiseError, h]
    · simpa only [lookupValue, ifBoundOtherwiseError, h, if_false] using
        lookup_correct sv n s rest x
termination_by sizeOf env


theorem eval_ret_correct (sv : BuiltinSemanticsVariant) (fuel : Nat) :
    (∀ s env t, eval sv fuel s env t = runSteps sv (.Eval s env t) fuel) ∧
    (∀ s v, ret sv fuel s v = runSteps sv (.Return s v) fuel) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel strong =>
    cases fuel with
    | zero =>
        constructor <;> intros <;> simp [eval, ret, runSteps]
    | succ n =>
      have ih := strong n (Nat.lt_succ_self n)
      constructor
      · intro s env t
        cases t <;> try simp only [eval]
        all_goals try simp only [ih.1, ih.2]
        case Var x =>
          simpa only [runSteps, step] using (lookup_correct sv n s env x)
        case Constr i ts => cases ts <;> simp only [eval, ih.1, ih.2, runSteps, step]
        all_goals first | rfl | simp [runSteps, step]
      · intro s v
        cases s with
        | nil => simp [ret, runSteps, step]
        | cons frame rest =>
          cases frame with
          | LeftApplicationToTerm body env =>
              simp only [ret, ih.1]
              rfl
          | RightApplicationOfValue f =>
              cases f <;> try simp only [ret, ih.1]
              case VLam x body env =>
                change _ = runSteps sv (.Eval rest (.NonEmptyEnvironment env x v) body) n
                cases hp : RecursiveCalls.recognize x body env v with
                | none => simpa only [hp] using ih.1 rest (.NonEmptyEnvironment env x v) body
                | some plan =>
                  obtain ⟨cert, hworker⟩ := RecursiveCalls.recognize_sound x body env v plan hp
                  have correct := cert.correct sv n rest
                  rw [hworker] at correct
                  cases hw : plan.worker sv n with
                  | none => simpa only [hw] using correct
                  | some pair =>
                    rcases pair with ⟨remaining,result⟩
                    have lt := cert.spends sv n remaining result (by simpa only [hworker] using hw)
                    simp only [lt]
                    rw [(strong remaining (by omega)).2]
                    simpa only [hw] using correct
              case VBuiltin b vs expected =>
                cases expected with
                | More arg tail => cases arg <;> simp [ret, ih.2, runSteps, step, ifArgVOtherwiseError]
                | One arg =>
                    cases arg <;> simp only [ret, ih.2, runSteps, step, ifArgVOtherwiseError, evalBuiltin]
                    case ArgV => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | LeftApplicationToValue arg =>
              cases v <;> try simp only [ret, ih.1]
              case VBuiltin b vs expected =>
                cases expected with
                | More next tail => cases next <;> simp [ret, ih.2, runSteps, step, ifArgVOtherwiseError]
                | One next =>
                    cases next <;> simp only [ret, ih.2, runSteps, step, ifArgVOtherwiseError, evalBuiltin]
                    case ArgV => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | ForceFrame =>
              cases v <;> try simp only [ret, ih.1]
              case VBuiltin b vs expected =>
                cases expected with
                | More next tail => cases next <;> simp [ret, ih.2, runSteps, step, ifArgQOtherwiseError]
                | One next =>
                    cases next <;> simp only [ret, ih.2, runSteps, step, ifArgQOtherwiseError, evalBuiltin]
                    case ArgQ => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | ConstructorArgument i vs ts env =>
              cases ts <;> simp [ret, ih.1, ih.2, runSteps, step]
          | CaseScrutinee ts env =>
              rw [ret.eq_def]
              simp only [ih.1, runSteps]
              unfold step
              split <;> simp_all [runSteps] <;>
                repeat (first | assumption | rfl | (split <;> simp_all [runSteps]))
              all_goals by_cases h : ts.length = 1 ∨ ts.length = 2 <;>
                simp_all [runSteps] <;> split <;> simp_all [runSteps]

/-- Kernel-checked equality for every machine state, fuel, and builtin semantics
variant, including constructor fields and primitive case branches. -/
theorem run_eq_runSteps (sv : BuiltinSemanticsVariant) (s : State) (fuel : Nat) :
    run sv s fuel = runSteps sv s fuel := by
  cases s with
  | Eval stack env t => exact (eval_ret_correct sv fuel).1 stack env t
  | Return stack v => exact (eval_ret_correct sv fuel).2 stack v
  | Halt v => simp [run, runSteps]
  | Error => simp [run, runSteps]

theorem execute_eq (p : Program) (params : List Term) (fuel : Nat) :
    execute p params fuel = cekExecuteProgram p params fuel := by
  cases p
  simp only [execute, cekExecuteProgram, cekExecuteProgramWithSemanticVariant, run_eq_runSteps]

#print axioms run_eq_runSteps
#print axioms execute_eq
end PlutusCore.UPLC.LoopCek
