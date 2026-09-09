import PlutusCore.UPLC.LiftedSearch
open PlutusCore.UPLC PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins PlutusCore.Data PlutusCore.Default
namespace PlutusCore.UPLC.LiftedSearch
open CekBlocks
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem empty_block (sv : BuiltinSemanticsVariant) (env : Environment) (ready : Ready env) (s : Stack) :
    advance sv 16 (entry env s []) = .Return s (.VCon (.Data (.Constr 1 []))) := by
  simp [advance, entry, originalBody, step,
    ifBoundOtherwiseError, ifArgVOtherwiseError, evalBuiltin,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList,                                 v3, ready.currentValid.bound3]

theorem hit_block (sv : BuiltinSemanticsVariant) (env : Environment) (ready : Ready env)
    (s : Stack) (i : Int) (tail : List (Data × Data)) :
    advance sv 103 (entry env s ((.B { data := "" }, .I i) :: tail)) =
      .Return s (.VCon (.Data (.Constr 0 [.I i]))) := by
  simp [advance, entry, originalBody, step,
    ifBoundOtherwiseError, ifArgVOtherwiseError, evalBuiltin,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.List.headList, BuiltinFunctions.List.tailList,
    BuiltinFunctions.Pair.fstPair, BuiltinFunctions.Pair.sndPair,
    BuiltinFunctions.Data.unBData, BuiltinFunctions.Data.unIData,
    BuiltinFunctions.ByteString.equalsByteString, BuiltinFunctions.Bool.ifThenElse,
    BuiltinFunctions.Utils.tryCatchSome, PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Data.unBData, PlutusCore.Data.unIData,
    PlutusCore.ByteString.equalsByteString, PlutusCore.ByteString.PlutusCore.ByteStringInternal.BEqByteString,
    PlutusCore.Bool.ifThenElse, PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair,
    Pure.pure, Except.pure, expectedArgs, v0, ready.currentValid.bound0, v1, ready.currentValid.bound1, v2, ready.currentValid.bound2, v3, ready.currentValid.bound3, v4, ready.currentValid.bound4, v5, ready.currentValid.bound5, v6, ready.currentValid.bound6, BuiltinFunctions.Data.constrData, BuiltinFunctions.Data.iData,
    BuiltinFunctions.List.mkCons, PlutusCore.Data.constrData, PlutusCore.Data.iData, PlutusCore.List.mkCons]

theorem miss_block (sv : BuiltinSemanticsVariant) (env : Environment) (ready : Ready env)
    (s : Stack) (b : PlutusCore.ByteString.ByteString) (i : Int) (tail : List (Data × Data))
    (h : ("" == b.data) = false) :
    advance sv 92 (entry env s ((.B b, .I i) :: tail)) = entry (recurEnv ready.captured) s tail := by
  simp [advance, entry, recurEnv, originalBody, step,
    ifBoundOtherwiseError, ifArgVOtherwiseError, evalBuiltin,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.List.headList, BuiltinFunctions.List.tailList,
    BuiltinFunctions.Pair.fstPair, BuiltinFunctions.Pair.sndPair,
    BuiltinFunctions.Data.unBData, BuiltinFunctions.Data.unIData,
    BuiltinFunctions.ByteString.equalsByteString, BuiltinFunctions.Bool.ifThenElse,
    BuiltinFunctions.Utils.tryCatchSome, PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Data.unBData, PlutusCore.Data.unIData,
    PlutusCore.ByteString.equalsByteString, PlutusCore.ByteString.PlutusCore.ByteStringInternal.BEqByteString,
    PlutusCore.Bool.ifThenElse, PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair,
    Pure.pure, Except.pure, expectedArgs, v0, ready.currentValid.bound0, v1, ready.currentValid.bound1, v3, ready.currentValid.bound3, v4, ready.currentValid.bound4, v5, ready.currentValid.bound5, v6, ready.currentValid.bound6, ready.recursiveBinding, h]

theorem invalid_key_block (sv : BuiltinSemanticsVariant) (env : Environment) (ready : Ready env)
    (s : Stack) (key value : Data) (tail : List (Data × Data)) (h : ∀ b, key ≠ Data.B b) :
    advance sv 45 (entry env s ((key,value) :: tail)) = .Error := by
  cases key
  all_goals try simp_all [advance, entry, originalBody, step,
    ifBoundOtherwiseError, ifArgVOtherwiseError, evalBuiltin,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.List.headList, BuiltinFunctions.List.tailList,
    BuiltinFunctions.Pair.fstPair,     BuiltinFunctions.Data.unBData,         BuiltinFunctions.Utils.tryCatchSome, PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Data.unBData,         PlutusCore.Pair.fstPair,     Pure.pure, Except.pure, expectedArgs, v0, ready.currentValid.bound0, v1, ready.currentValid.bound1, v3, ready.currentValid.bound3, v5, ready.currentValid.bound5]

theorem invalid_value_block (sv : BuiltinSemanticsVariant) (env : Environment) (ready : Ready env)
    (s : Stack) (b : PlutusCore.ByteString.ByteString) (value : Data)
    (tail : List (Data × Data)) (h : ∀ i, value ≠ Data.I i) :
    advance sv 58 (entry env s ((.B b,value) :: tail)) = .Error := by
  cases value
  all_goals try simp_all [advance, entry, originalBody, step,
    ifBoundOtherwiseError, ifArgVOtherwiseError, evalBuiltin,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.List.headList, BuiltinFunctions.List.tailList,
    BuiltinFunctions.Pair.fstPair, BuiltinFunctions.Pair.sndPair,
    BuiltinFunctions.Data.unBData, BuiltinFunctions.Data.unIData,
        BuiltinFunctions.Utils.tryCatchSome, PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Data.unBData, PlutusCore.Data.unIData,
        PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair,
    Pure.pure, Except.pure, expectedArgs, v0, ready.currentValid.bound0, v1, ready.currentValid.bound1, v3, ready.currentValid.bound3, v4, ready.currentValid.bound4, v5, ready.currentValid.bound5]

def finish (sv : BuiltinSemanticsVariant) (s : Stack) (result : Option (Nat × Data)) : State :=
  match result with
  | none => .Error
  | some (remaining,d) => runSteps sv (.Return s (.VCon (.Data d))) remaining

/-- The whole loop is independent of irrelevant captured bindings, provided the
checked builtin and self bindings hold in the current and recursive environments. -/
theorem scan_correct (sv : BuiltinSemanticsVariant) (xs : List (Data × Data))
    (env : Environment) (ready : Ready env) (fuel : Nat) (s : Stack) :
    finish sv s (scan fuel xs) = runSteps sv (entry env s xs) fuel := by
  induction xs generalizing env fuel with
  | nil =>
    rw [shortcut sv 16 _ _ (empty_block sv env ready s) rfl]
    simp only [scan]
    split <;> simp_all [finish]
  | cons pair tail ih =>
    rcases pair with ⟨key,value⟩
    cases key <;> try {
      simp only [scan, finish]
      symm
      apply block_error sv 45
      apply invalid_key_block sv env ready
      intro b; simp }
    case B b =>
      cases value <;> try {
        simp only [scan, finish]
        symm
        apply block_error sv 58
        apply invalid_value_block sv env ready
        intro i; simp }
      case I i =>
        by_cases eq : ("" == b.data) = true
        · have beq : b = { data := "" } := by cases b; simp_all
          subst b
          rw [shortcut sv 103 _ _ (hit_block sv env ready s i tail) rfl]
          simp only [scan, beq_self_eq_true, if_true]
          split <;> simp_all [finish]
        · have neq : ("" == b.data) = false := by simpa using eq
          rw [shortcut sv 92 _ _ (miss_block sv env ready s b i tail neq) rfl]
          simp only [scan, neq, Bool.false_eq_true, if_false]
          split
          · exact ih _ (recurReady _ ready.capturedValid) _
          · rfl

#print axioms scan_correct

#print axioms empty_block
#print axioms hit_block
#print axioms miss_block
end PlutusCore.UPLC.LiftedSearch
