import PlutusCore.UPLC
import Tests.Utils

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins PlutusCore.UPLC.Term

namespace CardanoStaticControl
set_option maxHeartbeats 0

-- These equations are kernel checked against the pinned interpreter. The
-- optimization annotation changes only reduction order, never CEK fuel.
theorem lookup_hit (s : Stack) (env : Environment) (x : String) (v : CekValue) :
    ifBoundOtherwiseError s (.NonEmptyEnvironment env x v) x = .Return s v := by
  simp [ifBoundOtherwiseError]

theorem lookup_skip (s : Stack) (env : Environment) (x y : String)
    (v : CekValue) (h : x ≠ y) :
    ifBoundOtherwiseError s (.NonEmptyEnvironment env y v) x =
      ifBoundOtherwiseError s env x := by
  simp [ifBoundOtherwiseError, h]

theorem static_access (s : Stack) (env : Environment) (v discarded : CekValue) :
    ifBoundOtherwiseError s
      (.NonEmptyEnvironment (.NonEmptyEnvironment env "x" v) "unused" discarded)
      "x" = .Return s v := by
  simp [ifBoundOtherwiseError]

theorem variable_fuel_one (sv : BuiltinSemanticsVariant) (v : CekValue) :
    runSteps sv (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 1 =
      .Error := by
  simp [runSteps, step, ifBoundOtherwiseError]

theorem variable_fuel_two (sv : BuiltinSemanticsVariant) (v : CekValue) :
    runSteps sv (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 2 =
      .Halt v := by
  simp [runSteps, step, ifBoundOtherwiseError]

attribute [local blaster_specialize] ifBoundOtherwiseError step runSteps

#testOptimize ["StaticCekShadowing"]
  (fun v discarded : CekValue =>
    runSteps .defaultFunSemanticsVariantA
      (.Eval [] (.NonEmptyEnvironment (.NonEmptyEnvironment .EmptyEnvironment "x" discarded) "x" v)
        (.Var "x")) 2) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["StaticCekMissingName"]
  (fun v : CekValue => runSteps .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "other" v) (.Var "x")) 2) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StaticCekLookupFuel"]
  (fun v : CekValue => runSteps .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 1) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StaticCekCapturedEnvironment"]
  (fun v other : CekValue => runSteps .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue
      (.VLam "argument" (.Var "captured") (.NonEmptyEnvironment .EmptyEnvironment "captured" v))]
      other) 3) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["StaticCekHaltAtZeroFuel"]
  (fun v : CekValue => runSteps .defaultFunSemanticsVariantA (.Halt v) 0) ===>
  (fun v : CekValue => State.Halt v)

#testOptimize ["StaticCekErrorAtZeroFuel"]
  (runSteps .defaultFunSemanticsVariantA .Error 0) ===> State.Error

end CardanoStaticControl
