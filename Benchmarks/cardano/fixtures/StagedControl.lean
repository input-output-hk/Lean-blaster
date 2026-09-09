import PlutusCore.UPLC
import Tests.Benchmarks.OptimizeTestUtils

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins PlutusCore.UPLC.Term

namespace CardanoStagedControl
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

theorem variable_fuel_one (sv : PlutusCore.Default.BuiltinSemanticsVariant) (v : CekValue) :
    runSteps sv (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 1 =
      .Error := by
  simp [runSteps, step, ifBoundOtherwiseError]

theorem variable_fuel_two (sv : PlutusCore.Default.BuiltinSemanticsVariant) (v : CekValue) :
    runSteps sv (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 2 =
      .Halt v := by
  simp [runSteps, step, ifBoundOtherwiseError]

attribute [local blaster_specialize 2] PlutusCore.UPLC.StagedCek.eval PlutusCore.UPLC.StagedCek.ret
attribute [local blaster_specialize 1] PlutusCore.UPLC.StagedCek.lookupValue

#testOptimize ["StagedCekShadowing"]
  (fun v discarded : CekValue =>
    PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
      (.Eval [] (.NonEmptyEnvironment (.NonEmptyEnvironment .EmptyEnvironment "x" discarded) "x" v)
        (.Var "x")) 2) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["StagedCekMissingName"]
  (fun v : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "other" v) (.Var "x")) 2) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StagedCekLookupFuel"]
  (fun v : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 1) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StagedCekCapturedEnvironment"]
  (fun v other : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue
      (.VLam "argument" (.Var "captured") (.NonEmptyEnvironment .EmptyEnvironment "captured" v))]
      other) 3) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["StagedCekHaltAtZeroFuel"]
  (fun v : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA (.Halt v) 0) ===>
  (fun v : CekValue => State.Halt v)

#testOptimize ["StagedCekErrorAtZeroFuel"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA .Error 0) ===> State.Error

#testOptimize ["StagedCekApplyNonFunction"]
  (fun c : Const => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue (.VCon c)] (.VCon .Unit)) 3) ===>
  (fun _ : Const => State.Error)

#testOptimize ["StagedCekWrongForceTag"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.ForceFrame] (.VBuiltin .AddInteger [] (.One .ArgV))) 3) ===>
  State.Error

#testOptimize ["StagedCekConstructorFallback"] (norm-result: 1)
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Constr 0 [])) 2) ===>
  State.Halt (.VConstr 0 [])

#testOptimize ["StagedCekApplication"]
  (fun c : Const => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Apply (.Lam "x" (.Var "x")) (.Const c))) 7) ===>
  (fun c : Const => State.Halt (.VCon c))

#testOptimize ["StagedCekApplicationExhaustion"]
  (fun c : Const => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Apply (.Lam "x" (.Var "x")) (.Const c))) 6) ===>
  (fun _ : Const => State.Error)

end CardanoStagedControl
