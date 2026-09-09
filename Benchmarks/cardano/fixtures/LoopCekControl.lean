import PlutusCore.UPLC
import Tests.Benchmarks.OptimizeTestUtils

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins PlutusCore.UPLC.Term

namespace CardanoLoopCekControl
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

attribute [local blaster_specialize 2] PlutusCore.UPLC.LoopCek.eval PlutusCore.UPLC.LoopCek.ret
attribute [local blaster_specialize 1] PlutusCore.UPLC.LoopCek.lookupValue

open PlutusCore.UPLC
attribute [local blaster_specialize 1] StagedCek.lookupValue
attribute [local blaster_specialize 2] LiftedSearch.recognizeCall
attribute [local blaster_specialize 1] LiftedSearch.bodyWitness LiftedSearch.readyWitness LiftedSearch.bindingsWitness LiftedSearch.scan
attribute [local blaster_specialize 3] LiftedSearch.worker
attribute [local blaster_specialize 2] LiftedSearch.recognizeFast
attribute [local blaster_specialize 1] LiftedSearch.bodyMatches LiftedSearch.readyMatch LiftedSearch.bindingsMatch
attribute [local blaster_specialize 2] RecursiveCalls.recognize LiftedMapSearch.recognizeFast
attribute [local blaster_specialize 1] LiftedMapSearch.bodyWitness LiftedMapSearch.bodyMatches LiftedMapSearch.readyMatch LiftedMapSearch.bindingsMatch LiftedMapSearch.scan
attribute [local blaster_specialize 3] LiftedMapSearch.worker

#testOptimize ["LoopCekShadowing"]
  (fun v discarded : CekValue =>
    PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
      (.Eval [] (.NonEmptyEnvironment (.NonEmptyEnvironment .EmptyEnvironment "x" discarded) "x" v)
        (.Var "x")) 2) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["LoopCekMissingName"]
  (fun v : CekValue => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "other" v) (.Var "x")) 2) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["LoopCekLookupFuel"]
  (fun v : CekValue => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] (.NonEmptyEnvironment .EmptyEnvironment "x" v) (.Var "x")) 1) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["LoopCekCapturedEnvironment"]
  (fun v other : CekValue => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue
      (.VLam "argument" (.Var "captured") (.NonEmptyEnvironment .EmptyEnvironment "captured" v))]
      other) 3) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["LoopCekHaltAtZeroFuel"]
  (fun v : CekValue => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA (.Halt v) 0) ===>
  (fun v : CekValue => State.Halt v)

#testOptimize ["LoopCekErrorAtZeroFuel"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA .Error 0) ===> State.Error

#testOptimize ["LoopCekApplyNonFunction"]
  (fun c : Const => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue (.VCon c)] (.VCon .Unit)) 3) ===>
  (fun _ : Const => State.Error)

#testOptimize ["LoopCekWrongForceTag"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.ForceFrame] (.VBuiltin .AddInteger [] (.One .ArgV))) 3) ===>
  State.Error

#testOptimize ["LoopCekConstructor"] (norm-result: 1)
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Constr 0 [])) 2) ===>
  State.Halt (.VConstr 0 [])

#testOptimize ["LoopCekApplication"]
  (fun c : Const => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Apply (.Lam "x" (.Var "x")) (.Const c))) 7) ===>
  (fun c : Const => State.Halt (.VCon c))

#testOptimize ["LoopCekApplicationExhaustion"]
  (fun c : Const => PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Apply (.Lam "x" (.Var "x")) (.Const c))) 6) ===>
  (fun _ : Const => State.Error)

#testOptimize ["LoopCekConstructorFieldOrder"] (norm-result: 1)
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.ConstructorArgument 0 [.VCon (.Integer 1)] [] .EmptyEnvironment] (.VCon (.Integer 2))) 2) ===>
  State.Halt (.VConstr 0 [.VCon (.Integer 1), .VCon (.Integer 2)])

#testOptimize ["LoopCekCaseApplicationOrder"] (norm-result: 1)
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Eval [] .EmptyEnvironment (.Case (.Constr 0 [.Const (.Integer 7), .Const (.Integer 9)])
      [.Lam "a" (.Lam "b" (.Var "a"))])) 20) ===>
  State.Halt (.VCon (.Integer 7))

#testOptimize ["LoopCekCaseOutOfBounds"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] .EmptyEnvironment] (.VConstr 1 [])) 4) ===> State.Error

#testOptimize ["LoopCekPrimitiveCase"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] .EmptyEnvironment] (.VCon (.Bool false))) 3) ===>
  State.Halt (.VCon .Unit)

#testOptimize ["LoopCekPrimitiveCaseArity"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] .EmptyEnvironment] (.VCon (.Bool true))) 3) ===> State.Error

#testOptimize ["LoopCekNegativeCaseIndex"]
  (PlutusCore.UPLC.LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] .EmptyEnvironment] (.VCon (.Integer (-1)))) 3) ===> State.Error

open PlutusCore.UPLC

def base : Environment :=
  let e := Environment.EmptyEnvironment
  let e := Environment.NonEmptyEnvironment e "dbi_0" (.VBuiltin .TailList [] (.One .ArgV))
  let e := Environment.NonEmptyEnvironment e "dbi_1" (.VBuiltin .HeadList [] (.One .ArgV))
  let e := Environment.NonEmptyEnvironment e "dbi_2" (.VBuiltin .MkCons [] (.More .ArgV (.One .ArgV)))
  let e := Environment.NonEmptyEnvironment e "dbi_3" (.VBuiltin .ChooseList [] (.More .ArgV (.More .ArgV (.One .ArgV))))
  let e := Environment.NonEmptyEnvironment e "dbi_4" (.VBuiltin .SndPair [] (.One .ArgV))
  let e := Environment.NonEmptyEnvironment e "dbi_5" (.VBuiltin .FstPair [] (.One .ArgV))
  Environment.NonEmptyEnvironment e "dbi_6" (.VBuiltin .IfThenElse [] (.More .ArgV (.More .ArgV (.One .ArgV))))

def call (captured : Environment) (xs : List (PlutusCore.Data.Data × PlutusCore.Data.Data)) : State :=
  .Return [Frame.RightApplicationOfValue
    (.VLam "dbi_23" LiftedSearch.originalBody (LiftedSearch.recurEnv captured))] (.VCon (.ConstPairDataList xs))

#testOptimize ["LoopCekRecognizesUnusedCapture"]
  (fun unused : CekValue => (LiftedSearch.readyWitness
    (LiftedSearch.recurEnv (.NonEmptyEnvironment base "unused" unused))).isSome) ===>
  (fun _ : CekValue => true)

#testOptimize ["LoopCekRejectsShadowedBuiltin"]
  (LiftedSearch.readyWitness (.NonEmptyEnvironment (LiftedSearch.recurEnv base) "dbi_0" (.VCon .Unit))).isSome ===> false

#testOptimize ["LoopCekLiftedHit"] (norm-result: 1)
  (fun i : Int => LoopCek.run .defaultFunSemanticsVariantA (call base [(.B {data := ""}, .I i)]) 105) ===>
  (fun i : Int => State.Halt (.VCon (.Data (.Constr 0 [.I i]))))

#testOptimize ["LoopCekLiftedHitFuel"]
  (fun i : Int => LoopCek.run .defaultFunSemanticsVariantA (call base [(.B {data := ""}, .I i)]) 104) ===>
  (fun _ : Int => State.Error)

#testOptimize ["LoopCekLiftedRecursion"] (norm-result: 1)
  (fun i : Int => LoopCek.run .defaultFunSemanticsVariantA
    (call base [(.B {data := "x"}, .I 0), (.B {data := ""}, .I i)]) 197) ===>
  (fun i : Int => State.Halt (.VCon (.Data (.Constr 0 [.I i]))))

#testOptimize ["LoopCekLiftedRecursiveFuel"]
  (fun i : Int => LoopCek.run .defaultFunSemanticsVariantA
    (call base [(.B {data := "x"}, .I 0), (.B {data := ""}, .I i)]) 196) ===>
  (fun _ : Int => State.Error)

#testOptimize ["LoopCekLiftedMalformedUnmatchedPayload"]
  (LoopCek.run .defaultFunSemanticsVariantA
    (call base [(.B {data := "x"}, .List []), (.B {data := ""}, .I 42)]) 1000) ===> State.Error

#testOptimize ["LoopCekFallbackPreservesUnusedBadBinding"] (norm-result: 1)
  (LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue (.VLam "dbi_23" LiftedSearch.originalBody
      (.NonEmptyEnvironment (LiftedSearch.recurEnv base) "dbi_0" (.VCon .Unit)))] (.VCon (.ConstPairDataList []))) 18) ===>
  State.Halt (.VCon (.Data (.Constr 1 [])))

def changedBody : Term := (.Force (.Apply (.Apply (.Apply (.Var "dbi_3") (.Var "dbi_23")) (.Delay (.Const (.Data (.Constr 1 []))))) (.Delay (.Apply (.Lam "dbi_24" (.Apply (.Lam "dbi_25" (.Apply (.Lam "dbi_26" (.Apply (.Lam "dbi_27" (.Force (.Apply (.Apply (.Apply (.Var "dbi_6") (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.EqualsByteString) (.Const (.ByteString { data := "x" }))) (.Var "dbi_26"))) (.Delay (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.ConstrData) (.Const (.Integer 0))) (.Apply (.Apply (.Var "dbi_2") (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.IData) (.Var "dbi_27"))) (.Const (.ConstDataList [])))))) (.Delay (.Apply (.Apply (.Var "dbi_22") (.Var "dbi_22")) (.Var "dbi_25")))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnIData) (.Apply (.Var "dbi_4") (.Var "dbi_24"))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnBData) (.Apply (.Var "dbi_5") (.Var "dbi_24"))))) (.Apply (.Var "dbi_0") (.Var "dbi_23")))) (.Apply (.Var "dbi_1") (.Var "dbi_23"))))))

#testOptimize ["LoopCekRejectsDifferentKeyTemplate"]
  (LiftedSearch.bodyWitness changedBody).isSome ===> false

#testOptimize ["LoopCekFallbackUsesChangedKey"] (norm-result: 1)
  (fun i : Int => LoopCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue (.VLam "dbi_23" changedBody (LiftedSearch.recurEnv base))]
      (.VCon (.ConstPairDataList [(.B {data := "x"}, .I i)]))) 105) ===>
  (fun i : Int => State.Halt (.VCon (.Data (.Constr 0 [.I i]))))


def mapCall (captured : Environment) (xs : List (PlutusCore.Data.Data × PlutusCore.Data.Data)) : State :=
  .Return [Frame.RightApplicationOfValue
    (.VLam "dbi_20" LiftedMapSearch.originalBody (LiftedMapSearch.recurEnv captured))] (.VCon (.ConstPairDataList xs))

#testOptimize ["LoopCekMapRecognizesUnusedCapture"]
  (fun unused : CekValue => LiftedMapSearch.readyMatch
    (LiftedMapSearch.recurEnv (.NonEmptyEnvironment base "unused" unused))) ===>
  (fun _ : CekValue => true)

#testOptimize ["LoopCekMapRejectsShadowedBuiltin"]
  LiftedMapSearch.readyMatch (.NonEmptyEnvironment (LiftedMapSearch.recurEnv base) "dbi_0" (.VCon .Unit)) ===> false

#testOptimize ["LoopCekMapHit"] (norm-result: 1)
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) =>
    LoopCek.run .defaultFunSemanticsVariantA (mapCall base [(.B {data := ""}, .Map payload)]) 105) ===>
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => State.Halt (.VCon (.Data (.Constr 0 [.Map payload]))))

#testOptimize ["LoopCekMapHitFuel"]
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) =>
    LoopCek.run .defaultFunSemanticsVariantA (mapCall base [(.B {data := ""}, .Map payload)]) 104) ===>
  (fun _ : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => State.Error)

#testOptimize ["LoopCekMapRecursion"] (norm-result: 1)
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => LoopCek.run .defaultFunSemanticsVariantA
    (mapCall base [(.B {data := "x"}, .Map []), (.B {data := ""}, .Map payload)]) 197) ===>
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => State.Halt (.VCon (.Data (.Constr 0 [.Map payload]))))

#testOptimize ["LoopCekMapRecursiveFuel"]
  (fun payload : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => LoopCek.run .defaultFunSemanticsVariantA
    (mapCall base [(.B {data := "x"}, .Map []), (.B {data := ""}, .Map payload)]) 196) ===>
  (fun _ : List (PlutusCore.Data.Data × PlutusCore.Data.Data) => State.Error)

#testOptimize ["LoopCekMapMalformedUnmatchedPayload"]
  (LoopCek.run .defaultFunSemanticsVariantA
    (mapCall base [(.B {data := "x"}, .I 0), (.B {data := ""}, .Map [])]) 1000) ===> State.Error

#testOptimize ["LoopCekMapMalformedKey"]
  (LoopCek.run .defaultFunSemanticsVariantA (mapCall base [(.I 0, .Map [])]) 1000) ===> State.Error

#testOptimize ["LoopCekMapEmpty"] (norm-result: 1)
  (LoopCek.run .defaultFunSemanticsVariantA (mapCall base []) 18) ===>
  State.Halt (.VCon (.Data (.Constr 1 [])))

#testOptimize ["LoopCekMapEmptyFuel"]
  (LoopCek.run .defaultFunSemanticsVariantA (mapCall base []) 17) ===> State.Error

end CardanoLoopCekControl
