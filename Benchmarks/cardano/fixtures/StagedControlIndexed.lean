import PlutusCore.UPLC
import Tests.Benchmarks.OptimizeTestUtils

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins PlutusCore.UPLC.Term

namespace CardanoStagedControlIndexed
set_option maxHeartbeats 0

attribute [local blaster_specialize 2] PlutusCore.UPLC.StagedCek.eval PlutusCore.UPLC.StagedCek.ret
attribute [local blaster_specialize 1] PlutusCore.UPLC.StagedCek.lookupValue

#testOptimize ["StagedCekShadowing"]
  (fun v discarded : CekValue =>
    PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
      (.Eval [] [v, discarded]
        (.Var 0)) 2) ===>
  (fun v _ : CekValue => State.Halt v)

#testOptimize ["StagedCekMissingName"]
  (fun v : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [v] (.Var 1)) 2) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StagedCekLookupFuel"]
  (fun v : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [v] (.Var 0)) 1) ===>
  (fun _ : CekValue => State.Error)

#testOptimize ["StagedCekCapturedEnvironment"]
  (fun v other : CekValue => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.RightApplicationOfValue
      (.VLam "argument" (.Var 1) [v])]
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

#testOptimize ["StagedCekConstructor"] (norm-result: 1)
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [] (.Constr 0 [])) 2) ===>
  State.Halt (.VConstr 0 [])

#testOptimize ["StagedCekApplication"]
  (fun c : Const => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [] (.Apply (.Lam "x" (.Var 0)) (.Const c))) 7) ===>
  (fun c : Const => State.Halt (.VCon c))

#testOptimize ["StagedCekApplicationExhaustion"]
  (fun c : Const => PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [] (.Apply (.Lam "x" (.Var 0)) (.Const c))) 6) ===>
  (fun _ : Const => State.Error)

#testOptimize ["StagedCekConstructorFieldOrder"] (norm-result: 1)
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.ConstructorArgument 0 [.VCon (.Integer 1)] [] []] (.VCon (.Integer 2))) 2) ===>
  State.Halt (.VConstr 0 [.VCon (.Integer 1), .VCon (.Integer 2)])

#testOptimize ["StagedCekCaseApplicationOrder"] (norm-result: 1)
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Eval [] [] (.Case (.Constr 0 [.Const (.Integer 7), .Const (.Integer 9)])
      [.Lam "a" (.Lam "b" (.Var 1))])) 20) ===>
  State.Halt (.VCon (.Integer 7))

#testOptimize ["StagedCekCaseOutOfBounds"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] []] (.VConstr 1 [])) 4) ===> State.Error

#testOptimize ["StagedCekPrimitiveCase"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] []] (.VCon (.Bool false))) 3) ===>
  State.Halt (.VCon .Unit)

#testOptimize ["StagedCekPrimitiveCaseArity"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] []] (.VCon (.Bool true))) 3) ===> State.Error

#testOptimize ["StagedCekNegativeCaseIndex"]
  (PlutusCore.UPLC.StagedCek.run .defaultFunSemanticsVariantA
    (.Return [Frame.CaseScrutinee [.Const .Unit] []] (.VCon (.Integer (-1)))) 3) ===> State.Error

end CardanoStagedControlIndexed
