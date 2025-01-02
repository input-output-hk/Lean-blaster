import Solver.Command.Syntax
import Solver.Tests.Utils
import Solver.Tests.Smt.Benchmarks.ValidatorsExamples.PlutusLedgerAPI.VDummy
import Solver.Tests.Smt.Benchmarks.ValidatorsExamples.HelloWorld.Types

open Tests.ValidatorsExamples.PlutusLedgerAPI

namespace Tests.ValidatorsExamples.HelloWorld

def HelloWorldValidator : HelloWorldDatum -> HelloWorldRedeemer -> ScriptContext -> Bool :=
    fun _datum redeemer _sc =>
        "Hello World!" == redeemer.redeemerMessage

theorem spec01_HelloWorld :
  ∀ (datum: HelloWorldDatum) (redeemer: HelloWorldRedeemer), (_c : ScriptContext) →
     HelloWorldValidator datum redeemer _c = true →
     "Hello World!" == redeemer.redeemerMessage := by sorry

#solve [spec01_HelloWorld]

end Tests.ValidatorsExamples.HelloWorld
