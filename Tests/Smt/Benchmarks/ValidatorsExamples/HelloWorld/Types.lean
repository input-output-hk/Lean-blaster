
namespace Tests.ValidatorsExamples.HelloWorld

structure HelloWorldDatum where
    datumMessage : String
deriving Repr, Inhabited, BEq

structure HelloWorldRedeemer where
    redeemerMessage : String
deriving Repr, BEq

end Tests.ValidatorsExamples.HelloWorld
