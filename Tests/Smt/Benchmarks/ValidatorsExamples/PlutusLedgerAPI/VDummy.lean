
namespace Tests.ValidatorsExamples.PlutusLedgerAPI

structure POSIXTime where
    time : Nat
deriving Repr, Inhabited, BEq, Ord

structure VerificationKeyHash where
    hash : Nat
deriving Repr, BEq

inductive Purpose
| Minting
| Spending
| Rewarding
| Certifying
| Voting
| Proposing
deriving Repr, BEq

structure ValidityRange where
    upper_bound : Nat
    lower_bound : Nat
deriving Repr, BEq

structure Tx where
    values : List Nat
    signatories : List VerificationKeyHash
    validity_range : ValidityRange
deriving Repr, BEq

structure ScriptContext where
    purpose : Purpose
    transaction : Tx

end Tests.ValidatorsExamples.PlutusLedgerAPI
