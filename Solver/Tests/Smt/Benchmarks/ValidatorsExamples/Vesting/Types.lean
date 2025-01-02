import Solver.Tests.Smt.Benchmarks.ValidatorsExamples.PlutusLedgerAPI.VDummy

open Tests.ValidatorsExamples.PlutusLedgerAPI

namespace Tests.ValidatorsExamples.Vesting

structure VestingDatum where
    lock_until : POSIXTime
    beneficiary : VerificationKeyHash
deriving Repr, BEq

structure VestingRedeemer where
    dummy : Nat
deriving Repr, BEq

-- Just to be able to quickly switch between different versions ("list bugged" and not bugged)
structure Demo where
    buggy : Bool
deriving Repr, BEq

end Tests.ValidatorsExamples.Vesting
