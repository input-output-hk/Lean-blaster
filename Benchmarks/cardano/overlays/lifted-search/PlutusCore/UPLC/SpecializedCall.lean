import PlutusCore.UPLC.StagedCekProofs
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.Default
namespace PlutusCore.UPLC

/-- A verified specialization of a lambda body for one captured environment and
argument. Successful workers consume original CEK fuel and return the remaining
fuel. Their result is resumed with the existing continuation. -/
structure SpecializedCall (binder : String) (body : Term) (env : Environment) (arg : CekValue) where
  worker : BuiltinSemanticsVariant → Nat → Option (Nat × CekValue)
  spends : ∀ sv fuel remaining result, worker sv fuel = some (remaining,result) → remaining < fuel
  correct : ∀ sv fuel s,
    (match worker sv fuel with
      | none => State.Error
      | some (remaining,result) => runSteps sv (.Return s result) remaining) =
    runSteps sv (.Eval s (.NonEmptyEnvironment env binder arg) body) fuel

end PlutusCore.UPLC
