import WSC.Prep.GlobalImport
import WSC.Goldens.TermsCheck

set_option maxHeartbeats 0
namespace WSC.Benchmark.Acceptance

open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.CekMachine
open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open CardanoLedgerApi.IsData.Class (IsData)
open WSC.Goldens.Terms

/-- These are the existing post-#112 goldens, not synthetic accepting programs.
`TermsCheck` checks their literals against the original serialized payloads.
-/
def decodeInputs (params : List Data) (ctx : Data) : Option (CurrencySymbol × ScriptContext) := do
  let [param] := params | none
  return (← IsData.fromData param, ← IsData.fromData ctx)

def nonmemberData := programmableLogicGlobal_transfer_nonmember_covering_node_ctx
def nonmemberParams := programmableLogicGlobal_transfer_nonmember_covering_node_params
def nonmember := decodeInputs nonmemberParams nonmemberData

-- Failed decoding is a build failure, never a substituted default context.
theorem nonmember_decodes : nonmember.isSome = true := by native_decide
def nonmemberCS : CurrencySymbol := (nonmember.get nonmember_decodes).1
def nonmemberCtx : ScriptContext := (nonmember.get nonmember_decodes).2

def encodedData (inputs : List Term) : Option (List Data) := inputs.mapM fun t =>
  match t with
  | .Const (.Data d) => some d
  | _ => none

def exactInputs (params : List Data) (ctx : Data) : Bool :=
  match decodeInputs params ctx with
  | none => false
  | some (cs, context) =>
      encodedData (globalInputs1600 cs context) == some (params ++ [ctx])

inductive Outcome | unit | error | exhausted | otherHalt
deriving BEq, Repr, DecidableEq

def outcome : State → Outcome
  | .Halt (.VCon .Unit) => .unit
  | .Halt _ => .otherHalt
  | .Error => .error
  | _ => .exhausted

/-- Exhaustion is distinct from an actual CEK error. Count the real `step`
transitions without invoking `runSteps`' fuel-exhaustion-to-error conversion.
-/
def measure (s0 : State) (limit : Nat) : Nat × Outcome := Id.run do
  let mut s := s0
  let mut steps := 0
  for _ in [0:limit] do
    match s with
    | .Halt _ | .Error => return (steps, outcome s)
    | _ =>
      s := step default s
      steps := steps + 1
  return (steps, outcome s)

def start (params : List Data) (ctx : Data) : State :=
  match programmableLogicGlobal1600.script with
  | .Program _ body => initialState (applyParams body ((params ++ [ctx]).map (Term.Const ∘ .Data)))

def exec (fuel : Nat) : State := cekExecuteProgram programmableLogicGlobal1600.script
  (globalInputs1600 nonmemberCS nonmemberCtx) fuel

def checkGolden (params : List Data) (ctx : Data) (k : Nat) (expected : Outcome) : Bool :=
  let s := start params ctx
  exactInputs params ctx &&
  measure s (10 * k) == (k, expected) &&
  measure s (k - 1) == (k - 1, .exhausted) &&
  outcome (runSteps default s k) == expected &&
  outcome (runSteps default s (10 * k)) == expected &&
  outcome (runSteps default s (k - 1)) == .error

-- Executable validation through native_decide; this is a compiler-backed
-- regression gate, not a kernel-reduced equivalence certificate for the optimizer.
example : checkGolden nonmemberParams nonmemberData 1453 .unit = true := by native_decide
example : checkGolden programmableLogicGlobal_transfer_member_single_policy_params
    programmableLogicGlobal_transfer_member_single_policy_ctx 2782 .unit = true := by native_decide
example : checkGolden programmableLogicGlobal_transfer_mixed_many_policies_params
    programmableLogicGlobal_transfer_mixed_many_policies_ctx 3441 .unit = true := by native_decide
example : checkGolden programmableLogicGlobal_transfer_containment_violation_REJECT_params
    programmableLogicGlobal_transfer_containment_violation_REJECT_ctx 2370 .error = true := by native_decide

example : outcome (exec 1452) = .error ∧ outcome (exec 1453) = .unit ∧
    outcome (exec 1600) = .unit := by native_decide

#eval do
  IO.println "CARDANO_ACCEPTANCE nonmember_k=1453 member_k=2782 mixed_k=3441 rejection_k=2370 roundtrip=true unit_halts=true"

end WSC.Benchmark.Acceptance
