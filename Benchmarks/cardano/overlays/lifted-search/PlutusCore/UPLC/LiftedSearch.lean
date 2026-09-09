import PlutusCore.UPLC.CekBlocks
open PlutusCore.UPLC PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins PlutusCore.Data PlutusCore.Default
namespace PlutusCore.UPLC.LiftedSearch
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def originalBody : Term := (.Force (.Apply (.Apply (.Apply (.Var "dbi_3") (.Var "dbi_23")) (.Delay (.Const (.Data (.Constr 1 []))))) (.Delay (.Apply (.Lam "dbi_24" (.Apply (.Lam "dbi_25" (.Apply (.Lam "dbi_26" (.Apply (.Lam "dbi_27" (.Force (.Apply (.Apply (.Apply (.Var "dbi_6") (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.EqualsByteString) (.Const (.ByteString { data := "" }))) (.Var "dbi_26"))) (.Delay (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.ConstrData) (.Const (.Integer 0))) (.Apply (.Apply (.Var "dbi_2") (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.IData) (.Var "dbi_27"))) (.Const (.ConstDataList [])))))) (.Delay (.Apply (.Apply (.Var "dbi_22") (.Var "dbi_22")) (.Var "dbi_25")))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnIData) (.Apply (.Var "dbi_4") (.Var "dbi_24"))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnBData) (.Apply (.Var "dbi_5") (.Var "dbi_24"))))) (.Apply (.Var "dbi_0") (.Var "dbi_23")))) (.Apply (.Var "dbi_1") (.Var "dbi_23"))))))
def originalSelf : Term := .Lam "dbi_22" (.Lam "dbi_23" originalBody)
def v0 : CekValue := .VBuiltin .TailList [] (.One .ArgV)
def v1 : CekValue := .VBuiltin .HeadList [] (.One .ArgV)
def v2 : CekValue := .VBuiltin .MkCons [] (.More .ArgV (.One .ArgV))
def v3 : CekValue := .VBuiltin .ChooseList [] (.More .ArgV (.More .ArgV (.One .ArgV)))
def v4 : CekValue := .VBuiltin .SndPair [] (.One .ArgV)
def v5 : CekValue := .VBuiltin .FstPair [] (.One .ArgV)
def v6 : CekValue := .VBuiltin .IfThenElse [] (.More .ArgV (.More .ArgV (.One .ArgV)))

structure Valid (env : Environment) : Prop where
  bound0 : ∀ s, ifBoundOtherwiseError s env "dbi_0" = .Return s v0
  bound1 : ∀ s, ifBoundOtherwiseError s env "dbi_1" = .Return s v1
  bound2 : ∀ s, ifBoundOtherwiseError s env "dbi_2" = .Return s v2
  bound3 : ∀ s, ifBoundOtherwiseError s env "dbi_3" = .Return s v3
  bound4 : ∀ s, ifBoundOtherwiseError s env "dbi_4" = .Return s v4
  bound5 : ∀ s, ifBoundOtherwiseError s env "dbi_5" = .Return s v5
  bound6 : ∀ s, ifBoundOtherwiseError s env "dbi_6" = .Return s v6

structure Ready (env : Environment) where
  captured : Environment
  currentValid : Valid env
  capturedValid : Valid captured
  recursiveBinding : ∀ s, ifBoundOtherwiseError s env "dbi_22" =
    .Return s (.VLam "dbi_22" (.Lam "dbi_23" originalBody) captured)

def recurEnv (captured : Environment) : Environment :=
  .NonEmptyEnvironment captured "dbi_22" (.VLam "dbi_22" (.Lam "dbi_23" originalBody) captured)

def recurReady (captured : Environment) (valid : Valid captured) : Ready (recurEnv captured) where
  captured := captured
  capturedValid := valid
  currentValid := by
    constructor
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound0]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound1]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound2]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound3]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound4]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound5]
    · intro s; simp [recurEnv, ifBoundOtherwiseError, valid.bound6]
  recursiveBinding := by intro s; simp [recurEnv, ifBoundOtherwiseError]

def entry (env : Environment) (s : Stack) (xs : List (Data × Data)) : State :=
  .Eval s (.NonEmptyEnvironment env "dbi_23" (.VCon (.ConstPairDataList xs))) originalBody

/-- Consume the entire search, returning the original remaining CEK fuel. -/
def scan (fuel : Nat) (xs : List (Data × Data)) : Option (Nat × Data) :=
  match xs with
  | [] => if 16 ≤ fuel then some (fuel-16, .Constr 1 []) else none
  | (.B b, .I i) :: tail =>
    if "" == b.data then
      if 103 ≤ fuel then some (fuel-103, .Constr 0 [.I i]) else none
    else
      if 92 ≤ fuel then scan (fuel-92) tail else none
  | _ => none
termination_by xs.length

theorem scan_fuel_lt (xs : List (Data × Data)) (fuel remaining : Nat) (result : Data)
    (h : scan fuel xs = some (remaining,result)) : remaining < fuel := by
  induction xs generalizing fuel with
  | nil => simp only [scan] at h; split at h <;> simp_all; omega
  | cons pair tail ih =>
    rcases pair with ⟨key,value⟩
    cases key <;> cases value <;> simp only [scan] at h <;> try contradiction
    split at h
    · split at h <;> simp_all; omega
    · split at h
      · have lt := ih _ h; omega
      · contradiction

end PlutusCore.UPLC.LiftedSearch
