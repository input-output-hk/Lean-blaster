import PlutusCore.UPLC.LiftedMapSearchProofs
import PlutusCore.UPLC.SpecializedCall
open PlutusCore.UPLC PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins PlutusCore.Data
namespace PlutusCore.UPLC.LiftedMapSearch
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Recognize this exact template and retain a kernel-checked equality witness.
The prototype deliberately falls back for other alpha-renamings. -/
def bodyWitness (t : Term) : Option (PLift (t = originalBody)) :=
  match t with
  | (.Force (.Apply (.Apply (.Apply (.Var "dbi_3") (.Var "dbi_20")) (.Delay (.Const (.Data (.Constr 1 []))))) (.Delay (.Apply (.Lam "dbi_21" (.Apply (.Lam "dbi_22" (.Apply (.Lam "dbi_23" (.Apply (.Lam "dbi_24" (.Force (.Apply (.Apply (.Apply (.Var "dbi_6") (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.EqualsByteString) (.Const (.ByteString { data := "" }))) (.Var "dbi_23"))) (.Delay (.Apply (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.ConstrData) (.Const (.Integer 0))) (.Apply (.Apply (.Var "dbi_2") (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.MapData) (.Var "dbi_24"))) (.Const (.ConstDataList [])))))) (.Delay (.Apply (.Apply (.Var "dbi_19") (.Var "dbi_19")) (.Var "dbi_22")))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnMapData) (.Apply (.Var "dbi_4") (.Var "dbi_21"))))) (.Apply (.Builtin PlutusCore.UPLC.Term.BuiltinFun.UnBData) (.Apply (.Var "dbi_5") (.Var "dbi_21"))))) (.Apply (.Var "dbi_0") (.Var "dbi_20")))) (.Apply (.Var "dbi_1") (.Var "dbi_20")))))) => some ⟨rfl⟩
  | _ => none

theorem lookup_step (env : Environment) (x : String) (v : CekValue)
    (h : StagedCek.lookupValue env x = some v) (s : Stack) :
    ifBoundOtherwiseError s env x = .Return s v := by
  cases env with
  | EmptyEnvironment => simp [StagedCek.lookupValue] at h
  | NonEmptyEnvironment rest y value =>
      by_cases eq : x = y
      · simpa [StagedCek.lookupValue, ifBoundOtherwiseError, eq] using h
      · simp only [StagedCek.lookupValue, eq, if_false] at h
        simpa only [ifBoundOtherwiseError, eq, if_false] using lookup_step rest x v h s
termination_by sizeOf env

/-- Certificates are proof-only; unused captured environments are not copied into
runtime scan results. Each lookup obeys the original shadowing rules. -/
def bindingsWitness (env : Environment) : Option (PLift (Valid env)) :=
  match h0 : StagedCek.lookupValue env "dbi_0" with
  | some (.VBuiltin .TailList [] (.One .ArgV)) =>
    match h1 : StagedCek.lookupValue env "dbi_1" with
    | some (.VBuiltin .HeadList [] (.One .ArgV)) =>
      match h2 : StagedCek.lookupValue env "dbi_2" with
      | some (.VBuiltin .MkCons [] (.More .ArgV (.One .ArgV))) =>
        match h3 : StagedCek.lookupValue env "dbi_3" with
        | some (.VBuiltin .ChooseList [] (.More .ArgV (.More .ArgV (.One .ArgV)))) =>
          match h4 : StagedCek.lookupValue env "dbi_4" with
          | some (.VBuiltin .SndPair [] (.One .ArgV)) =>
            match h5 : StagedCek.lookupValue env "dbi_5" with
            | some (.VBuiltin .FstPair [] (.One .ArgV)) =>
              match h6 : StagedCek.lookupValue env "dbi_6" with
              | some (.VBuiltin .IfThenElse [] (.More .ArgV (.More .ArgV (.One .ArgV)))) =>
                some ⟨{
                  bound0 := lookup_step env "dbi_0" v0 h0
                  bound1 := lookup_step env "dbi_1" v1 h1
                  bound2 := lookup_step env "dbi_2" v2 h2
                  bound3 := lookup_step env "dbi_3" v3 h3
                  bound4 := lookup_step env "dbi_4" v4 h4
                  bound5 := lookup_step env "dbi_5" v5 h5
                  bound6 := lookup_step env "dbi_6" v6 h6
                }⟩
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

def readyWitness (env : Environment) : Option (PLift (Nonempty (Ready env))) :=
  match hs : StagedCek.lookupValue env "dbi_19" with
  | some (.VLam "dbi_19" (.Lam "dbi_20" body) captured) =>
    match bodyWitness body, bindingsWitness env, bindingsWitness captured with
    | some bodyEq, some currentValid, some capturedValid =>
      some ⟨⟨{
        captured := captured
        currentValid := currentValid.down
        capturedValid := capturedValid.down
        recursiveBinding := by
          intro s
          have hit := lookup_step env "dbi_19" _ hs s
          simpa only [bodyEq.down] using hit
      }⟩⟩
    | _, _, _ => none
  | _ => none

def worker (xs : List (Data × Data)) (_sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (fuel : Nat) : Option (Nat × CekValue) :=
  match scan fuel xs with
  | none => none
  | some (remaining,d) => some (remaining, .VCon (.Data d))

def recognizeCall (binder : String) (body : Term) (env : Environment) (arg : CekValue) :
    Option (SpecializedCall binder body env arg) :=
  match binder, arg with
  | "dbi_20", .VCon (.ConstPairDataList xs) =>
    match bodyWitness body, readyWitness env with
    | some bodyEq, some envReady =>
      some {
        worker := worker xs
        spends := by
          intro sv fuel remaining result h
          unfold worker at h
          cases eq : scan fuel xs with
          | none => simp [eq] at h
          | some pair =>
            rcases pair with ⟨rest,d⟩
            simp only [eq, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl,rfl⟩
            exact scan_fuel_lt xs fuel rest d eq
        correct := by
          intro sv fuel s
          rcases envReady.down with ⟨ready⟩
          rw [bodyEq.down]
          have correct := scan_correct sv xs env ready fuel s
          cases eq : scan fuel xs with
          | none => simpa only [worker, finish, entry, eq] using correct
          | some pair =>
            rcases pair with ⟨remaining,d⟩
            simpa only [worker, finish, entry, eq] using correct
      }
    | _, _ => none
  | _, _ => none

#print axioms recognizeCall

#print axioms bodyWitness
#print axioms readyWitness
end PlutusCore.UPLC.LiftedMapSearch
