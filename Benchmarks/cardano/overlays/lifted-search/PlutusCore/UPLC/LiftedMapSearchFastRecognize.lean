import PlutusCore.UPLC.LiftedMapSearchRecognize
import PlutusCore.UPLC.LiftedSearchFastRecognize
open PlutusCore.UPLC PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins PlutusCore.Data
namespace PlutusCore.UPLC.LiftedMapSearch
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Runtime recognition uses ordinary booleans and a nonindexed worker record.
The correspondence with the proof-carrying recognizer is established below,
so preparation need not normalize types indexed by the full closure environment. -/

def bodyMatches (t : Term) : Bool := (bodyWitness t).isSome

theorem bodyMatches_eq (t : Term) : bodyMatches t = (bodyWitness t).isSome := rfl

def bindingsMatch (env : Environment) : Bool :=
  match StagedCek.lookupValue env "dbi_0" with
  | some (.VBuiltin .TailList [] (.One .ArgV)) =>
    match StagedCek.lookupValue env "dbi_1" with
    | some (.VBuiltin .HeadList [] (.One .ArgV)) =>
      match StagedCek.lookupValue env "dbi_2" with
      | some (.VBuiltin .MkCons [] (.More .ArgV (.One .ArgV))) =>
        match StagedCek.lookupValue env "dbi_3" with
        | some (.VBuiltin .ChooseList [] (.More .ArgV (.More .ArgV (.One .ArgV)))) =>
          match StagedCek.lookupValue env "dbi_4" with
          | some (.VBuiltin .SndPair [] (.One .ArgV)) =>
            match StagedCek.lookupValue env "dbi_5" with
            | some (.VBuiltin .FstPair [] (.One .ArgV)) =>
              match StagedCek.lookupValue env "dbi_6" with
              | some (.VBuiltin .IfThenElse [] (.More .ArgV (.More .ArgV (.One .ArgV)))) => true
              | _ => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem bindingsMatch_eq (env : Environment) : bindingsMatch env = (bindingsWitness env).isSome := by
  unfold bindingsMatch bindingsWitness
  repeat' first | rfl | (solve | simp_all) | (split <;> try simp_all)

def readyMatch (env : Environment) : Bool :=
  match StagedCek.lookupValue env "dbi_19" with
  | some (.VLam "dbi_19" (.Lam "dbi_20" body) captured) =>
      bodyMatches body && bindingsMatch env && bindingsMatch captured
  | _ => false

theorem readyMatch_eq (env : Environment) : readyMatch env = (readyWitness env).isSome := by
  unfold readyMatch readyWitness
  simp only [bodyMatches_eq, bindingsMatch_eq]
  repeat' first | rfl | (solve | simp_all) | (split <;> try simp_all)
  all_goals
    obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
    simp_all [Option.isSome_iff_exists]
  all_goals
    intro b hb c hc
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro d hd
    solve_by_elim

abbrev CallPlan := LiftedSearch.CallPlan

def recognizeFast (binder : String) (body : Term) (env : Environment) (arg : CekValue) : Option CallPlan :=
  match binder, arg with
  | "dbi_20", .VCon (.ConstPairDataList xs) =>
      if bodyMatches body && readyMatch env then some ⟨worker xs⟩ else none
  | _, _ => none

theorem recognizeFast_eq (binder : String) (body : Term) (env : Environment) (arg : CekValue) :
    recognizeFast binder body env arg =
      (recognizeCall binder body env arg).map (fun p => LiftedSearch.CallPlan.mk p.worker) := by
  unfold recognizeFast recognizeCall
  split
  · simp only [bodyMatches_eq, readyMatch_eq]
    cases bodyWitness body <;> cases readyWitness env <;> rfl
  · split <;> simp_all

theorem recognizeFast_sound (binder : String) (body : Term) (env : Environment) (arg : CekValue)
    (plan : CallPlan) (h : recognizeFast binder body env arg = some plan) :
    ∃ cert : SpecializedCall binder body env arg, cert.worker = plan.worker := by
  rw [recognizeFast_eq] at h
  cases hc : recognizeCall binder body env arg with
  | none => simp [hc] at h
  | some cert =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      cases h
      exact ⟨cert, rfl⟩

#print axioms recognizeFast_sound
end PlutusCore.UPLC.LiftedMapSearch
