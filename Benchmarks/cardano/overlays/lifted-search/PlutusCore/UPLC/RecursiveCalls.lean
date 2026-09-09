import PlutusCore.UPLC.LiftedMapSearchFastRecognize

namespace PlutusCore.UPLC.RecursiveCalls
open Term CekMachine CekValue

/-- Select a certified recursive-body worker. Binder names only route the
check; each candidate still verifies its full body and captured bindings. -/
def recognize (binder : String) (body : Term) (env : Environment) (arg : CekValue) :
    Option LiftedSearch.CallPlan :=
  if binder = "dbi_23" then LiftedSearch.recognizeFast binder body env arg
  else if binder = "dbi_20" then LiftedMapSearch.recognizeFast binder body env arg
  else none

theorem recognize_sound (binder : String) (body : Term) (env : Environment) (arg : CekValue)
    (plan : LiftedSearch.CallPlan) (h : recognize binder body env arg = some plan) :
    ∃ cert : SpecializedCall binder body env arg, cert.worker = plan.worker := by
  simp only [recognize] at h
  split at h
  · exact LiftedSearch.recognizeFast_sound binder body env arg plan h
  · split at h
    · exact LiftedMapSearch.recognizeFast_sound binder body env arg plan h
    · contradiction

#print axioms recognize_sound
end PlutusCore.UPLC.RecursiveCalls
