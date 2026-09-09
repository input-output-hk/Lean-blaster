import Tests.Utils
namespace Tests.Issue245
structure Plan (n : Nat) where
  worker : Nat → Nat

def recognize (n : Nat) : Option (Plan n) :=
  match n with
  | 0 => some { worker := fun x => x+1 }
  | _ => none

def run (fuel n x : Nat) : Nat :=
  match fuel with
  | 0 => x
  | fuel+1 =>
    match recognize n with
    | none => x
    | some plan =>
      let remaining := plan.worker fuel
      if h : remaining < fuel then run remaining n x else x+1
termination_by fuel

example (x : Nat) : run 3 1 x = x := by simp [run, recognize]
attribute [local blaster_specialize 1] run
#testOptimize ["IndexedPlanFallback"] (fun x : Nat => run 3 1 x) ===> (fun x : Nat => x)

#testOptimize ["IndexedPlanSelected"] (norm-result: 1)
  (fun x : Nat => run 3 0 x) ===> (fun x : Nat => Nat.add 1 x)

#testOptimize ["IndexedPlanSymbolicFallback"]
  (fun n x : Nat => run 3 (n + 1) x) ===> (fun _ x : Nat => x)

def witness (n : Nat) : Option (PLift (n = 0)) :=
  match n with
  | 0 => some ⟨rfl⟩
  | _ => none

def hasWitness (n : Nat) : Bool := (witness n).isSome

#testOptimize ["IndexedProofSelected"] hasWitness 0 ===> true
#testOptimize ["IndexedProofFallback"] hasWitness 1 ===> false
end Tests.Issue245
