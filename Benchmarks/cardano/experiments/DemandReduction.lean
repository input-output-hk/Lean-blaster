import Tests.Utils
set_option blaster.reduceBeforeArguments true
namespace Tests.DemandReduction

def countdown : Nat → Nat
  | 0 => 0
  | n + 1 => countdown n

def ignore (_ : Nat) : Nat := 7

#testOptimize ["IgnoreUnusedComputation"] (norm-result: 1) (ignore (countdown 100000)) ===> (7 : Nat)
#testOptimize ["ProjectBeforeFields"]
  (fun x : Nat => ((x, countdown 100000) : Nat × Nat).1) ===> (fun x : Nat => x)
#testOptimize ["RecursiveCallStillReduces"] (norm-result: 1) (countdown 100) ===> (0 : Nat)
#testOptimize ["KeepChildFacts"]
  (∀ a b c : Prop, (a → b) ∧ (a → c ∧ (a → b))) ===>
  (∀ a b c : Prop, (a → b) ∧ (a → b ∧ c))
#blaster (gen-cex: 0) [∀ n : Nat, ignore n = 7]
#blaster (gen-cex: 0) (solve-result: 1) [∀ n : Nat, ignore n = n]
end Tests.DemandReduction
