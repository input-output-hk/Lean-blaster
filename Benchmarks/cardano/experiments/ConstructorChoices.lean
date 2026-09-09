import Tests.Utils

set_option blaster.hoistConstructorChoices false

namespace Tests.ConstructorChoices

#testOptimize ["KeepChoiceInConstructor"] (norm-result: 1)
  (fun b : Bool => some (if b then (3 : Nat) else 4)) ===>
  (fun b : Bool => some (Blaster.dite' (true = b) (fun _ => 3) (fun _ => 4)))

#testOptimize ["ConsumeConstructorChoice"]
  (∀ b : Bool, (some (if b then (3 : Nat) else 4)).getD 5 = (if b then 3 else 4)) ===> True

#blaster (gen-cex: 0)
  [∀ b c : Bool, ((if b then (3 : Nat) else 4), (if c then (5 : Nat) else 6)).1 = (if b then 3 else 4)]

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b c : Bool, ((if b then (3 : Nat) else 4), (if c then (5 : Nat) else 6)).1 = 3]

end Tests.ConstructorChoices
