import Tests.Utils
import Tests.Optimize.Extension.ExtensionSameName.Defs

/-! First module annotating `len_nil`/`len_cons`, from the root namespace: the generated optimization
    functions are named `Test.ExtensionSameName.blaster_opt_len_nil` and
    `Test.ExtensionSameName.blaster_opt_len_cons` (the namespace of the theorems is below the current
    one), as explicit definitions `def Test.ExtensionSameName.blaster_opt_len_nil` would be. -/

open Test.ExtensionSameName

attribute [blaster] len_nil len_cons

example : Blaster.OptFn := Test.ExtensionSameName.blaster_opt_len_nil
example : Blaster.OptFn := blaster_opt_len_cons

#testOptimize [ "ExtSameNameModuleA_1" ] (norm-result: 1)
  ∀ (a b : Nat) (xs : List Nat) (n : Nat), len (a :: b :: xs) = n ===>
  ∀ (xs : List Nat) (n : Nat), n = Nat.add 2 (len xs)

#testOptimize [ "ExtSameNameModuleA_2" ] (norm-result: 1)
  ∀ (a n : Nat), len [a] = n ===> ∀ (n : Nat), 1 = n
