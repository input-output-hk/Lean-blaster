import Tests.Utils
import Tests.Optimize.Extension.ExtensionSameName.Defs

/-! Second module (independent of `ModuleA`) annotating `len_nil`/`len_cons`, from the namespace
    `Test.ExtensionSameName.ModB`: the generated optimization functions are named
    `Test.ExtensionSameName.ModB.Test.ExtensionSameName.blaster_opt_len_nil` and
    `Test.ExtensionSameName.ModB.Test.ExtensionSameName.blaster_opt_len_cons`, as explicit definitions
    `def Test.ExtensionSameName.blaster_opt_len_nil` in this namespace would be. -/

namespace Test.ExtensionSameName.ModB

attribute [blaster] len_nil len_cons

example : Blaster.OptFn := Test.ExtensionSameName.blaster_opt_len_nil
example : Blaster.OptFn := Test.ExtensionSameName.ModB.Test.ExtensionSameName.blaster_opt_len_cons

#testOptimize [ "ExtSameNameModuleB_1" ] (norm-result: 1)
  ∀ (a b : Nat) (xs : List Nat) (n : Nat), len (a :: b :: xs) = n ===>
  ∀ (xs : List Nat) (n : Nat), n = Nat.add 2 (len xs)

#testOptimize [ "ExtSameNameModuleB_2" ] (norm-result: 1)
  ∀ (a n : Nat), len [a] = n ===> ∀ (n : Nat), 1 = n

end Test.ExtensionSameName.ModB
