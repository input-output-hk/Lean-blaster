import Blaster.Optimize.Env

/-! Definitions shared by `ModuleA` and `ModuleB`, which both annotate the same theorems with
    `@[blaster]` (see `Tests/Optimize/Extension/ExtensionSameName.lean`). -/

namespace Test.ExtensionSameName

axiom len : List Nat → Nat
axiom len_nil : len [] = 0
axiom len_cons : ∀ (a : Nat) (xs : List Nat), len (a :: xs) = len xs + 1

end Test.ExtensionSameName
