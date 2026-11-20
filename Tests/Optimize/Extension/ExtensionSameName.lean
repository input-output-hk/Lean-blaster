import Lean
import Tests.Utils
import Blaster.Optimize.Env
import Tests.Optimize.Extension.ExtensionSameName.ModuleA
import Tests.Optimize.Extension.ExtensionSameName.ModuleB

/-!
# Naming of the generated optimization functions

The optimization function generated for a theorem `<p>.<name>` is named as an explicit definition
`def <p'>.blaster_opt_<name>` written where the `@[blaster]` attribute is applied would be, `<p'>`
being the namespace `<p>` relative to the current namespace `<ns>`: `<p>.blaster_opt_<name>` when the
theorem is declared in the current namespace (or below), `<ns>.<p>.blaster_opt_<name>` otherwise. A
private theorem yields a private function. The auxiliary definitions created while elaborating the
generated code (the `match_<n>` matchers) are named after the generated function.

The same theorem can therefore be annotated from different namespaces, possibly in different modules
(`ModuleA` annotates `len_nil`/`len_cons` from the root namespace, `ModuleB` from
`Test.ExtensionSameName.ModB`, both are imported here), theorems sharing their short name can be
annotated from different namespaces or sections, and annotating a theorem twice from the same
namespace fails as a duplicate definition would.
-/

open Lean Meta Blaster.Optimize

namespace Outside
axiom g : Nat → Nat
axiom g_zero : g 0 = 7
end Outside

namespace Test.ExtensionSameName

/-- Fail if the generated optimization function `<ns>.blaster_opt_<thm>` of the theorem `<p>.<thm>`
    annotated from namespace `<ns>` (and its matcher, when `withMatcher` is set) does not exist. -/
def checkGenerated (ns : Name) (thm : String) (withMatcher : Bool) : MetaM Unit := do
  let fn := ns ++ Name.mkSimple s!"blaster_opt_{thm}"
  unless (← getEnv).contains fn do
    throwError "optimization function `{fn}` not found"
  if withMatcher then
    unless (← getEnv).contains (fn ++ `match_1) do
      throwError "matcher `{fn ++ `match_1}` not found"

/-! ## Same theorem annotated from two modules (in different namespaces) -/

run_meta do
  for ns in [`Test.ExtensionSameName, `Test.ExtensionSameName.ModB.Test.ExtensionSameName] do
    checkGenerated ns "len_nil" (withMatcher := false)
    checkGenerated ns "len_cons" (withMatcher := true)
  -- the matchers are not named after the theorem
  if (← getEnv).contains `Test.ExtensionSameName.len_cons.match_1 then
    throwError "matcher `Test.ExtensionSameName.len_cons.match_1` found"

-- both copies of the rules are registered
#testOptimize [ "ExtSameName_1" ] (norm-result: 1)
  ∀ (a b : Nat) (xs : List Nat) (n : Nat), len (a :: b :: xs) = n ===>
  ∀ (xs : List Nat) (n : Nat), n = Nat.add 2 (len xs)

#testOptimize [ "ExtSameName_2" ] (norm-result: 1)
  ∀ (a n : Nat), len [a] = n ===> ∀ (n : Nat), 1 = n

/-! ## Same theorem annotated twice from the same namespace -/

-- `ModuleA` already generated `Test.ExtensionSameName.blaster_opt_len_nil`
/-- error: `Test.ExtensionSameName.blaster_opt_len_nil` has already been declared -/
#guard_msgs (error) in
attribute [blaster] len_nil

/-! ## Theorems with the same short name in different namespaces -/

axiom f1 : List Nat → Nat
axiom f2 : List Nat → Nat

namespace A
@[blaster] axiom f_cons : ∀ (a : Nat) (xs : List Nat), f1 (a :: xs) = f1 xs + 1
example : Blaster.OptFn := blaster_opt_f_cons
end A

namespace B
@[blaster] axiom f_cons : ∀ (a : Nat) (xs : List Nat), f2 (a :: xs) = f2 xs + 2
example : Blaster.OptFn := blaster_opt_f_cons
end B

example : Blaster.OptFn := A.blaster_opt_f_cons
example : Blaster.OptFn := B.blaster_opt_f_cons

-- (a matcher is shared by the generated functions of the same module when the patterns are
-- identical, so only the existence of the optimization functions is checked here)
run_meta do
  for ns in [`Test.ExtensionSameName.A, `Test.ExtensionSameName.B] do
    checkGenerated ns "f_cons" (withMatcher := false)

#testOptimize [ "ExtSameName_3" ] (norm-result: 1)
  ∀ (a b : Nat) (xs : List Nat) (n : Nat), f1 (a :: b :: xs) = n ===>
  ∀ (xs : List Nat) (n : Nat), n = Nat.add 2 (f1 xs)

#testOptimize [ "ExtSameName_4" ] (norm-result: 1)
  ∀ (a b : Nat) (xs : List Nat) (n : Nat), f2 (a :: b :: xs) = n ===>
  ∀ (xs : List Nat) (n : Nat), n = Nat.add 4 (f2 xs)

#testOptimize [ "ExtSameName_5" ] (norm-result: 1)
  ∀ (a : Nat) (xs : List Nat), f1 (a :: xs) = f2 (a :: xs) ===>
  ∀ (xs : List Nat), f1 xs = Nat.add 1 (f2 xs)

/-! ## Theorems with the same short name in different sections (and namespaces) -/

section
namespace C
@[blaster] axiom f_nil : f1 [] = 10
example : Blaster.OptFn := blaster_opt_f_nil
end C
end

section
namespace D
@[blaster] axiom f_nil : f2 [] = 20
example : Blaster.OptFn := blaster_opt_f_nil
end D
end

run_meta do
  for ns in [`Test.ExtensionSameName.C, `Test.ExtensionSameName.D] do
    checkGenerated ns "f_nil" (withMatcher := false)

#testOptimize [ "ExtSameName_6" ] (norm-result: 1)
  ∀ (a : Nat), f1 [a] + f2 [a] = 0 ===> False

#testOptimize [ "ExtSameName_7" ] (norm-result: 1)
  ∀ (a : Nat) (n : Nat), f1 [a] + f2 [a] = n ===> ∀ (n : Nat), 33 = n

/-! ## Theorem declared outside the current namespace -/

attribute [blaster] Outside.g_zero

-- named `Test.ExtensionSameName.Outside.blaster_opt_g_zero`, as `def Outside.blaster_opt_g_zero` would be
example : Blaster.OptFn := Outside.blaster_opt_g_zero
run_meta checkGenerated `Test.ExtensionSameName.Outside "g_zero" (withMatcher := false)

#testOptimize [ "ExtSameName_8" ] (norm-result: 1)
  ∀ (n : Nat), Outside.g 0 = n ===> ∀ (n : Nat), 7 = n

/-! ## Private theorems -/

axiom f3 : List Nat → Nat

@[blaster] private axiom f3_nil : f3 [] = 3

-- named `_private.<module>.0.Test.ExtensionSameName.blaster_opt_f3_nil`, as `private def blaster_opt_f3_nil` would be
example : Blaster.OptFn := blaster_opt_f3_nil
run_meta do
  let fn := mkPrivateName (← getEnv) `Test.ExtensionSameName.blaster_opt_f3_nil
  unless (← getEnv).contains fn do throwError "optimization function `{fn}` not found"
  if (← getEnv).contains `Test.ExtensionSameName.blaster_opt_f3_nil then
    throwError "the optimization function of a private theorem is not private"

#testOptimize [ "ExtSameName_9" ] (norm-result: 1)
  ∀ (a : Nat), f3 [a] = f3 [] ===> ∀ (a : Nat), 3 = f3 [a]


axiom f : Nat → Nat
axiom g : Nat → Nat
axiom f_eq : ∀ n, f n = g n

-- Two sections cannot both annotate the same theorem in the same namespace
section A
attribute [blaster] f_eq
end A

section B

/-- error: `Test.ExtensionSameName.blaster_opt_f_eq` has already been declared -/
#guard_msgs (error) in
attribute [blaster] f_eq
end B

end Test.ExtensionSameName
