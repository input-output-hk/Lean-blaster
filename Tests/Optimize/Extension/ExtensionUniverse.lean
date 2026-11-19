import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionUniverse

/-! Universe polymorphic theorem: levels are recovered from the lhs. -/

universe u

axiom pl : {α : Type u} → List α → Nat

@[blaster]
axiom pl_cons : ∀ {α : Type u} (a : α) (xs : List α), pl (a :: xs) = Nat.add 1 (pl xs)

@[blaster (noRestart := true)]
axiom pl_nil : ∀ {α : Type u}, pl (@List.nil α) = 0

-- NOTE: the unused binder `a` is removed by the optimizer
#testOptimize [ "ExtPoly_1" ] (norm-result: 1) ∀ (a : Nat) (xs : List Nat) (m : Nat), pl (a :: xs) = m ===> ∀ (xs : List Nat) (m : Nat), m = Nat.add 1 (pl xs)
#testOptimize [ "ExtPoly_2" ] (norm-result: 1) ∀ (m : Nat), pl ([] : List Nat) = m ===> ∀ (m : Nat), 0 = m

/-! ## Universe level parameters of the rhs recovered from the lhs
     A level parameter used in the rhs is recovered, in this order, from a constant of the lhs arguments
     (`@List.cons.{u}`), from a sort of the lhs arguments (`Sort u`, `Type u`) or from the head expression
     passed to the generated function (`@box.{u}`, when the pattern variable `α : Type u` is the only
     argument carrying `u`). -/

/-! `u` occurs in the head `@box.{u}` and in the rhs `@some.{u}` only. -/
def box {α : Type u} (x : α) : Option α := some x

@[blaster]
theorem box_eq_some {α : Type u} (x : α) : box x = some x := rfl

#testOptimize [ "ExtHeadLevel_1" ] ∀ (x : Nat), box x = some x ===> True
#testOptimize [ "ExtHeadLevel_2" ] ∀ (x : List Nat), box x = some x ===> True
#testOptimize [ "ExtHeadLevel_3" ] ∀ (x : Type), box x = some x ===> True
#testOptimize [ "ExtHeadLevel_4" ] ∀ (x : Nat), box x = none ===> False
-- the rule has no `restart`: the rewritten equality is not optimized further
#testOptimize [ "ExtHeadLevel_5" ] ∀ (x y : Nat), box x = some y ===> ∀ (x y : Nat), some x = some y

/-! `u` also occurs in a constant of the arguments (`@List.cons.{u}`): recovered from the arguments. -/
def box2 {α : Type u} (xs : List α) : Option (List α) := some xs

@[blaster]
theorem box2_cons {α : Type u} (a : α) (xs : List α) : box2 (a :: xs) = some (a :: xs) := rfl

#testOptimize [ "ExtHeadLevel_6" ] ∀ (a : Nat) (xs : List Nat), box2 (a :: xs) = some (a :: xs) ===> True
#testOptimize [ "ExtHeadLevel_7" ] ∀ (a : Type) (xs : List Type), box2 (a :: xs) = some (a :: xs) ===> True
-- the rule does not match: the definition is unfolded natively
#testOptimize [ "ExtHeadLevel_8" ] ∀ (xs : List Nat), box2 xs = some xs ===> True

/-! `u` occurs in a sort of the arguments (`Type u`, i.e. `Sort (u + 1)`) and in the head `@tyg.{u + 2}`:
    recovered from the sort (`Level.dec` of the matched level). -/
axiom tyg : Sort v → Nat
axiom tyh : Sort v → Nat

@[blaster]
axiom tyg_type : tyg (Type u) = tyh (Type u)

#testOptimize [ "ExtSortLevel_1" ] tyg (Type 1) = tyh (Type 1) ===> True
#testOptimize [ "ExtSortLevel_2" ] tyg (Type 3) = tyh (Type 3) ===> True
#testOptimize [ "ExtSortLevel_3" ] tyg (Type 1) = tyh (Type 2) ===> tyh (Type 1) = tyh (Type 2)
-- no rewriting: `Type 1` matches `Type u` but `Prop` (`Sort 0`) does not
#testOptimize [ "ExtSortLevel_4" ] tyg Prop = tyh Prop ===> tyg Prop = tyh Prop

/-! `u + 1` occurs in a universe polymorphic constant of the arguments (`@PProd.{u + 1, u + 1}`):
    recovered from the constant (`Level.dec` of the matched level). -/
axiom tyk : Sort v → Nat

@[blaster]
axiom tyk_pprod : tyk (PProd.{u + 1, u + 1} (Sort u) (Sort u)) = tyh (Sort u)

#testOptimize [ "ExtSortLevel_5" ] tyk (PProd.{3, 3} (Type 1) (Type 1)) = tyh (Type 1) ===> True
#testOptimize [ "ExtSortLevel_6" ] tyk (PProd.{1, 1} Prop Prop) = tyh Prop ===> True

/-! ## Several universe level parameters
     Every level parameter of the rhs must be recovered (from the arguments or from the head); levels built
     for the rhs are normalized (`max 0 0` ↦ `0`, as elaborated by Lean in the goal), and a level parameter
     occurring several times in the lhs must be matched by equivalent levels. -/
universe v w

/-! Both levels from the head `@box3.{u, v}`; the rhs uses `@Prod.{u, v}` and `@some.{max u v}`. -/
def box3 {α : Type u} {β : Type v} (a : α) (b : β) : Option (α × β) := some (a, b)

@[blaster]
theorem box3_eq {α : Type u} {β : Type v} (a : α) (b : β) : box3 a b = some (a, b) := rfl

#testOptimize [ "ExtMultiLevel_1" ] ∀ (a : Nat) (b : List Nat), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiLevel_2" ] ∀ (a : Type) (b : Nat), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiLevel_3" ] ∀ (a : Nat) (b : Type 1), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiLevel_4" ] ∀ (a : Type 2) (b : Type 1), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiLevel_5" ] ∀ (a : Nat) (b : Nat), box3 a b = none ===> False

/-! `u` from a constant of the arguments (`@List.cons.{u}`), `v` from the head. -/
def box4 {α : Type u} {β : Type v} (xs : List α) (b : β) : Option (List α × β) := some (xs, b)

@[blaster]
theorem box4_cons {α : Type u} {β : Type v} (a : α) (xs : List α) (b : β) : box4 (a :: xs) b = some (a :: xs, b) := rfl

#testOptimize [ "ExtMultiLevel_6" ] ∀ (a : Nat) (xs : List Nat) (b : Type), box4 (a :: xs) b = some (a :: xs, b) ===> True
#testOptimize [ "ExtMultiLevel_7" ] ∀ (a : Type 1) (xs : List (Type 1)) (b : Nat), box4 (a :: xs) b = some (a :: xs, b) ===> True

/-! Three levels, `@some.{max u (max v w)}` in the rhs. -/
def box5 {α : Type u} {β : Type v} {γ : Type w} (a : α) (b : β) (c : γ) : Option (α × β × γ) := some (a, b, c)

@[blaster]
theorem box5_eq {α : Type u} {β : Type v} {γ : Type w} (a : α) (b : β) (c : γ) : box5 a b c = some (a, b, c) := rfl

#testOptimize [ "ExtMultiLevel_8" ] ∀ (a : Nat) (b : Type) (c : Type 2), box5 a b c = some (a, b, c) ===> True
#testOptimize [ "ExtMultiLevel_9" ] ∀ (a : Type 3) (b : Nat) (c : Nat), box5 a b c = some (a, b, c) ===> True

/-! Both levels from sorts of the arguments, swapped in the rhs. -/
axiom ty2 : Sort v → Sort w → Nat
axiom ty2h : Sort v → Sort w → Nat

@[blaster]
axiom ty2_type : ty2 (Type u) (Type v) = ty2h (Type v) (Type u)

#testOptimize [ "ExtMultiSort_1" ] ty2 (Type 1) (Type 2) = ty2h (Type 2) (Type 1) ===> True
#testOptimize [ "ExtMultiSort_2" ] ty2 (Type 1) (Type 2) = ty2h (Type 1) (Type 2) ===> ty2h (Type 1) (Type 2) = ty2h (Type 2) (Type 1)
-- no rewriting: `Prop` does not match `Type u`
#testOptimize [ "ExtMultiSort_3" ] ty2 Prop (Type 2) = ty2h (Type 2) Prop ===> ty2 Prop (Type 2) = ty2h (Type 2) Prop

/-! Non-linear occurrence of a level parameter in two sorts: the matched levels must be equivalent. -/
axiom ty3 : Sort v → Sort w → Nat

@[blaster]
axiom ty3_type : ty3 (Type u) (Type u) = ty2h (Type u) (Type u)

#testOptimize [ "ExtMultiSort_4" ] ty3 (Type 1) (Type 1) = ty2h (Type 1) (Type 1) ===> True
-- no rewriting: `Type 1` and `Type 2` are not the same instance of `Type u`
#testOptimize [ "ExtMultiSort_5" ] ty3 (Type 1) (Type 2) = ty2h (Type 1) (Type 1) ===> ty2h (Type 1) (Type 1) = ty3 (Type 1) (Type 2)

/-! Non-linear occurrence of a level parameter in a sort and in a constant (`@PUnit.{u + 1}`). -/
axiom ty4 : Sort v → Sort w → Nat

@[blaster]
axiom ty4_type : ty4 (Type u) (PUnit.{u + 1}) = ty2h (Type u) (Type u)

#testOptimize [ "ExtMultiSort_6" ] ty4 (Type 1) (PUnit.{2}) = ty2h (Type 1) (Type 1) ===> True
-- no rewriting: `PUnit.{3}` is not `PUnit.{u + 1}` for `u := 1`
#testOptimize [ "ExtMultiSort_7" ] ty4 (Type 1) (PUnit.{3}) = ty2h (Type 1) (Type 1) ===> ty2h (Type 1) (Type 1) = ty4 (Type 1) (PUnit.{3})

/-! A level parameter under `max` cannot be recovered from the lhs. -/
axiom ty5 : Sort v → Nat

/-- error: blaster: universe level parameter `u` cannot be recovered from the lhs -/
#guard_msgs in
@[blaster]
axiom ty5_max : ty5 (Sort (max u v)) = ty2h (Sort u) (Sort v)

/-! `max` in the rhs, with the parameters recovered from the arguments: the built level is normalized. -/
axiom ty6 : Sort v → Sort w → Nat

@[blaster]
axiom ty6_max : ty6 (Type u) (Type v) = ty5 (Sort (max u v))

#testOptimize [ "ExtMultiMax_1" ] ty6 (Type 1) (Type 2) = ty5 (Type 1) ===> True
#testOptimize [ "ExtMultiMax_2" ] ty6 (Type 2) (Type 1) = ty5 (Type 1) ===> True
#testOptimize [ "ExtMultiMax_3" ] ty6 (Type 2) (Type 2) = ty5 (Type 1) ===> True
#testOptimize [ "ExtMultiMax_4" ] ty6 (Type 2) (Type 1) = ty5 (Type 2) ===> ty5 (Type 1) = ty5 (Type 2)

/-! Universe polymorphic goals with `max` levels. The levels built for the rhs are normalized
    (`Level.normalize`), and the levels of the goal are normalized by the optimizer (`normLevel`, which
    orders the operands of `max` with `Level.normLt` as `Level.normalize` does): the order of the operands
    of `max` as elaborated by Lean (`some.{max v u}` for `{α : Type u} {β : Type v}`) or as written in the
    goal (`Sort (max v u)`, `Sort (max u 1)`) does not matter, both sides are hash-consed to the same term. -/

-- the goal is elaborated with `some.{max v u}`, the rule builds `some.{max u v}`
#testOptimize [ "ExtMultiMaxPoly_1" ] ∀ {α : Type u} {β : Type v} (a : α) (b : β), box3 a b = some (a, b) ===> True
-- the goal is elaborated with `some.{max u v}`
#testOptimize [ "ExtMultiMaxPoly_2" ] ∀ {α : Type v} {β : Type u} (a : α) (b : β), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiMaxPoly_3" ] ∀ {α : Type u} {β : Type u} (a : α) (b : β), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiMaxPoly_4" ] ∀ {α : Type u} (a : α) (b : Nat), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiMaxPoly_5" ] ∀ {α : Type u} (a : Nat) (b : α), box3 a b = some (a, b) ===> True
#testOptimize [ "ExtMultiMaxPoly_6" ] ∀ {α : Type u} (a : α) (b : Type u), box3 a b = some (a, b) ===> True

#testOptimize [ "ExtMultiMaxPoly_7" ] ty6 (Type u) (Type v) = ty5 (Sort (max u v)) ===> True
-- `Sort (max v u)` is written in the goal, the rule builds `Sort (max u v)`
#testOptimize [ "ExtMultiMaxPoly_8" ] ty6 (Type v) (Type u) = ty5 (Sort (max v u)) ===> True
-- `Sort (max u 1)` is written in the goal, the rule builds `Sort (max 1 u)`
#testOptimize [ "ExtMultiMaxPoly_9" ] ty6 (Type u) (Type 1) = ty5 (Sort (max u 1)) ===> True
#testOptimize [ "ExtMultiMaxPoly_10" ] ty6 (Type u) (Type u) = ty5 (Sort u) ===> True
#testOptimize [ "ExtMultiMaxPoly_11" ] ty6 (Type u) (Type u) = ty5 (Sort (max u u)) ===> True
#testOptimize [ "ExtMultiMaxPoly_12" ] ty6 (Type u) (Type 0) = ty5 (Sort u) ===> True
#testOptimize [ "ExtMultiMaxPoly_13" ] ty6 (Type (u + 1)) (Type u) = ty5 (Sort (u + 1)) ===> True

end Test.ExtensionUniverse
