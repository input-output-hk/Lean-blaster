import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionBinder

/-! ## Pattern variables under a binder of the lhs

A variable of the theorem cannot depend on a binder (`fun`, `∀`) of its lhs: when the pattern of a
variable occurs under a binder, the matched term must not contain loose bound variables, otherwise
the rule would be applied to a term that is not an instance of its lhs (`app (fun y => y) n` is not
an instance of `app (fun _ => x) n`, and rewriting it to `x := y` would leave a dangling variable).
Such a match is rejected (`Expr.hasLooseBVars` check), the rule is not applied. -/

axiom app : (Nat → Nat) → Nat → Nat

@[blaster (noRestart := true)]
axiom app_const (x n : Nat) : app (fun _ => x) n = x

-- the body of the lambda is the bound variable
#testOptimize [ "ExtBinderLam_1" ]
  ∀ (n m : Nat), app (fun y => y) n = m ===> ∀ (n m : Nat), m = app (fun y => y) n

-- the body of the lambda depends on the bound variable
#testOptimize [ "ExtBinderLam_2" ]
  ∀ (n m : Nat), app (fun y => Nat.add y m) n = m ===> ∀ (n m : Nat), m = app (fun y => Nat.add m y) n

#testOptimize [ "ExtBinderLam_3" ]
  ∀ (n m : Nat) (f : Nat → Nat), app (fun y => f y) n = m ===> ∀ (n m : Nat) (f : Nat → Nat), m = app (fun y => f y) n

-- the body of the lambda does not depend on the bound variable: the rule applies
#testOptimize [ "ExtBinderLam_4" ] ∀ (n m : Nat), app (fun _ => m) n = m ===> True

#testOptimize [ "ExtBinderLam_5" ] ∀ (n m : Nat) (f : Nat → Nat), app (fun _ => f m) n = f m ===> True

/-! Variable under two binders. -/

axiom app2 : (Nat → Nat → Nat) → Nat

@[blaster (noRestart := true)]
axiom app2_const (x : Nat) : app2 (fun _ _ => x) = x

#testOptimize [ "ExtBinderLam_6" ] ∀ (m : Nat), app2 (fun a _ => a) = m ===> ∀ (m : Nat), m = app2 (fun a _ => a)

#testOptimize [ "ExtBinderLam_7" ] ∀ (m : Nat), app2 (fun _ b => b) = m ===> ∀ (m : Nat), m = app2 (fun _ b => b)

#testOptimize [ "ExtBinderLam_8" ] ∀ (m : Nat), app2 (fun _ _ => m) = m ===> True

/-! Proposition-valued lambda. -/

axiom q : (Nat → Prop) → Prop

@[blaster (noRestart := true)]
axiom q_const (p : Prop) : q (fun _ => p) = p

#testOptimize [ "ExtBinderLam_9" ] (norm-result: 1) q (fun y => y = 0) → 1 = 0 ===> ¬ q (fun y => 0 = y)

#testOptimize [ "ExtBinderLam_10" ] (norm-result: 1)
  ∀ (c : Prop), q (fun y => c ∧ y = 0) → c ===> ∀ (c : Prop), q (fun y => c ∧ 0 = y) → c

#testOptimize [ "ExtBinderLam_11" ] ∀ (c : Prop), q (fun _ => c) → c ===> True

/-! Variable under a `∀` binder. -/

axiom w : Prop → Nat

@[blaster (noRestart := true)]
axiom w_all (p : Prop) : w (∀ y : Nat, p ∨ 0 < y) = w p

#testOptimize [ "ExtBinderForall_1" ] (norm-result: 1)
  ∀ (m : Nat), w (∀ y : Nat, y = 1 ∨ 0 < y) = m ===> ∀ (m : Nat), m = w (∀ y : Nat, 1 = y ∨ 0 < y)

#testOptimize [ "ExtBinderForall_2" ] (norm-result: 1)
  ∀ (m : Nat) (f : Nat → Prop), w (∀ y : Nat, f y ∨ 0 < y) = m ===>
  ∀ (m : Nat) (f : Nat → Prop), m = w (∀ y : Nat, f y ∨ 0 < y)

#testOptimize [ "ExtBinderForall_3" ] ∀ (c : Prop) (m : Nat), w (∀ y : Nat, c ∨ 0 < y) = m ===> ∀ (c : Prop) (m : Nat), m = w c

/-! `List.map (fun _ => x) l`: without the check, `List.map (fun y => y) l = List.replicate l.length n`
    was rewritten to `True` (it is falsified by `l = [1], n = 0`). -/

@[blaster (noRestart := true)]
theorem map_const_nat (x : Nat) (l : List Nat) :
    List.map (fun _ => x) l = List.replicate l.length x := List.map_const'

#testOptimize [ "ExtBinderMap_1" ]
  ∀ (l : List Nat) (n : Nat), List.map (fun y => y) l = List.replicate l.length n ===>
  ∀ (l : List Nat) (n : Nat), List.replicate l.length n = List.map (fun y => y) l

#testOptimize [ "ExtBinderMap_2" ]
  ∀ (l : List Nat) (n : Nat), List.map (fun y => y + n) l = List.replicate l.length n ===>
  ∀ (l : List Nat) (n : Nat), List.replicate l.length n = List.map (fun y => Nat.add n y) l

#testOptimize [ "ExtBinderMap_3" ] ∀ (l : List Nat) (n : Nat), List.map (fun _ => n) l = List.replicate l.length n ===> True

end Test.ExtensionBinder
