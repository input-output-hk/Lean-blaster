import Lean
import Solver.Command.Syntax

namespace Tests.Issue15

-- Issue 1: translateApp: unexpected application Lean.Expr.app
--           (Lean.Expr.proj `Tests.Issue15.Input 1 (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 926)))
--            (Lean.Expr.proj `Tests.Issue15.Input 0 (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 926)))
-- Diagnosis : We need to properly translate function application, whereby the function is a ctor argument (see thm1).

-- Issue 2: translateApp: unexpected application Lean.Expr.app
--          (Lean.Expr.mdata
--            { entries := [(`_solver.ctorSelector, Lean.DataValue.ofBool true)] }
--              (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkNum `Tests.Issue15.FunCongruence.mk 1) [])
--                (Lean.Expr.const `x []))) (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 858))
-- Diagnosis: We need to properly handle function in ctor argument and applied in ctor proposition (see thm2)


structure Input where
  x : Nat
  f : Nat → Nat

theorem thm1: ∀ (f : Input) (g : Input), f.2 = g.2 → f.1 = g.1 → f.2 f.1 = g.2 g.1 := by
  intro f g; apply congr

#solve [thm1]


structure FunRelOne where
  f : Nat → Nat
  inv : ∀ (x y : Nat), x = y → f x = f y

theorem thm2: ∀ (f : FunRelOne) (x y : Nat), x = y → f.f x = f.f y := by
  intro f x y h
  apply f.inv
  assumption

#solve [thm2]

/-- Considering implicit arguments in ctor proposition with explicit polymorphic param -/
structure FunRelTwo α where
  f [LT α] : α → α
  inv : ∀ (x y : α), [LT α] → x < y → f x < f y

theorem thm3 : ∀ (α : Type) (f : FunRelTwo α) (x y : α) [LT α], x < y → f.f x < f.f y := by
  intro _ f x y h1 h2
  apply f.inv
  assumption

#solve [thm3]

/-- Considering implicit arguments in ctor proposition without explicit polymorhic param -/
structure FunRelThree where
  f [LT α] : α → α
  inv : ∀ (x y : α), [LT α] → x < y → f x < f y

theorem thm4 : ∀ (f : FunRelThree) (x y : α) [LT α], x < y → f.f x < f.f y := by
  intros f x y h1 h2
  apply f.inv
  assumption

#solve [thm4]

end Tests.Issue15
