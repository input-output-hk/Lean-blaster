import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeLet

/-! ## Test objectives to validate inlining of let expressions. -/

-- let x := a ∧ b in x ===> a ∧ b
#testOptimize [ "LetElim_1" ] ∀ (a b : Prop), let x := a ∧ b; x ===> ∀ (a b : Prop), a ∧ b

-- let x := a ∧ b in
-- let y := c ∨ b in
-- y ∧ x ===> (c ∨ b) ∧ (a ∧ b)
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElim_2" ] ∀ (a b c : Prop), let x := a ∧ b; let y := c ∨ b; y ∧ x ===> ∀ (a b c : Prop), (b ∨ c) ∧ (a ∧ b)

-- let x := a ∧ b in
-- let y := x ∨ c in
-- y ∨ b ===> ((a ∧ b) ∨ c) ∨ b
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElim_3" ] ∀ (a b c : Prop), let x := a ∧ b; let y := x ∨ c; y ∨ b ===> ∀ (a b c : Prop), b ∨ (c ∨ (a ∧ b))

-- let x := a ∧ b in
-- let y := c ∨ b in
-- (y ∧ x) = ((b ∧ a) ∧ (b ∨ c)) ===> True
#testOptimize [ "LetElim_4" ] ∀ (a b c : Prop), let x := a ∧ b; let y := c ∨ b; (y ∧ x) = ((b ∧ a) ∧ (b ∨ c)) ===> True

-- let x := a = b in
-- let y := c = b in
--  (y ∧ x) = ((b = a) ∧ (b = c)) ===> True
-- With Type(a) = Type(b) = α
#testOptimize [ "LetElim_5" ] ∀ (α : Type) (a b c : α), let x := a = b; let y := c = b; (y ∧ x) = ((b = a) ∧ (b = c)) ===> True

-- let x := fun z => a ∧ z in
-- x b ∨ x c ===> (a ∧ b) ∨ (a ∧ c)
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElim_6" ] ∀ (a b c : Prop), let x := fun z => a ∧ z; x b ∨ x c ===> ∀ (a b c : Prop), (a ∧ c) ∨ (a ∧ b)

-- let x := fun z => a ∧ z in
-- (x b ∨ x c) = ((a ∧ b) ∨ (a ∧ c)) ===> True
#testOptimize [ "LetElim_7" ] ∀ (a b c : Prop), let x := fun z => a ∧ z; (x b ∨ x c) = ((a ∧ c) ∨ (a ∧ b)) ===> True

end Tests.OptimizeLet
